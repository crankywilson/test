#!/usr/bin/env python3
"""progdeps: get a repo and its dependencies ready to build.

  progdeps get REPO REF [--only DEP ...] [--src DEP ...] [--allsrcs]
                                  clone REPO and set up its deps
  progdeps sync [--pull]          bring this tree up to date; never changes what's in it
  progdeps add DEP [--src]        add one dep, as prebuilt or source
  progdeps add --all              end a sparse tree: use every dep
  progdeps drop DEP               remove one dep
  progdeps status                 compare deps/ with what deps.dat asks for now
  progdeps list [PATTERN] [--repo REPO]
                                  version lines on the server, or a repo's branches and tags
  progdeps publish REPO REF       build and upload whatever the store lacks
  progdeps plan REPO REF TAG      freeze everything on a release branch, ready to tag
  progdeps release REPO TAG       after TAG is pushed: publish, then tag every repo below

get, sync and add use the network mount when it has a prebuilt, and download otherwise.
--mount requires the mount. --download always makes real local copies, for taking
a project off the network.

Developers and CI use the same resolver and the same build keys.
See README.md.
"""
import argparse
import configparser
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path

CONFIG = Path(os.environ.get("PROGDEPS_CONFIG", "~/.config/progdeps/config")).expanduser()
STATE = ".progdeps"    # per-project; goes away with the project tree
DEPS_FILE = "deps.dat"
OLD_DEPS_FILE = "deps.data"    # still read, so lines made before the rename keep working
DEPS_DIR = "deps"
MARKER = ".progdeps-key"
OUTPUT = ("include", "lib", "bin", "env.sh")    # what a repo's build leaves behind
RELEASE_PREFIX = "REL_"    # a release branch is this plus the exact release name
DIRECT_DEP = "DIRECT_DEP"    # marks the top's own deps in a frozen list
NOBUILD = "NOBUILD"    # build field for a repo that is only data, with no package; the default
PROJECT_VAR = "PROJECTROOT"    # the top of the tree; deps are in $PROJECTROOT/deps
NOT_IN_KEY = "# --- progdeps: not part of the build key below this line ---"


class Error(Exception):
    pass


def current_variant():
    """How things are built here: the OS, plus PROGDEPS_VARIANT if set.

    The key says which code and deps; the variant says how it was built, such as
    rhel9 or rhel9-debug. CI publishes each variant it needs under the same key.
    """
    release = {}
    for line in Path("/etc/os-release").read_text().splitlines():
        name, _, value = line.partition("=")
        release[name] = value.strip('"')
    name = release.get("ID", "linux") + release.get("VERSION_ID", "").split(".")[0]
    extra = os.environ.get("PROGDEPS_VARIANT")
    return f"{name}-{extra}" if extra else name


VARIANT = current_variant()


def run(cmd, cwd=None, env=None, capture=False):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE if capture else None)
    if result.returncode != 0:
        raise Error(f"command failed: {' '.join(map(str, cmd))}")
    return result.stdout.strip() if capture else ""


@dataclass
class Spec:
    """One line of a deps file."""
    repo: str
    ref: str
    root_var: str = ""    # empty: no variable; reach it under $PROJECTROOT/deps
    build: str = NOBUILD
    direct: bool = True    # in a frozen list, only lines marked DIRECT_DEP

    @property
    def name(self):
        return self.repo.rsplit("/", 1)[-1]


@dataclass
class Node:
    spec: Spec
    commit: str
    deps: list = field(default_factory=list)    # names of direct deps
    key: str = ""
    data: str = ""    # for a data-only repo, what its key uses instead of the commit

    @property
    def name(self):
        return self.spec.name

    @property
    def data_only(self):
        return self.spec.build == NOBUILD

    @property
    def ident(self):
        return self.commit if self.data_only else f"{self.key}/{VARIANT}"


def parse_deps(text, source, frozen=False):
    specs = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        direct = line.endswith(":" + DIRECT_DEP)
        if direct and not frozen:
            raise Error(f"{source}: {DIRECT_DEP} is only for frozen lists, got: {line}")
        parts = line.removesuffix(":" + DIRECT_DEP).split(":", 3)
        if len(parts) < 2 or not all(parts[:2]):
            raise Error(f"{source}: expected repo:ref[:ROOT[:build]], got: {line}")
        if frozen and not re.fullmatch(r"[0-9a-f]{40}", parts[1]):
            raise Error(f"{source}: a frozen list needs an exact commit, got: {line}")
        if len(parts) > 3 and not parts[3]:
            parts[3] = NOBUILD    # an empty build is the same as none
        specs.append(Spec(*parts, direct=direct or not frozen))
    return specs


def parse_file(text, source):
    """Returns a deps file's JSON header, which may be empty, and its deps.

    A "release" key in the header means a frozen list: exact commits and keys for
    everything below, final for that part of the tree.
    """
    header = {}
    if text.startswith("{"):
        try:
            header, end = json.JSONDecoder().raw_decode(text)
        except json.JSONDecodeError as error:
            raise Error(f"{source}: bad JSON header: {error}")
        text = text[end:]
    return header, parse_deps(text, source, "release" in header)


def direct_names(specs):
    return [spec.name for spec in specs if spec.direct]


def spec_line(spec, commit, direct=False):
    """A deps.dat line at an exact commit, leaving off fields that are the default."""
    fields = [spec.repo, commit]
    if spec.root_var or spec.build != NOBUILD:
        fields.append(spec.root_var)
    if spec.build != NOBUILD:
        fields.append(spec.build)
    return ":".join(fields) + (f":{DIRECT_DEP}" if direct else "")


def deps_file_in(folder):
    """The deps file in a folder: deps.dat, or deps.data from before the rename."""
    for name in (DEPS_FILE, OLD_DEPS_FILE):
        if (Path(folder) / name).exists():
            return Path(folder) / name
    return Path(folder) / DEPS_FILE


def deps_file_at(repo, commit):
    """A deps file's name and text at a commit, or (DEPS_FILE, None) if it has neither name."""
    for name in (DEPS_FILE, OLD_DEPS_FILE):
        show = subprocess.run(["git", "-C", repo, "show", f"{commit}:{name}"],
                              capture_output=True, text=True)
        if show.returncode == 0:
            return name, show.stdout
    return DEPS_FILE, None


def check_root(config, name, specs, where):
    """A root repo, with nothing below it but data-only repos, must name progdeps itself.
    Repos above it may name progdeps too, but needn't: they inherit it."""
    tool = config.tool_name
    if any(spec.name == tool for spec in specs) or any(spec.build != NOBUILD for spec in specs):
        return
    raise Error(f"{name} at {where} is a root repo, with nothing built below it, so its "
                f"{DEPS_FILE} must name {config.tool_repo}, as in group/{tool}:LINE")


class Config:
    def __init__(self):
        if not CONFIG.exists():
            raise Error(f"{CONFIG} not found")
        parser = configparser.ConfigParser()
        parser.read(CONFIG)
        self.git_base = parser["git"]["base"]
        self.tool_repo = parser["git"].get("tool_repo", "progdeps")
        self.flat = parser["git"].getboolean("flat", fallback=False)
        hints = parser["git"].get("tool_hints", "")
        self.tool_hints = [name for name in re.split(r"[\s,]+", hints) if name]
        self.store_url = parser["store"]["url"].rstrip("/")
        self.token_file = Path(parser["store"]["token_file"]).expanduser()
        mount = parser["store"].get("mount")
        self.mount = Path(mount).expanduser() if mount else None

    @property
    def tool_name(self):
        return self.tool_repo.rsplit("/", 1)[-1]

    def git_url(self, repo):
        # A flat server has no groups, so it uses only the repo name
        path = repo.rsplit("/", 1)[-1] if self.flat else repo
        return f"{self.git_base}/{path}.git"


class Store:
    """Prebuilt output, one tarball per build key."""

    def __init__(self, config):
        self.base = config.store_url
        self.token = config.token_file.read_text().strip()

    def _url(self, node):
        return f"{self.base}/{node.name}/{node.key}/{VARIANT}.tar.gz"

    def _open(self, node, method="GET", data=None):
        request = urllib.request.Request(self._url(node), data=data, method=method,
                                         headers={"PRIVATE-TOKEN": self.token})
        return urllib.request.urlopen(request)

    def has(self, node):
        try:
            with self._open(node, "HEAD"):
                return True
        except urllib.error.HTTPError as error:
            if error.code == 404:
                return False
            raise Error(f"store: {node.name}: HTTP {error.code}")

    def download(self, node, path):
        with self._open(node) as response, open(path, "wb") as out:
            shutil.copyfileobj(response, out)

    def upload(self, node, path):
        with self._open(node, "PUT", Path(path).read_bytes()):
            pass


class Resolver:
    """Follows deps files through the chain, keeping bare mirrors under STATE."""

    def __init__(self, config, state):
        self.config = config
        self.mirrors = Path(state) / "repos"
        self.nodes = {}
        self.order = []    # dependencies come before what needs them
        self.active = []

    def fetch(self, spec):
        """Gets one commit and no file contents, returning its mirror and commit.

        Assumes the server allows fetching a raw commit hash. Branches and tags always
        work. A more robust version would detect that and fall back to a deeper fetch,
        or to `git archive --remote`, and report what the server refused.
        """
        path = self.mirrors / f"{spec.name}.git"
        url = self.config.git_url(spec.repo)
        if not path.exists():
            path.mkdir(parents=True)
            run(["git", "-C", path, "init", "-q", "--bare", "--template="])
            run(["git", "-C", path, "remote", "add", "origin", url])
        partial = ["--filter=blob:none"] if "://" in url else []
        run(["git", "-C", path, "fetch", "-q", "--depth", "1", *partial, "origin", spec.ref])
        return path, run(["git", "-C", path, "rev-parse", "FETCH_HEAD^{commit}"], capture=True)

    def conflict(self, known, spec, commit):
        raise Error(f"conflict: {spec.name} is requested two ways: "
                    f"{known.spec.ref} ({known.commit[:7]}, {known.spec.root_var}, "
                    f"{known.spec.build}) and {spec.ref} ({commit[:7]}, "
                    f"{spec.root_var}, {spec.build})")

    def agrees(self, known, spec, commit):
        return (known.commit, known.spec.root_var, known.spec.build) == \
            (commit, spec.root_var, spec.build)

    def add_frozen(self, specs, chosen=None):
        """Walks a frozen list like any other, but with every repo at the commit it names.

        Who needs whom comes from each dep's deps.data at that commit, and must agree with
        the list. Keys are always computed here: packageKeysUsed in the header is only a
        record, and nothing reads it. Returns the list's direct deps.
        """
        listed = {spec.name: spec for spec in specs}

        def walk(spec):
            known = self.nodes.get(spec.name)
            if known:
                if not self.agrees(known, spec, spec.ref):
                    self.conflict(known, spec, spec.ref)
                return known
            if spec.name in self.active:
                raise Error(f"dependency cycle through {spec.name}")
            mirror, commit = self.fetch(spec)
            header, wanted = self.deps_at(spec, mirror, commit)
            if spec.build != NOBUILD and "release" not in header:
                check_root(self.config, spec.name, [w for w in wanted if w.direct], commit[:7])
            children = []
            self.active.append(spec.name)
            for child in (child for child in wanted if child.direct):
                locked = listed.get(child.name)
                if locked is None:
                    raise Error(f"{spec.name}'s {DEPS_FILE} at {commit[:7]} names "
                                f"{child.name}, which isn't in the locked list")
                same = (child.root_var, child.build) == (locked.root_var, locked.build)
                if "release" in header:    # a lower release: its commits are exact too
                    same = same and child.ref == locked.ref
                if not same:
                    raise Error(f"{spec.name}'s {DEPS_FILE} at {commit[:7]} has {child.name} as "
                                f"{child.ref}:{child.root_var}:{child.build}, but the locked "
                                f"list has {locked.ref[:7]}:{locked.root_var}:{locked.build}")
                children.append(walk(locked))
            self.active.pop()
            return self.add_node(spec, mirror, commit, children)

        for name in (chosen or direct_names(specs)):
            walk(listed[name])
        unused = set(listed) - set(self.nodes)
        if unused and not chosen:
            raise Error(f"the locked list has {' '.join(sorted(unused))}, but nothing in it "
                        f"needs them")
        return [self.nodes[name] for name in direct_names(specs) if name in self.nodes]

    def deps_at(self, spec, mirror, commit):
        name, text = deps_file_at(mirror, commit)
        if text is None:
            return {}, []
        return parse_file(text, f"{spec.name}/{name}")

    def add_node(self, spec, mirror, commit, children):
        node = Node(spec, commit, [child.name for child in children])
        node.data = self.data_hash(spec, mirror, commit)
        node.key = build_key(node, children)
        self.nodes[spec.name] = node
        self.order.append(node)
        return node

    def visit(self, spec, top=False):
        if spec.name in self.active:
            raise Error(f"dependency cycle through {spec.name}")
        mirror, commit = self.fetch(spec)
        known = self.nodes.get(spec.name)
        if known:
            if not self.agrees(known, spec, commit):
                self.conflict(known, spec, commit)
            return known
        header, specs = self.deps_at(spec, mirror, commit)
        if "release" in header:
            tag = header["release"]
            at_tag = spec.ref == tag and commit in remote_tag(self.config.git_url(spec.repo), tag)
            under_review = top and spec.ref == RELEASE_PREFIX + tag
            if not at_tag and not under_review:
                raise Error(f"{spec.name} at {spec.ref} has a frozen list for {tag}, but isn't "
                            f"that release. Was a release branch merged here by mistake?")
            children = self.add_frozen(specs)
        else:
            if spec.build != NOBUILD:
                check_root(self.config, spec.name, specs, f"{spec.ref} ({commit[:7]})")
            self.active.append(spec.name)
            children = [self.visit(child) for child in specs]
            self.active.pop()
        return self.add_node(spec, mirror, commit, children)

    def data_hash(self, spec, mirror, commit):
        """A repo with no build is only data, so only its env.sh above NOT_IN_KEY counts."""
        if spec.build != NOBUILD:
            return ""
        text = run(["git", "-C", mirror, "show", f"{commit}:env.sh"], capture=True)
        return hashlib.sha256(text.split(NOT_IN_KEY)[0].strip().encode()).hexdigest()

    def closure(self, node):
        """Every package node needs, directly or not, in build order."""
        names = set()

        def walk(current):
            for name in current.deps:
                if name not in names:
                    names.add(name)
                    walk(self.nodes[name])
        walk(node)
        return [n for n in self.order if n.name in names]


def remote_tag(url, tag):
    """The commits a tag names on the server; empty if it doesn't exist."""
    output = run(["git", "ls-remote", url, f"refs/tags/{tag}", f"refs/tags/{tag}^{{}}"],
                 capture=True)
    return [line.split()[0] for line in output.splitlines()]


def build_key(node, children):
    # The compiler isn't here: the platform data defines it, so changing it changes every key
    parts = [node.name, node.data or node.commit, node.spec.build]
    parts += sorted(f"{child.name}={child.key}" for child in children)
    return hashlib.sha256("\n".join(parts).encode()).hexdigest()[:16]


def build_env(project, nodes, folder_of):
    env = dict(os.environ)
    env[PROJECT_VAR] = str(project)
    for node in nodes:
        if node.spec.root_var:
            env[node.spec.root_var] = str(folder_of(node))
    libs = [str(Path(folder_of(node)) / "lib") for node in nodes]
    env["LD_LIBRARY_PATH"] = ":".join(libs + [env.get("LD_LIBRARY_PATH", "")])
    return env


def with_env(command, nodes, folder_of):
    """Prefixes a build command with the env.sh of every dep that has one."""
    sources = [f'. "{folder_of(node)}/env.sh"' for node in nodes
               if (Path(folder_of(node)) / "env.sh").exists()]
    return "; ".join(sources + [command])


def from_git(resolver, node, dest):
    """A data-only repo needs no package: its files come straight from git, at that commit."""
    mirror = resolver.fetch(node.spec)[0]
    with tempfile.TemporaryDirectory() as tmp:
        tarball = Path(tmp) / "repo.tar"
        run(["git", "-C", mirror, "archive", "--format=tar", "-o", tarball, node.commit])
        unpack(tarball, dest)
    (dest / MARKER).write_text(node.ident + "\n")


def unpack(path, dest):
    dest.mkdir(parents=True)
    with tarfile.open(path) as tar:
        tar.extractall(dest, filter="data")


def write_sourceme(project, nodes, folder_of):
    lines = ["# Generated by progdeps. Source this, then use plain make.",
             f"export {PROJECT_VAR}={project}"]
    roots = []
    for node in nodes:
        folder = Path(folder_of(node))
        where = f"${PROJECT_VAR}/{folder.relative_to(project)}"
        if node.spec.root_var:
            lines.append(f"export {node.spec.root_var}={where}")
            where = f"${node.spec.root_var}"
        if (folder / "env.sh").exists():
            lines.append(f". {where}/env.sh")
        if (folder / "progdeps").exists():
            lines.append(f"export PATH={where}:$PATH")
        if (folder / "lib").exists() or not node.data_only:
            roots.append(f"{where}/lib")
    libs = ":".join([f"${PROJECT_VAR}/lib"] + roots)
    lines.append(f"export LD_LIBRARY_PATH={libs}:$LD_LIBRARY_PATH")
    text = "\n".join(lines) + "\n"
    path = project / "sourceme.sh"
    path.write_text(text)
    path.chmod(0o755)
    print(f"Created for developers to source, for example in ~/.bashrc:\n{path}\n{text}")


def mount_folder(config, node):
    """Where node's prebuilt is on the mount, or None if it isn't there."""
    if config.mount is None:
        return None
    folder = config.mount / node.name / node.ident
    return folder if (folder / MARKER).exists() else None


def add_to_mount(config, node, tarball):
    """Unpacks into place all at once, so nobody sees a half-written folder."""
    if config.mount is None or mount_folder(config, node):
        return
    folder = config.mount / node.name / node.ident
    temporary = folder.with_name(f".{VARIANT}.{os.getpid()}")
    unpack(tarball, temporary)
    (temporary / MARKER).write_text(node.ident + "\n")
    temporary.rename(folder)


def remove_dep(dest):
    if dest.is_symlink():
        dest.unlink()
    else:
        shutil.rmtree(dest, ignore_errors=True)


def read_deps(project):
    deps_file = deps_file_in(project)
    return parse_file(deps_file.read_text(), deps_file) if deps_file.exists() else ({}, [])


def selection(project, names, only=(), drop=(), everything=False):
    """The remembered --only selection, updated; empty means everything."""
    unknown = (set(only) | set(drop)) - set(names)
    if unknown:
        raise Error(f"not in {DEPS_FILE}: {' '.join(sorted(unknown))}")
    remembered = project / STATE / "only"
    if everything:
        remembered.unlink(missing_ok=True)
    chosen = set(remembered.read_text().split()) if remembered.exists() else set()
    if drop and not chosen:
        chosen = set(names)    # dropping from everything means keeping the rest
    chosen = (chosen | set(only)) - set(drop)
    if only or drop:
        remembered.parent.mkdir(parents=True, exist_ok=True)
        remembered.write_text("\n".join(sorted(chosen)) + "\n")
    if chosen:
        left_out = sorted(set(names) - chosen)
        print(f"sparse: {' '.join(sorted(chosen))}"
              + (f" (not selected: {' '.join(left_out)})" if left_out else ""))
    return chosen


def check_release(project, header):
    """A frozen list counts only at its release tag, or on a release branch under review."""
    tag = header["release"]
    branch = run(["git", "-C", project, "branch", "--show-current"], capture=True)
    tagged = tag in run(["git", "-C", project, "tag", "--points-at", "HEAD"], capture=True).split()
    if branch and branch != RELEASE_PREFIX + tag:
        raise Error(f"{DEPS_FILE} is frozen for {tag}, but this is branch {branch}. "
                    f"Was a release branch merged here by mistake?")
    if tagged:
        return
    if not branch:
        raise Error(f"{DEPS_FILE} is frozen for {tag}, but this commit isn't that release")
    if run(["git", "-C", project, "tag", "--list", tag], capture=True):
        raise Error(f"{DEPS_FILE} is frozen for {tag}, but {tag} is on a different commit")
    print(f"unreleased: {tag} is under review on {branch}")


def load_tree(project, config, only=(), drop=(), everything=False):
    header, specs = read_deps(project)
    chosen = selection(project, direct_names(specs), only, drop, everything)
    resolver = Resolver(config, project / STATE)
    if "release" in header:
        check_release(project, header)
        resolver.add_frozen(specs, chosen)
    else:
        if deps_file_in(project).exists():
            check_root(config, project.name, specs, "the top")
        for spec in specs:
            if not chosen or spec.name in chosen:
                resolver.visit(spec)
    return resolver


def prune(deps_dir, nodes):
    """Removes deps nothing needs now, except clones, which may hold work."""
    for path in sorted(deps_dir.iterdir()):
        if path.name in nodes:
            continue
        if (path / ".git").exists():
            print(f"{path.name}: no longer needed, keeping your clone in {path}")
        else:
            print(f"{path.name}: no longer needed, removing")
            remove_dep(path)


def sync(project, config, mode="auto", src=(), allsrcs=False, only=(), drop=(),
         everything=False, known=()):
    project = Path(project).resolve()
    resolver = load_tree(project, config, only, drop, everything)
    if allsrcs:    # data-only repos have nothing to build, and always come from git
        src = [name for name, node in resolver.nodes.items() if not node.data_only]
    unknown = (set(src) | set(known)) - set(resolver.nodes)
    if unknown:
        raise Error(f"not a dependency here: {' '.join(sorted(unknown))}")

    deps_dir = project / DEPS_DIR
    deps_dir.mkdir(exist_ok=True)
    folder_of = lambda node: deps_dir / node.name
    store = Store(config)
    for node in resolver.order:
        dest = folder_of(node)
        marker = dest / MARKER
        if (dest / ".git").exists() or node.name in src:
            if not (dest / ".git").exists():
                remove_dep(dest)
                run(["git", "clone", "-q", config.git_url(node.spec.repo), dest])
                run(["git", "-C", dest, "checkout", "-q", node.commit])
            print(f"{node.name}: building from source in {dest}")
            needs = resolver.closure(node)
            run(["sh", "-c", with_env(node.spec.build, needs, folder_of)], cwd=dest,
                env=build_env(project, needs, folder_of))
            continue
        current = marker.exists() and marker.read_text().strip() == node.ident
        if node.data_only:
            if current:
                print(f"{node.name}: already current ({node.commit[:7]})")
            else:
                print(f"{node.name}: from git at {node.commit[:7]}")
                remove_dep(dest)
                from_git(resolver, node, dest)
            continue
        linked = dest.is_symlink()
        wanted = mount_folder(config, node)
        if mode == "mount" and wanted is None:
            raise Error(f"{node.name}: {node.ident} is not on the mount "
                        f"({config.mount or 'no mount configured'})")
        if mode == "auto" and current:
            print(f"{node.name}: already current ({node.ident})")
        elif mode == "mount" and current and linked:
            print(f"{node.name}: already current on the mount ({node.ident})")
        elif mode == "download" and current and not linked:
            print(f"{node.name}: already current ({node.ident})")
        elif mode != "download" and wanted:
            print(f"{node.name}: using the mount, {wanted}")
            remove_dep(dest)
            dest.symlink_to(wanted)
        elif store.has(node):
            print(f"{node.name}: downloading {node.ident}")
            remove_dep(dest)
            with tempfile.TemporaryDirectory() as tmp:
                tarball = Path(tmp) / "package.tar.gz"
                store.download(node, tarball)
                unpack(tarball, dest)
            marker.write_text(node.ident + "\n")
        else:
            raise Error(f"{node.name}: no prebuilt for {node.ident} at "
                        f"{node.spec.ref} ({node.commit[:7]}). Run publish, or use "
                        f"--src {node.name}.")
    prune(deps_dir, resolver.nodes)
    write_sourceme(project, resolver.order, folder_of)


def cmd_get(args, config):
    name = args.repo.rsplit("/", 1)[-1]
    dest = Path(args.dir or name)
    if dest.exists():
        raise Error(f"{dest} already exists")
    run(["git", "clone", "-q", config.git_url(args.repo), dest])
    run(["git", "-C", dest, "checkout", "-q", args.ref])
    hand_off(dest, args, config)
    finish_get(dest, args, config)


def hand_off(dest, args, config):
    """Runs the rest of `get` with this line's own tool, so old lines keep their rules.

    The tool's version comes from the first progdeps line found going down the chain.
    Only this step and the deps file's line format have to stay stable from one tool
    version to the next.
    """
    if os.environ.get("PROGDEPS_HANDED_OFF"):
        return
    project = dest.resolve()
    if not deps_file_in(project).exists():
        print(f"note: no {DEPS_FILE} here, so using this copy of the tool")
        return
    resolver = Resolver(config, project / STATE)
    tool = find_tool(resolver, config, read_deps(project)[1])
    node = Node(tool, resolver.fetch(tool)[1])
    folder = project / DEPS_DIR / config.tool_name
    from_git(resolver, node, folder)
    print(f"handing off to the progdeps for this line, at {node.commit[:7]}", flush=True)
    command = [str(folder / "progdeps"), "finish-get", str(project), "--mode", args.mode]
    for option, values in (("--only", args.only), ("--src", args.src)):
        command += [item for value in values for item in (option, value)]
    command += ["--allsrcs"] if args.allsrcs else []
    os.execve(command[0], command, {**os.environ, "PROGDEPS_HANDED_OFF": "1"})


def find_tool(resolver, config, specs):
    """The first progdeps line going down the chain, reading as few deps files as it can.

    Every root repo names progdeps, so a top usually finds it one or two levels down.
    It goes breadth first, trying the repos in tool_hints first, such as dep1 and prog,
    and stops at the first line found. It doesn't check that every line agrees: the
    line's own tool resolves the whole tree right after, and catches that. The mirrors
    it fetches stay, so that resolve reuses them.
    """
    tool = config.tool_name
    hint = {name: rank for rank, name in enumerate(config.tool_hints)}
    queue, seen = list(specs), set()
    while True:
        found = next((spec for spec in queue if spec.name == tool), None)
        if found:
            return found
        queue = [spec for spec in queue if spec.name not in seen]
        if not queue:
            raise Error(f"no {config.tool_repo} line found below the top. Every root repo, "
                        f"one with nothing built below it, must name it in its {DEPS_FILE}")
        spec = min(queue, key=lambda spec: hint.get(spec.name, len(hint)))
        queue.remove(spec)
        seen.add(spec.name)
        queue += resolver.deps_at(spec, *resolver.fetch(spec))[1]


def finish_get(dest, args, config):
    try:
        sync(dest, config, args.mode, args.src, args.allsrcs, args.only)
    except Error as error:
        raise Error(f"{error}\nStopped partway, and everything so far is still in {dest}. "
                    f"Fix that, then run `progdeps sync` there, or `progdeps add DEP --src` "
                    f"for a dep you wanted as source.")


def behind_upstream(project, pull=False):
    """Warns if this repo's branch is behind the server. The tool never changes your source
    unless asked, and then only by fast-forward.
    """
    git = ["git", "-C", str(project)]
    if subprocess.run(git + ["rev-parse", "-q", "--verify", "@{u}"], capture_output=True).returncode:
        return    # detached, or a branch with nothing to compare to
    if subprocess.run(git + ["fetch", "-q", "origin"], capture_output=True).returncode:
        return    # offline; don't get in the way
    behind = int(run(git + ["rev-list", "--count", "HEAD..@{u}"], capture=True))
    if not behind:
        return
    upstream = run(git + ["rev-parse", "--abbrev-ref", "@{u}"], capture=True)
    if pull:
        if subprocess.run(git + ["merge", "-q", "--ff-only", "@{u}"]).returncode:
            raise Error(f"can't fast-forward to {upstream}. Sort that out with git, then sync.")
        print(f"pulled {behind} commit{'s' if behind > 1 else ''} from {upstream}")
    else:
        print(f"warning: this repo is {behind} commit{'s' if behind > 1 else ''} behind "
              f"{upstream}. Run `git pull`, then sync again, or use `sync --pull`.")


def cmd_sync(args, config):
    behind_upstream(".", args.pull)
    sync(".", config, args.mode)


def cmd_add(args, config):
    if args.all == bool(args.dep):
        raise Error("add takes one dep, or --all")
    if args.all:
        sync(".", config, args.mode, everything=True)
        return
    project = Path(".").resolve()
    direct = direct_names(read_deps(project)[1])
    sparse = (project / STATE / "only").exists()
    only = [args.dep] if sparse and args.dep in direct else []
    sync(project, config, args.mode, [args.dep] if args.src else [], only=only, known=[args.dep])


def cmd_drop(args, config):
    sync(".", config, drop=[args.dep])


def cmd_status(args, config):
    project = Path(".").resolve()
    behind_upstream(project)
    resolver = load_tree(project, config)
    behind = 0
    for node in resolver.order:
        dest = project / DEPS_DIR / node.name
        if (dest / ".git").exists():
            state = "source checkout"
        elif not (dest / MARKER).exists():
            state, behind = "missing", behind + 1
        elif (dest / MARKER).read_text().strip() == node.ident:
            state = "current, on mount" if dest.is_symlink() else "current, local copy"
            state = "current" if node.data_only else state
        else:
            state, behind = "BEHIND", behind + 1
        ref = node.commit[:7] if node.spec.ref == node.commit else node.spec.ref
        built_as = "from git" if node.data_only else node.ident
        print(f"{node.name:8} {ref:10} {node.commit[:7]}  {built_as}  {state}")
    print("run `progdeps sync` to update" if behind else "up to date")


def cmd_list(args, config):
    repo = args.repo or config.tool_repo
    output = run(["git", "ls-remote", "--heads", "--tags", config.git_url(repo), args.pattern],
                 capture=True)
    found = {}
    for line in output.splitlines():
        commit, ref = line.split()
        kind, name = ref.split("/", 2)[1:]
        found[name.removesuffix("^{}")] = (kind, commit)    # a tag's ^{} line is its real commit
    if not args.repo:
        found.pop("master", None)    # the tool, not a version line
    for name, (kind, commit) in sorted(found.items()):
        print(f"{name:20} {commit[:7]}  {'branch' if kind == 'heads' else 'tag'}")
    if not found:
        print(f"nothing matches {args.pattern} in {repo}")


def cmd_publish(args, config):
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        resolver = Resolver(config, work)
        top = Spec(args.repo, args.ref, args.repo.rsplit("/", 1)[-1].upper() + "ROOT", "make")
        resolver.visit(top, top=True)
        store = Store(config)
        # Lay it out like a project from get, so $PROJECTROOT/deps/NAME means the same here
        top_node = resolver.nodes[top.name]
        project = work / top.name
        run(["git", "clone", "-q", config.git_url(top.repo), project])
        run(["git", "-C", project, "checkout", "-q", top_node.commit])
        folder_of = lambda node: project if node is top_node else project / DEPS_DIR / node.name
        built = []
        for node in resolver.order:
            if node.data_only:
                from_git(resolver, node, folder_of(node))
                continue
            if store.has(node):
                print(f"{node.name}: already in store ({node.ident})")
                if config.mount and not mount_folder(config, node):
                    tarball = work / f"{node.key}.tar.gz"
                    store.download(node, tarball)
                    add_to_mount(config, node, tarball)
                    print(f"{node.name}: added to the mount")
                continue
            for dep in resolver.closure(node):
                if not folder_of(dep).exists():
                    tarball = work / f"{dep.key}.tar.gz"
                    store.download(dep, tarball)
                    unpack(tarball, folder_of(dep))
            print(f"{node.name}: building {node.commit[:7]} as {node.ident}")
            checkout = folder_of(node)
            if node is not top_node:
                run(["git", "clone", "-q", config.git_url(node.spec.repo), checkout])
                run(["git", "-C", checkout, "checkout", "-q", node.commit])
            needs = resolver.closure(node)
            run(["sh", "-c", with_env(node.spec.build, needs, folder_of)], cwd=checkout,
                env=build_env(project, needs, folder_of))
            tarball = work / f"{node.key}.tar.gz"
            with tarfile.open(tarball, "w:gz") as tar:
                for folder in OUTPUT:
                    if (checkout / folder).exists():
                        tar.add(checkout / folder, arcname=folder)
            store.upload(node, tarball)
            add_to_mount(config, node, tarball)
            if node is not top_node:    # leave just the package, as a prebuilt would be
                shutil.rmtree(checkout)
                unpack(tarball, checkout)
            built.append(node.name)
    total = len([node for node in resolver.order if not node.data_only])
    print(f"built {len(built)} of {total}: {' '.join(built) or 'nothing'}")


def freeze_patch(resolver, specs, uses):
    """Applies --use to an existing frozen list, then walks it, so keys above what changed
    are new. A new dep in a changed repo is an error, since it isn't in the list.
    """
    changes = dict(use.split("=", 1) for use in uses)
    listed = {spec.name: spec for spec in specs}
    unknown = set(changes) - set(listed)
    if unknown:
        raise Error(f"--use: not in this list: {' '.join(sorted(unknown))}")
    for name, ref in changes.items():
        listed[name].ref = resolver.fetch(Spec(listed[name].repo, ref))[1]
    resolver.add_frozen(specs)


def same_url(a, b):
    def norm(url):
        url = url.strip().rstrip("/").removesuffix(".git")
        return os.path.realpath(url) if "://" not in url and ":" not in url else url
    return norm(a) == norm(b)


def find_checkout(url, name):
    """The checkout of url around the current directory, and its remote for url.

    Walks up through enclosing repos, so a clone in deps/ doesn't hide the project.
    Returns (None, None) outside any repo, and errors inside some other repo.
    """
    here, other = Path.cwd(), None
    while True:
        found = subprocess.run(["git", "-C", here, "rev-parse", "--show-toplevel"],
                               capture_output=True, text=True)
        if found.returncode != 0:
            break
        top = Path(found.stdout.strip())
        for remote in run(["git", "-C", top, "remote"], capture=True).split():
            if same_url(run(["git", "-C", top, "remote", "get-url", remote], capture=True), url):
                return top, remote
        other = other or top
        here = top.parent
    if other:
        raise Error(f"you're inside {other}, which isn't a checkout of {name}. Run plan inside "
                    f"that repo's checkout, or outside any repo to get a fresh clone.")
    return None, None


def commit_file(repo, parent, name, text, message):
    """A new commit on parent with one file replaced, without touching the work tree,
    the index, or the current branch."""
    with tempfile.TemporaryDirectory() as tmp:
        env = {**os.environ, "GIT_INDEX_FILE": str(Path(tmp) / "index")}
        content = Path(tmp) / name
        content.write_text(text)
        run(["git", "-C", repo, "read-tree", parent], env=env)
        blob = run(["git", "-C", repo, "hash-object", "-w", content], capture=True)
        run(["git", "-C", repo, "update-index", "--add", "--cacheinfo", f"100644,{blob},{name}"],
            env=env)
        tree = run(["git", "-C", repo, "write-tree"], env=env, capture=True)
        return run(["git", "-C", repo, "commit-tree", tree, "-p", parent, "-m", message],
                   capture=True)


def cmd_plan(args, config):
    """Adds a local branch REL_<tag> holding the locked list. The person pushes it."""
    url = config.git_url(args.repo)
    branch = RELEASE_PREFIX + args.tag
    if remote_tag(url, args.tag):
        raise Error(f"{args.tag} already exists")
    if run(["git", "ls-remote", "--heads", url, branch], capture=True):
        raise Error(f"{branch} already exists on the server")
    checkout, remote = find_checkout(url, args.repo)
    if checkout is None:
        checkout, remote = Path(args.repo.rsplit("/", 1)[-1]).resolve(), "origin"
        if checkout.exists():
            raise Error(f"{checkout} already exists, and isn't a checkout of {args.repo}")
        run(["git", "clone", "-q", url, checkout])
        print(f"cloned {args.repo} into {checkout}")
    if run(["git", "-C", checkout, "branch", "--list", branch], capture=True):
        raise Error(f"{branch} already exists in {checkout}. To start over: "
                    f"git branch -D {branch}")
    run(["git", "-C", checkout, "fetch", "-q", remote, args.ref])
    start = run(["git", "-C", checkout, "rev-parse", "FETCH_HEAD^{commit}"], capture=True)
    deps_name, text = deps_file_at(checkout, start)
    header, specs = parse_file(text, deps_name) if text is not None else ({}, [])
    direct = direct_names(specs)
    with tempfile.TemporaryDirectory() as tmp:
        resolver = Resolver(config, tmp)
        if "release" in header:
            freeze_patch(resolver, specs, args.use)
        else:
            if args.use:
                raise Error("--use is for planning from a release")
            check_root(config, args.repo.rsplit("/", 1)[-1], specs, f"{args.ref} ({start[:7]})")
            for spec in specs:
                resolver.visit(spec)
    lines = [spec_line(n.spec, n.commit, n.name in direct) for n in resolver.order]
    frozen = {"release": args.tag, "branchedFrom": args.ref,
              "packageKeysUsed": {n.name: n.key for n in resolver.order}}
    text = json.dumps(frozen, indent=2) + "\n" + "\n".join(lines) + "\n"
    commit = commit_file(checkout, start, deps_name, text, f"Freeze dependencies for {args.tag}")
    run(["git", "-C", checkout, "branch", branch, commit])
    store = Store(config)
    missing = [n.name for n in resolver.order if not n.data_only and not store.has(n)]
    print(f"Planned {args.tag} from {args.ref} ({remote}, {start[:7]}).\n"
          f"Created branch {branch} in {checkout}, as commit {commit[:7]}.\n"
          f"Your working tree and current branch weren't touched.\n")
    print("\n".join(f"  {line}" for line in lines))
    if missing:
        print(f"not yet prebuilt for {VARIANT}: {' '.join(missing)}")
    print(f"\nTo review:   git show {branch}:{deps_name}\n"
          f"             or: progdeps get {args.repo} {branch}, after pushing\n"
          f"To release:  git push {remote} {branch}\n"
          f"             then: progdeps release {args.repo} {args.tag}\n"
          f"To discard:  git branch -D {branch}")


def cmd_release(args, config):
    """Builds what's missing, then tags every repo below, and the top last.

    The top's tag means the release is done. Rerunning after a failure tags only
    what's missing, and a release whose top is tagged is refused.
    """
    url = config.git_url(args.repo)
    branch = RELEASE_PREFIX + args.tag
    if remote_tag(url, args.tag):
        raise Error(f"{args.tag} is already released")
    if not run(["git", "ls-remote", "--heads", url, branch], capture=True):
        raise Error(f"{branch} isn't on the server. Run plan, then push the branch it makes.")
    cmd_publish(argparse.Namespace(repo=args.repo, ref=branch), config)
    with tempfile.TemporaryDirectory() as tmp:
        resolver = Resolver(config, tmp)
        top = Spec(args.repo, branch)
        mirror, commit = resolver.fetch(top)
        deps_name, text = deps_file_at(mirror, commit)
        header, specs = parse_file(text or "", deps_name)
        if header.get("release") != args.tag:
            raise Error(f"{branch} doesn't hold a list made by `progdeps plan` for {args.tag}")
        added = 0
        for spec, ref in [(spec, spec.ref) for spec in specs] + [(top, commit)]:
            existing = remote_tag(config.git_url(spec.repo), args.tag)
            if ref in existing:
                print(f"{spec.name}: already tagged")
                continue
            if existing:
                raise Error(f"{spec.name}: {args.tag} is already on a different commit")
            mirror = resolver.fetch(Spec(spec.repo, ref))[0]
            run(["git", "-C", mirror, "push", "-q", "origin", f"{ref}:refs/tags/{args.tag}"])
            print(f"{spec.name}: tagged {ref[:7]}")
            added += 1
    print(f"released {args.tag}: tagged {added} repos, {args.repo} last")


def add_mode_options(parser):
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--mount", dest="mode", action="store_const", const="mount",
                       help="use only the network mount; error if a prebuilt isn't there")
    group.add_argument("--download", dest="mode", action="store_const", const="download",
                       help="always make real local copies")
    parser.set_defaults(mode="auto")


def main():
    parser = argparse.ArgumentParser(prog="progdeps", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    get = commands.add_parser("get")
    get.add_argument("repo")
    get.add_argument("ref")
    get.add_argument("--dir")
    get.add_argument("--only", action="append", default=[],
                     help="make a sparse tree: this direct dep and what it needs; can repeat")
    get.add_argument("--src", action="append", default=[],
                     help="clone and build this dep from source; can repeat")
    get.add_argument("--allsrcs", action="store_true",
                     help="clone and build every dep from source")
    add_mode_options(get)
    get.set_defaults(func=cmd_get)
    sync_cmd = commands.add_parser("sync")
    sync_cmd.add_argument("--pull", action="store_true",
                          help="fast-forward this repo to the server first")
    add_mode_options(sync_cmd)
    sync_cmd.set_defaults(func=cmd_sync)
    add = commands.add_parser("add")
    add.add_argument("dep", nargs="?")
    add.add_argument("--src", action="store_true", help="clone and build it from source")
    add.add_argument("--all", action="store_true", help="end a sparse tree: use every dep")
    add_mode_options(add)
    add.set_defaults(func=cmd_add)
    drop = commands.add_parser("drop")
    drop.add_argument("dep")
    drop.set_defaults(func=cmd_drop)
    finish = commands.add_parser("finish-get", help=argparse.SUPPRESS)
    finish.add_argument("dest", type=Path)
    finish.add_argument("--mode", default="auto")
    finish.add_argument("--only", action="append", default=[])
    finish.add_argument("--src", action="append", default=[])
    finish.add_argument("--allsrcs", action="store_true")
    finish.set_defaults(func=lambda args, config: finish_get(args.dest, args, config))
    commands.add_parser("status").set_defaults(func=cmd_status)
    listing = commands.add_parser("list")
    listing.add_argument("pattern", nargs="?", default="*")
    listing.add_argument("--repo", help="a repo's branches and tags, instead of version lines")
    listing.set_defaults(func=cmd_list)
    publish = commands.add_parser("publish")
    publish.add_argument("repo")
    publish.add_argument("ref")
    publish.set_defaults(func=cmd_publish)
    plan = commands.add_parser("plan")
    plan.add_argument("repo")
    plan.add_argument("ref")
    plan.add_argument("tag")
    plan.add_argument("--use", action="append", default=[], metavar="DEP=REF",
                      help="when planning from a release: move this dep; can repeat")
    plan.set_defaults(func=cmd_plan)
    release = commands.add_parser("release")
    release.add_argument("repo")
    release.add_argument("tag")
    release.set_defaults(func=cmd_release)
    args = parser.parse_args()
    try:
        args.func(args, Config())
    except Error as error:
        sys.exit(f"progdeps: {error}")


if __name__ == "__main__":
    main()
