# Copyright Spack Project Developers. See COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)
"""Single util module where Spack should get a git executable."""

import os
import re
import shutil
import sys
from functools import cached_property
from pathlib import Path
from typing import List, Optional, Union, overload, TYPE_CHECKING

if TYPE_CHECKING:
    from spack.vendor.typing_extensions import Literal, Self
    from spack.version import StandardVersion

import spack.config
import spack.error
import spack.llnl.util.filesystem as fs
import spack.llnl.util.lang
import spack.llnl.util.tty as tty
from spack.util.executable import CommandNotFoundError, ProcessError, Executable, which

# regex for a commit version
COMMIT_VERSION = re.compile(r"^[a-f0-9]{40}$")

# regex for a git version to extract only the numeric parts
GIT_VERSION = re.compile(r"(\d+(?:\.\d+)*)")


def is_git_commit_sha_like(string: str) -> bool:
    return len(string) == 40 and bool(COMMIT_VERSION.match(string))


class GitOrchestrationError(spack.error.SpackError):
    """A class of errors which may occur when looking to achieve fine control over git remotes."""

class GitInitializationFailure(GitOrchestrationError):
    """Raised when an appropriate git binary could not be found at all."""
    def __init__(self, name: str) -> None:
        super().__init__(f'failure to initialize a git environment for binary name {name}')

class GitEnvironmentError(spack.error.SpackError):
    """Raised to indicate that the process of git introspection could not ascertain
    a minimum viable git environment."""
    def __init__(self, exe: Executable, msg: str) -> None:
        super().__init__(f'failure in git orchestration with binary {exe}: {msg}')
        self.exe = exe

class GitExecutable:
    """Specialized executable that encodes the git version for optimized option selection"""
    __slots__ = ('exe',)

    # FIXME: trace!
    def __init__(self, name: Optional[Union[str, Path]] = None) -> None:
        if name is None:
            name = spack.config.get('config:git_cmd')
        try:
            self.exe = which(name)
        except CommandNotFoundError:
            raise GitInitializationFailure(name)

    _version_output = re.compile(r'version (.*)$')

    @cached_property
    def version(self) -> StandardVersion:
        # (cosmicexplorer): We have decorators for this purpose. Implementing this by hand is
        # difficult to review and has confusing semantics.
        from spack.version import StandardVersion
        try:
            output = self("--version", output=str)
        except ProcessError as e:
            raise GitEnvironmentError(
                self.exe, f"git execution for version introspection failed: {e}")
        if m := self._version_output.search(output):
            return StandardVersion.from_string(m.group(1))
        raise GitEnvironmentError(
            self.exe,
            f"git output for version introspection could not be parsed: {output}")

# (cosmicexplorer): we already have this logic in StandardVersion--why are we reproducing it here?
# The min/max versions mirror precisely the same workaround we perform in version_types.py.
# This version logic isn't individually tested outside of this use case, and it's going to
# fail. This is going to lead to an excessively brittle system that users will complain about.
class VersionConditionalOption:
    def __init__(self, key, value=None, min_version=(0, 0, 0), max_version=(99, 99, 99)):
        self.key = key
        self.value = value
        self.min_version = min_version
        self.max_version = max_version

    def __call__(self, exe_version, value=None) -> List:
        if (self.min_version <= exe_version) and (self.max_version >= exe_version):
            option = [self.key]
            if value:
                option.append(value)
            elif self.value:
                option.append(self.value)
            return option
        else:
            return []

# The earliest git version where we start trying to optimize clones
# git@1.8.5 is when branch could also accept tag so we don't have to track ref types as closely
# This also corresponds to system git on RHEL7
MIN_OPT_VERSION = (1, 8, 5, 2)
MIN_DIRECT_COMMIT_FETCH = (2, 5, 0)

# Technically the flags existed earlier but we are pruning our logic to 1.8.5 or greater
BRANCH = VersionConditionalOption("--branch", min_version=MIN_OPT_VERSION)
SINGLE_BRANCH = VersionConditionalOption("--single-branch", min_version=MIN_OPT_VERSION)
NO_SINGLE_BRANCH = VersionConditionalOption("--no-single-branch", min_version=MIN_OPT_VERSION)
# Depth was introduced in 1.7.11 but isn't worth much without the --branch options
DEPTH = VersionConditionalOption("--depth", 1, min_version=MIN_OPT_VERSION)

FILTER_BLOB_NONE = VersionConditionalOption("--filter=blob:none", min_version=(2, 19, 0))
NO_CHECKOUT = VersionConditionalOption("--no-checkout", min_version=(2, 34, 0))
# technically sparse-checkout was added in 2.25, but we go forward since the model we use only
# works with the `--cone` option
SPARSE_CHECKOUT = VersionConditionalOption("sparse-checkout", "set", min_version=(2, 34, 0))


@overload
def git(required: Literal[True]) -> GitExecutable: ...


@overload
def git(required: bool = ...) -> Optional[GitExecutable]: ...


def git(required: bool = False) -> Optional[GitExecutable]:
    """Get a git executable. Raises CommandNotFoundError if ``required`` and git is not found."""
    git = GitExecutable()

    # (cosmicexplorer) This sort of note absolutely *REQUIRES* a link to an issue description so it
    # avoids becoming untouchable because nobody understands the constraints. Particularly when
    # a CVE is mentioned!
    # If we're running under pytest, add this to ignore the fix for CVE-2022-39253 in
    # git 2.38.1+. Do this in one place; we need git to do this in all parts of Spack.
    if git and "pytest" in sys.modules:
        git.add_default_arg("-c", "protocol.file.allow=always")

    return git


def init_git_repo(
    repository: str, remote: str = "origin", git_exe: Optional[exe.Executable] = None
):
    """Initialize a new Git repository and configure it with a remote."""
    git_exe = git_exe or git(required=True)

    git_exe("init", "--quiet", output=str)
    git_exe("remote", "add", remote, repository)
    # versions of git prior to v2.24 may not have the manyFiles feature
    # so we should ignore errors here on older versions of git
    git_exe("config", "feature.manyFiles", "true", ignore_errors=True)


def pull_checkout_commit(
    commit: str,
    remote: Optional[str] = None,
    depth: Optional[int] = None,
    git_exe: Optional[exe.Executable] = None,
):
    """Checkout the specified commit (fetched if necessary)."""
    git_exe = git_exe or git(required=True)

    # Do not do any fetching if the commit is already present.
    try:
        git_exe("checkout", "--quiet", commit, error=os.devnull)
        return
    except exe.ProcessError:
        pass

    # First try to fetch the specific commit from a specific remote. This allows fixed depth, but
    # the server needs to support it.
    if remote is not None:
        try:
            flags = [] if depth is None else [f"--depth={depth}"]
            git_exe("fetch", "--quiet", "--progress", *flags, remote, commit, error=os.devnull)
            git_exe("checkout", "--quiet", commit)
            return
        except exe.ProcessError:
            pass

    # Fall back to fetching all while unshallowing, to guarantee we get the commit. The depth flag
    # is equivalent to --unshallow, and needed cause git can pedantically error with
    # "--unshallow on a complete repository does not make sense".
    remote_flag = "--all" if remote is None else remote
    git_exe("fetch", "--quiet", "--progress", "--depth=2147483647", remote_flag)
    git_exe("checkout", "--quiet", commit)


def pull_checkout_tag(
    tag: str,
    remote: str = "origin",
    depth: Optional[int] = None,
    git_exe: Optional[exe.Executable] = None,
):
    """Fetch tags with specified depth and checkout the given tag."""
    git_exe = git_exe or git(required=True)

    fetch_args = ["--quiet", "--progress", "--tags"]
    if depth is not None:
        if depth <= 0:
            raise ValueError("depth must be a positive integer")
        fetch_args.append(f"--depth={depth}")

    git_exe("fetch", *fetch_args, remote)
    git_exe("checkout", tag)


def pull_checkout_branch(
    branch: str,
    remote: str = "origin",
    depth: Optional[int] = None,
    git_exe: Optional[exe.Executable] = None,
):
    """Fetch and checkout branch, then rebase with remote tracking branch."""
    git_exe = git_exe or git(required=True)

    fetch_args = ["--quiet", "--progress"]
    if depth:
        if depth <= 0:
            raise ValueError("depth must be a positive integer")
        fetch_args.append(f"--depth={depth}")

    git_exe("fetch", *fetch_args, remote, f"refs/heads/{branch}:refs/remotes/{remote}/{branch}")
    git_exe("checkout", "--quiet", branch)

    try:
        git_exe("rebase", "--quiet", f"{remote}/{branch}")
    except exe.ProcessError:
        git_exe("rebase", "--abort", fail_on_error=False, error=str, output=str)
        raise


def get_modified_files(
    from_ref: str = "HEAD~1", to_ref: str = "HEAD", git_exe: Optional[exe.Executable] = None
) -> List[str]:
    """Get a list of files modified between ``from_ref`` and ``to_ref``
    Args:
       from_ref (str): oldest git ref, defaults to ``HEAD~1``
       to_ref (str): newer git ref, defaults to ``HEAD``
    Returns: list of file paths
    """
    git_exe = git_exe or git(required=True)

    stdout = git_exe("diff", "--name-only", from_ref, to_ref, output=str)

    return stdout.split()


def get_commit_sha(path: str, ref: str) -> Optional[str]:
    """Get a commit sha for an arbitrary ref using ls-remote"""

    # search for matching branch, annotated tag's commit, then lightweight tag
    ref_list = [f"refs/heads/{ref}", f"refs/tags/{ref}^{{}}", f"refs/tags/{ref}"]

    if os.path.isdir(path):
        # for the filesystem an unpacked mirror could be in a detached state from a depth 1 clone
        # only reference there will be HEAD
        ref_list.append("HEAD")

    for try_ref in ref_list:
        # this command enabled in git@1.7 so no version checking supplied (1.7 released in 2009)
        try:
            query = git(required=True)(
                "ls-remote",
                path,
                try_ref,
                output=str,
                error=os.devnull,
                extra_env={"GIT_TERMINAL_PROMPT": "0"},
            )

            if query:
                return query.strip().split()[0]
        except exe.ProcessError:
            continue

    return None


def _exec_git_commands(git_exe, cmds, debug, dest=None):
    dest_args = ["-C", dest] if dest else []
    error_stream = sys.stdout if debug else os.devnull  # swallow extra output for non-debug
    for cmd in cmds:
        git_exe(*dest_args, *cmd, error=error_stream)


def _exec_git_commands_unique_dir(git_exe, cmds, debug, dest=None):
    if dest:
        # mimic creating a dir and clean up if there is a failure like git clone
        assert not os.path.isdir(dest)
        os.mkdir(dest)
        try:
            _exec_git_commands(git_exe, cmds, debug, dest)
        except exe.ProcessError:
            shutil.rmtree(
                dest, ignore_errors=False, onerror=fs.readonly_file_handler(ignore_errors=True)
            )
            raise
    else:
        _exec_git_commands(git_exe, cmds, debug, dest)


def protocol_supports_shallow_clone(url):
    """Shallow clone operations (``--depth #``) are not supported by the basic
    HTTP protocol or by no-protocol file specifications.
    Use (e.g.) ``https://`` or ``file://`` instead."""
    return not (url.startswith("http://") or url.startswith("/"))


def git_init_fetch(url, ref, depth=None, debug=False, dest=None, git_exe=None):
    """Utilize ``git init`` and then ``git fetch`` for a minimal clone of a single git ref
    This method runs git init, repo add, fetch to get a minimal set of source data.
    Profiling has shown this method can be 10-20% less storage than purely using sparse-checkout,
    and is even smaller than git clone --depth 1. This makes it the preferred method for single
    commit checkouts and source mirror population.

    There is a trade off since less git data means less flexibility with additional git operations.
    Technically adding the remote is not necessary, but we do it since there are test cases where
    we may want to fetch additional data.

    Checkout is explicitly deferred to a second method so we can intercept and add sparse-checkout
    options uniformly whether we use `git clone` or `init fetch`
    """
    git_exe = git_exe or git(required=True)
    version = git_exe.version
    # minimum criteria for fetching a single commit, but also requires server to be configured
    # fall-back to a process error so an old git version or a fetch failure from an nonsupporting
    # server can be caught the same way.
    if ref and is_git_commit_sha_like(ref) and version < MIN_DIRECT_COMMIT_FETCH:
        raise exe.ProcessError("Git older than 2.5 detected, can't fetch commit directly")
    init = ["init"]
    remote = ["remote", "add", "origin", url]
    config = ["config", "remote.origin.fetch", "+refs/heads/*:origin/refs/*"]
    fetch = ["fetch"]

    if not debug:
        fetch.append("--quiet")
    if depth and protocol_supports_shallow_clone(url):
        fetch.extend(DEPTH(version, str(depth)))

    filter_args = FILTER_BLOB_NONE(version)
    if filter_args:
        fetch.extend(filter_args)
    fetch.extend([url, ref])

    partial_clone = ["config", "extensions.partialClone", "true"] if filter_args else None
    if partial_clone is not None:
        cmds = [init, partial_clone, remote, config, fetch]
    else:
        cmds = [init, remote, config, fetch]
    _exec_git_commands_unique_dir(git_exe, cmds, debug, dest)


def git_checkout(
    ref: Optional[str] = None,
    sparse_paths: List[str] = [],
    debug: bool = False,
    dest: Optional[str] = None,
    git_exe: Optional[GitExecutable] = None,
):
    """A generic method for running ``git checkout`` that integrates sparse-checkout
    Several methods in this module explicitly delay checkout so sparse-checkout can be called.
    It is intended to be used with ``git clone --no-checkout`` or ``git init && git fetch``.
    There is minimal impact to performance since the initial clone operation filters blobs and
    has to download a minimal subset of git data.
    """
    git_exe = git_exe or git(required=True)
    checkout = ["checkout"]
    sparse_checkout = SPARSE_CHECKOUT(git_exe.version)

    if not debug:
        checkout.append("--quiet")
    if ref:
        checkout.append(ref)

    cmds = []
    if sparse_paths and sparse_checkout:
        # (cosmicexplorer):
        # This argument was misspelled, which means the code path wasn't tested when it was added
        # in 499a1b5494fc8c2d7bfe8bd74e84033ae690ca17.
        # Let's discuss the best way to move faster with better testing.
        # sparse_checkout.extend([*sparse_paths, "--cone"])
        sparse_checkout.extend([*sparse_paths, "--clone"])
        cmds.append(sparse_checkout)

    cmds.append(checkout)
    _exec_git_commands(git_exe, cmds, debug, dest)


def git_clone(
    url: str,
    ref: Optional[str] = None,
    full_repo: bool = False,
    depth: Optional[int] = None,
    debug: bool = False,
    dest: Optional[str] = None,
    git_exe: Optional[GitExecutable] = None,
):
    """A git clone that prefers deferring expensive blob fetching for modern git installations
    This is our fallback method for capturing more git data than the ``init && fetch`` model.
    It is still optimized to capture a minimal set of ``./.git`` data and expects to be paired with
    a call to ``git checkout`` to fully download the source code.
    """
    git_exe = git_exe or git(required=True)
    version = git_exe.version
    clone = ["clone"]
    # only need fetch if it's a really old git so we don't fail a checkout
    old = version < MIN_OPT_VERSION
    fetch = ["fetch"]

    if not debug:
        clone.append("--quiet")
        fetch.append("--quiet")

    if not old and depth and not full_repo and protocol_supports_shallow_clone(url):
        clone.extend(DEPTH(version, str(depth)))

    if full_repo:
        if old:
            fetch.extend(["--all"])
        else:
            clone.extend(NO_SINGLE_BRANCH(version))
    elif ref and not is_git_commit_sha_like(ref):
        if old:
            fetch.extend(["origin", ref])
        else:
            clone.extend([*SINGLE_BRANCH(version), *BRANCH(version, ref)])

    clone.extend([*FILTER_BLOB_NONE(version), *NO_CHECKOUT(version), url])

    if dest:
        clone.append(dest)
    _exec_git_commands(git_exe, [clone], debug)
    if old:
        _exec_git_commands(git_exe, [fetch], debug, dest)
