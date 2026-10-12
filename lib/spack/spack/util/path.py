# Copyright Spack Project Developers. See COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

"""Utilities for managing paths in Spack.

TODO: this is really part of spack.config. Consolidate it.
"""

import contextlib
import dataclasses
import functools
import os
import pathlib
import re
import subprocess
import stat
import sys
from enum import IntEnum
from functools import lru_cache, cached_property
from typing import TYPE_CHECKING, Any, ClassVar, Iterable, List, Optional, Union, cast, overload
from urllib.parse import ParseResult, urlparse

import spack.llnl.util.tty as tty
from spack.util.lang import memoized

if TYPE_CHECKING:
    from typing_extensions import Self

__all__ = []


class Path(IntEnum):
    """Enum to identify the path-style."""

    unix = 0
    windows = 1
    platform_path = windows if sys.platform == "win32" else unix


class PlatformPath(str):
    def __new__(cls, path: str, /, mode: int | Path = Path.platform_path) -> Self:
        if type(mode) is int:
            mode = Path(mode)
        ret = super().__new__(cls, format_os_path(path, mode))
        return cls._coalesce_matching(ret)

    @staticmethod
    @lru_cache(maxsize=2000)
    def _coalesce_matching(p: 'PlatformPath') -> 'PlatformPath':
        return p

    def __repr__(self) -> str:
        r = super().__repr__()
        return f"{self.__class__.__name__}({r})"


@dataclasses.dataclass(slots=True, frozen=True, repr=True, init=True)
class ParsedUrl:
    arg: '_PathKey'
    parsed: ParseResult

    __hash__ = None

    def __post_init__(self) -> None:
        assert type(self.arg) is _PathKey, self.arg
        assert '\\' not in self.arg._is_or_as_str, self.arg
        assert type(self.parsed) is ParseResult, self.parsed
        assert bool(self.parsed.scheme) and len(self.parsed.scheme) > 1, self.parsed

    def __str__(self) -> str:
        return self.arg._is_or_as_str


@dataclasses.dataclass(frozen=True, repr=True, init=True)
class _PathKey:
    __slots__ = ('value', '__dict__')
    value: str | pathlib.PathLike

    def __hash__(self) -> int:
        return id(self._value)
    def __eq__(self, other: Any) -> bool:
        return self is other
    def __ne__(self, other: Any) -> bool:
        return not self == other

    @cached_property
    def _is_or_as_str(self) -> str:
        if isinstance(self.value, str):
            return self.value
        return str(self.value)

    def _format_platform_path(self, **kwargs) -> PlatformPath:
        return PlatformPath(self._is_or_as_str, **kwargs)

    @cached_property
    def _is_or_as_url(self) -> ParseResult | None:
        s = self._is_or_as_str
        if '\\' in s:
            return None
        ret = urlparse(s)
        if bool(ret.scheme) and len(ret.scheme) > 1:
            return ret
        return None

    def format_url_or_platform_path(self) -> ParsedUrl | PlatformPath:
        parsed = self._is_or_as_url
        if parsed is not None:
            return ParsedUrl(self, parsed)
        return self._format_platform_path()


@dataclasses.dataclass(slots=True, frozen=True, eq=True, repr=True, init=True)
class _PlatformPath:
    arg: _PathKey
    value: str

    _normalized_mapping: ClassVar[dict[PlatformPath, list[_PathKey]]] = {}

    # def __post_init__


class _SimpleFileType(IntEnum):
    REG = stat.S_IFREG
    DIR = stat.S_IFDIR
    LNK = stat.S_IFLNK
    FIFO = stat.S_IFIFO
    SOCK = stat.S_IFSOCK
    CHR = stat.S_IFCHR
    UNKNOWN = stat.S_IFWHT

    @classmethod
    def classify(cls, res: os.stat_result) -> Self:
        mode = res.st_mode
        assert type(mode) is int, mode
        for candidate in cls:
            v = candidate.value
            if v == 0:
                continue
            if (mode & v) != 0:
                return candidate
        return cls.UNKNOWN


@dataclasses.dataclass(slots=True, frozen=True, eq=True, init=True)
class _Fd:
    fd: int

    def __post_init__(self) -> None:
        assert self.fd > 0, self

    def __del__(self) -> None:
        os.close(fd)

    @classmethod
    def open(cls, k: _PathKey, flags: int = os.O_PATH | os.O_NOFOLLOW, **kwargs) -> Self:
        if not isinstance(flags, int):
            raise TypeError(f"flags argument {flags!r} must be integer")
        platform_path = k._format_platform_path()
        fd = os.open(platform_path, flags, **kwargs)
        return cls(fd)

    def _stat(self) -> os.stat_result:
        return os.fstat(self.fd)

    @cached_property
    def _idempotent_fstat(self) -> os.stat_result:
        return self._stat()

    def _dev_inode_pair(self) -> tuple[int, int]:
        s = self._idempotent_fstat
        return (s.st_dev, s.st_ino)

    def filetype(self) -> _SimpleFileType:
        return _SimpleFileType.classify(self._idempotent_fstat)

    def user_executable_bit(self) -> bool:
        return (self._stat().st_mode & stat.S_IXUSR) != 0

    def __hash__(self) -> int:
        return hash(self._dev_inode_pair)
    def __eq__(self, other: Any) -> bool:
        if type(other) is not self.__class__:
            return NotImplemented
        return self._dev_inode_pair == other._dev_inode_pair
    def __ne__(self, other: Any) -> bool:
        if type(other) is not self.__class__:
            return NotImplemented
        return not self == other


def format_os_path(path: str, mode: int | Path = Path.unix) -> str:
    """Formats the input path to use consistent, platform specific separators.

    Absolute paths are converted between drive letters and a prepended ``/`` as per platform
    requirement.

    Parameters:
        path: the path to be normalized, must be a string or expose the replace method.
        mode: the path file separator style to normalize the passed path to.
            Default is unix style, i.e. ``/``
    """
    if not path:
        return path

    if not isinstance(mode, Path):
        mode = Path(mode)

    if mode == Path.windows:
        path = path.replace("/", "\\")
    else:
        path = path.replace("\\", "/")
    return path


def convert_to_posix_path(path: str | pathlib.PathLike) -> str:
    """Converts the input path to POSIX style."""
    return format_os_path(path, mode=Path.unix)
    # return _PathKey(path)._format_platform_path(mode=Path.unix)


def convert_to_platform_path(path: str | pathlib.PathLike) -> str:
    """Converts the input path to the current platform's native style."""
    return format_os_path(path, mode=Path.platform_path)
    # return _PathKey(path)._format_platform_path(mode=Path.platform_path)


def single_iterable[T](x: Iterable[T]) -> T:
    i = iter(x)
    try:
        ret = next(i)
    except StopIteration:
        raise ValueError(f"iterable input {x!r} had no elements: should have exactly one!")
    try:
        again = next(i)
    except StopIteration:
        return ret
    raise ValueError(f"iterable input {x!r} had more than one element "
                     "(had {ret!r}, then {again!r})\n"
                     "should have exactly one!")


def last_of_nonempty_iterable[T](x: Iterable[T]) -> T:
    i = iter(x)
    count: int = 0
    try:
        while True:
            last = next(i)
            count += 1
    except StopIteration:
        if count == 0:
            raise ValueError(f"iterable input {x!r} must have at least one element!")
        return cast(T, last)


def path_to_os_path(*parameters: str | pathlib.PathLike) -> Iterable[str]:
    """Takes an arbitrary number of positional parameters, converts each argument of type
    string to use a normalized filepath separator, and returns a list of all values.
    """
    return tuple(
        _PathKey(p).format_url_or_platform_path()
        for p in parameters
    )


def _system_path_filter(_func=None, arg_slice: Optional[slice] = None):
    """Filters function arguments to account for platform path separators.
    Optional slicing range can be specified to select specific arguments

    This decorator takes all (or a slice) of a method's positional arguments
    and normalizes usage of filepath separators on a per platform basis.

    Note: `**kwargs`, urls, and any type that is not a string are ignored
    so in such cases where path normalization is required, that should be
    handled by calling path_to_os_path directly as needed.

    Parameters:
        arg_slice: a slice object specifying the slice of arguments
            in the decorated method over which filepath separators are
            normalized
    """

    def holder_func(func):
        @functools.wraps(func)
        def path_filter_caller(*args, **kwargs):
            args = list(args)
            if arg_slice:
                args[arg_slice] = path_to_os_path(*args[arg_slice])
            else:
                args = path_to_os_path(*args)
            return func(*args, **kwargs)

        return path_filter_caller

    if _func:
        return holder_func(_func)
    return holder_func


def _noop_decorator(_func=None, arg_slice: Optional[slice] = None):
    return _func if _func else lambda x: x


if sys.platform == "win32":
    system_path_filter = _system_path_filter
else:
    system_path_filter = _noop_decorator


def sanitize_win_longpath(path: str) -> str:
    """Strip Windows extended path prefix from strings
    Returns sanitized string.
    no-op if extended path prefix is not present"""
    return path.lstrip("\\\\?\\")


# This is intended to be longer than the part of the install path
# spack generates from the root path we give it.  Included in the
# estimate:
#
#   os-arch      ->   30
#   compiler     ->   30
#   package name ->   50   (longest is currently 47 characters)
#   version      ->   20
#   hash         ->   32
#   buffer       ->  138
#  ---------------------
#   total        ->  300
SPACK_MAX_INSTALL_PATH_LENGTH = 300

#: Padded paths comprise directories with this name (or some prefix of it). :
#: It starts with two underscores to make it unlikely that prefix matches would
#: include some other component of the installation path.
SPACK_PATH_PADDING_CHARS = "__spack_path_placeholder__"

#: Bytes equivalent of SPACK_PATH_PADDING_CHARS.
SPACK_PATH_PADDING_BYTES = SPACK_PATH_PADDING_CHARS.encode("ascii")

#: Special padding char if the padded string would otherwise end with a path
#: separator (since the path separator would otherwise get collapsed out,
#: causing inconsistent padding).
SPACK_PATH_PADDING_EXTRA_CHAR = "_"


def win_exe_ext():
    return r"(?:\.bat|\.exe)"


def sanitize_filename(filename: str) -> str:
    """
    Replaces unsupported characters (for the host) in a filename with underscores.

    Criteria for legal files based on
    https://en.wikipedia.org/wiki/Filename#Comparison_of_filename_limitations

    Args:
        filename: string containing filename to be created on the host filesystem

    Return:
        filename that can be created on the host filesystem
    """
    if sys.platform != "win32":
        # Only disallow null bytes and directory separators.
        return re.sub("[\0/]", "_", filename)

    # On Windows, things are more involved.
    # NOTE: this is incomplete, missing reserved names
    return re.sub(r'[\x00-\x1F\x7F"*/:<>?\\|]', "_", filename)


@memoized
def get_system_path_max():
    # Choose a conservative default
    sys_max_path_length = 256
    if sys.platform == "win32":
        sys_max_path_length = 260
    else:
        try:
            path_max_proc = subprocess.Popen(
                ["getconf", "PATH_MAX", "/"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT
            )
            proc_output = str(path_max_proc.communicate()[0].decode())
            sys_max_path_length = int(proc_output)
        except (ValueError, subprocess.CalledProcessError, OSError):
            tty.msg(
                "Unable to find system max path length, using: {0}".format(sys_max_path_length)
            )

    return sys_max_path_length


def _get_padding_string(length):
    spack_path_padding_size = len(SPACK_PATH_PADDING_CHARS)
    num_reps = int(length / (spack_path_padding_size + 1))
    extra_chars = length % (spack_path_padding_size + 1)
    reps_list = [SPACK_PATH_PADDING_CHARS for i in range(num_reps)]
    reps_list.append(SPACK_PATH_PADDING_CHARS[:extra_chars])
    padding = os.path.sep.join(reps_list)
    if padding.endswith(os.path.sep):
        padding = padding[: len(padding) - 1] + SPACK_PATH_PADDING_EXTRA_CHAR
    return padding


def add_padding(path, length):
    """Add padding subdirectories to path until total is length characters

    Returns the padded path. If path is length - 1 or more characters long,
    returns path. If path is length - 1 characters, warns that it is not
    padding to length

    Assumes path does not have a trailing path separator"""
    padding_length = length - len(path)
    if padding_length == 1:
        # The only 1 character addition we can make to a path is `/`
        # Spack internally runs normpath, so `foo/` will be reduced to `foo`
        # Even if we removed this behavior from Spack, the user could normalize
        # the path, removing the additional `/`.
        # Because we can't expect one character of padding to show up in the
        # resulting binaries, we warn the user and do not pad by a single char
        tty.warn("Cannot pad path by exactly one character.")
    if padding_length <= 0:
        return path

    # we subtract 1 from the padding_length to account for the path separator
    # coming from os.path.join below
    padding = _get_padding_string(padding_length - 1)

    return os.path.join(path, padding)


def longest_prefix_re(string, capture=True):
    """Return a regular expression that matches a the longest possible prefix of string.

    i.e., if the input string is ``the_quick_brown_fox``, then::

        m = re.compile(longest_prefix('the_quick_brown_fox'))
        m.match('the_').group(1)                 == 'the_'
        m.match('the_quick').group(1)            == 'the_quick'
        m.match('the_quick_brown_fox').group(1)  == 'the_quick_brown_fox'
        m.match('the_xquick_brown_fox').group(1) == 'the_'
        m.match('the_quickx_brown_fox').group(1) == 'the_quick'

    """
    if len(string) < 2:
        return string

    return "(%s%s%s?)" % (
        "" if capture else "?:",
        string[0],
        longest_prefix_re(string[1:], capture=False),
    )


def _build_padding_re(as_bytes: bool = False):
    """Build and return a compiled regex for filtering path padding placeholders."""
    pad = re.escape(SPACK_PATH_PADDING_CHARS)
    extra = SPACK_PATH_PADDING_EXTRA_CHAR
    longest_prefix = longest_prefix_re(SPACK_PATH_PADDING_CHARS, capture=False)

    regex = (
        r"((?:/[^/\s]*)*?)"  # zero or more leading non-whitespace path components
        r"(?:/{pad})+"  # the padding string repeated one or more times
        # trailing prefix of padding as path component
        r"(?:/{longest_prefix}|/{longest_prefix}{extra})?(?=/)"
    )
    regex = regex.replace("/", re.escape(os.sep))
    regex = regex.format(pad=pad, extra=extra, longest_prefix=longest_prefix)

    if as_bytes:
        return re.compile(regex.encode("ascii"))
    else:
        return re.compile(regex)


class _PaddingFilter:
    """Callable that filters path-padding placeholders from a string or bytes buffer.

    This turns paths like this:

        /foo/bar/__spack_path_placeholder__/__spack_path_placeholder__/...

    Into paths like this:

        /foo/bar/[padded-to-512-chars]/...

    Where ``padded-to-512-chars`` indicates that the prefix was padded with
    placeholders until it hit 512 characters. The actual value of this number
    depends on what the ``install_tree``'s ``padded_length`` is configured to.

    For a path to match and be filtered, the placeholder must appear in its
    entirety at least one time. e.g., "/spack/" would not be filtered, but
    "/__spack_path_placeholder__/spack/" would be.

    Note that only the first padded path in the string is filtered.
    """

    __slots__ = ("_re", "_needle", "_fmt")

    def __init__(self, as_bytes: bool = False) -> None:
        self._re = _build_padding_re(as_bytes=as_bytes)
        if as_bytes:
            self._needle: Union[str, bytes] = SPACK_PATH_PADDING_BYTES
            self._fmt: Union[str, bytes] = b"%b" + os.sep.encode("ascii") + b"[padded-to-%d-chars]"
        else:
            self._needle = SPACK_PATH_PADDING_CHARS
            self._fmt = "%s" + os.sep + "[padded-to-%d-chars]"

    def _replace(self, match):
        return self._fmt % (match.group(1), len(match.group(0)))

    def __call__(self, data):
        if self._needle not in data:
            return data
        return self._re.sub(self._replace, data)


#: Callable that filters path-padding placeholders from strings
padding_filter = _PaddingFilter(as_bytes=False)

#: Callable that filters path-padding placeholders from bytes buffers
padding_filter_bytes = _PaddingFilter(as_bytes=True)


@contextlib.contextmanager
def filter_padding():
    """Context manager to safely disable path padding in all Spack output.

    This is needed because Spack's debug output gets extremely long when we use a
    long padded installation path.
    """
    # circular import
    import spack.config

    padding = spack.config.get("config:install_tree:padded_length", None)
    if padding:
        # filter out all padding from the install command output
        with tty.output_filter(padding_filter):
            yield
    else:
        yield  # no-op: don't filter unless padding is actually enabled


def debug_padded_filter(string, level=1):
    """
    Return string, path padding filtered if debug level and not windows

    Args:
        string (str): string containing path
        level (int): maximum debug level value for filtering (e.g., 1
            means filter path padding if the current debug level is 0 or 1
            but return the original string if it is 2 or more)

    Returns (str): filtered string if current debug level does not exceed
        level and not windows; otherwise, unfiltered string
    """
    if sys.platform == "win32":
        return string

    return padding_filter(string) if tty.debug_level() <= level else string
