# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

"""
This module implements Version and version-ish objects.  These are:

Version
  A single version of a package.
VersionRange
  A range of versions of a package.
VersionList
  A list of Versions and VersionRanges.

All of these types support the following operations, which can
be called on any of the types::

  __eq__, __ne__, __lt__, __gt__, __ge__, __le__, __hash__
  __contains__
  satisfies
  overlaps
  union
  intersection
  concrete
"""
import re
import numbers
from abc import ABCMeta, abstractmethod, abstractproperty
from bisect import bisect_left
from functools import wraps
from typing import (Any, ClassVar, Dict, FrozenSet, Generic, Iterable,      # novm
                    Iterator, List, Optional, Tuple, Type, TypeVar, Union,  # novm
                    overload)                                               # novm

from six import add_metaclass, string_types

from llnl.util.lang import memoized

import spack.error
from spack.util.spack_yaml import syaml_dict


__all__ = ['Version', 'VersionRange', 'VersionList', 'ver']

# Valid version characters
VALID_VERSION = re.compile(r'^[A-Za-z0-9_\-]+$')

# regex for version segments
SEGMENT_REGEX = re.compile(r'(?:(?P<num>[0-9]+)|(?P<str>[a-zA-Z]+))(?P<sep>[_.-]*)')

# Infinity-like versions. The order in the list implies the comparison rules
infinity_versions = ['develop', 'main', 'master', 'head', 'trunk']

iv_min_len = min(len(s) for s in infinity_versions)


def coerce_versions(a, b):
    # type: (Any, Any) -> Tuple[VersionPredicate, VersionPredicate]
    """
    Convert both a and b to the 'greatest' type between them, in this order:
           Version < VersionRange < VersionList
    This is used to simplify comparison operations below so that we're always
    comparing things that are of the same type.
    """
    order = (Version, VersionRange, VersionList)
    ta, tb = type(a), type(b)

    def check_type(t):
        # type: (Type) -> None
        if t not in order:
            raise TypeError(
                "coerce_versions cannot be called on {0}: need one of {1}"
                .format(t, order))
    check_type(ta)
    check_type(tb)

    if ta == tb:
        return (a, b)
    elif order.index(ta) > order.index(tb):
        if ta == VersionRange:
            return (a, VersionRange.from_single_version(b))
        else:
            return (a, VersionList.from_version_or_range(b))
    else:
        if tb == VersionRange:
            return (VersionRange.from_single_version(a), b)
        else:
            return (VersionList.from_version_or_range(a), b)


def coerced(method):
    """Decorator that ensures that argument types of a method are coerced."""
    @wraps(method)
    def coercing_method(a, b, *args, **kwargs):
        if type(a) == type(b) or a is None or b is None:
            return method(a, b, *args, **kwargs)
        else:
            ca, cb = coerce_versions(a, b)
            return getattr(ca, method.__name__)(cb, *args, **kwargs)
    return coercing_method


class VersionStrComponent(object):
    # NOTE: this is intentionally not a UserString, the abc instanceof
    #       check is slow enough to eliminate all gains
    __slots__ = ['inf_ver', 'data']

    def __init__(self, string):
        self.inf_ver = None
        self.data = string
        if len(string) >= iv_min_len:
            try:
                self.inf_ver = infinity_versions.index(string)
            except ValueError:
                pass

    def __hash__(self):
        return hash(self.data)

    def __str__(self):
        return self.data

    def __eq__(self, other):
        if isinstance(other, VersionStrComponent):
            return self.data == other.data
        return self.data == other

    def __lt__(self, other):
        if isinstance(other, VersionStrComponent):
            if self.inf_ver is not None:
                if other.inf_ver is not None:
                    return self.inf_ver > other.inf_ver
                return False
            if other.inf_ver is not None:
                return True

            return self.data < other.data

        if self.inf_ver is not None:
            return False

        # Numbers are always "newer" than letters.
        # This is for consistency with RPM.  See patch
        # #60884 (and details) from bugzilla #50977 in
        # the RPM project at rpm.org.  Or look at
        # rpmvercmp.c if you want to see how this is
        # implemented there.
        if isinstance(other, int):
            return True

        if isinstance(other, str):
            return self < VersionStrComponent(other)
        # If we get here, it's an unsupported comparison

        raise ValueError("VersionStrComponent can only be compared with itself, "
                         "int and str")

    def __gt__(self, other):
        return not self.__lt__(other)


V = TypeVar('V', bound='VersionPredicate')


@add_metaclass(ABCMeta)
class VersionPredicate(Generic[V]):

    @classmethod
    @abstractmethod
    def parse(cls, string):
        # type: (str) -> VersionPredicate
        pass

    @abstractmethod
    def lowest(self):
        # type: () -> Optional[Version]
        pass

    @abstractmethod
    def highest(self):
        # type: () -> Optional[Version]
        pass

    @abstractmethod
    def satisfies(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def __contains__(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def overlaps(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def union(self, other):
        # type: (V) -> VersionPredicate
        pass

    @abstractmethod
    def intersection(self, other):
        # type: (V) -> VersionPredicate
        pass

    @abstractproperty
    def concrete(self):
        # type: () -> Optional[Version]
        pass

    @abstractmethod
    def __lt__(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def __le__(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def __gt__(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def __ge__(self, other):
        # type: (V) -> bool
        pass

    @abstractmethod
    def __eq__(self, other):
        # type: (Any) -> bool
        pass

    @abstractmethod
    def __ne__(self, other):
        # type: (Any) -> bool
        pass

    @abstractmethod
    def __hash__(self):
        # type: () -> int
        pass


class Version(VersionPredicate['Version']):
    """Class to represent versions"""
    __slots__ = ['version', 'separators', 'string']
    string = None               # type: str
    version = None              # type: Tuple[Union[str, int], ...]
    separators = None           # type: Tuple[str, ...]

    @classmethod
    def parse(cls, string):
        # type: (str) -> Version
        return cls(string)

    def __init__(self, string):
        # type: (Any) -> None
        if not isinstance(string, str):
            string = str(string)

        # preserve the original string, but trimmed.
        string = string.strip()
        self.string = string

        if not VALID_VERSION.match(string):
            raise ValueError("Bad characters in version string: %s" % string)

        # Split version into alphabetical and numeric segments simultaneously
        segments = SEGMENT_REGEX.findall(string)
        self.version = tuple(
            int(m[0]) if m[0] else VersionStrComponent(m[1]) for m in segments
        )
        self.separators = tuple(m[2] for m in segments)

    @property
    def dotted(self):
        # type: () -> Version
        """The dotted representation of the version.

        Example:
        >>> version = Version('1-2-3b')
        >>> version.dotted
        Version('1.2.3b')

        Returns:
            Version: The version with separator characters replaced by dots
        """
        return Version(self.string.replace('-', '.').replace('_', '.'))

    @property
    def underscored(self):
        # type: () -> Version
        """The underscored representation of the version.

        Example:
        >>> version = Version('1.2.3b')
        >>> version.underscored
        Version('1_2_3b')

        Returns:
            Version: The version with separator characters replaced by
                underscores
        """
        return Version(self.string.replace('.', '_').replace('-', '_'))

    @property
    def dashed(self):
        # type: () -> Version
        """The dashed representation of the version.

        Example:
        >>> version = Version('1.2.3b')
        >>> version.dashed
        Version('1-2-3b')

        Returns:
            Version: The version with separator characters replaced by dashes
        """
        return Version(self.string.replace('.', '-').replace('_', '-'))

    @property
    def joined(self):
        # type: () -> Version
        """The joined representation of the version.

        Example:
        >>> version = Version('1.2.3b')
        >>> version.joined
        Version('123b')

        Returns:
            Version: The version with separator characters removed
        """
        return Version(
            self.string.replace('.', '').replace('-', '').replace('_', ''))

    def up_to(self, index):
        # type: (int) -> Version
        """The version up to the specified component.

        Examples:
        >>> version = Version('1.23-4b')
        >>> version.up_to(1)
        Version('1')
        >>> version.up_to(2)
        Version('1.23')
        >>> version.up_to(3)
        Version('1.23-4')
        >>> version.up_to(4)
        Version('1.23-4b')
        >>> version.up_to(-1)
        Version('1.23-4')
        >>> version.up_to(-2)
        Version('1.23')
        >>> version.up_to(-3)
        Version('1')

        Returns:
            Version: The first index components of the version
        """
        return self[:index]

    def lowest(self):
        # type: () -> Version
        return self

    def highest(self):
        # type: () -> Version
        return self

    def isdevelop(self):
        # type: () -> bool
        """Triggers on the special case of the `@develop-like` version."""
        for inf in infinity_versions:
            for v in self.version:
                if v == inf:
                    return True

        return False

    @coerced
    def satisfies(self, other):
        # type: (Version) -> bool
        """A Version 'satisfies' another if it is at least as specific and has
        a common prefix.  e.g., we want gcc@4.7.3 to satisfy a request for
        gcc@4.7 so that when a user asks to build with gcc@4.7, we can find
        a suitable compiler.
        """

        nself = len(self.version)
        nother = len(other.version)
        return nother <= nself and self.version[:nother] == other.version

    def __iter__(self):
        # type: () -> Iterator[Union[str, int]]
        return iter(self.version)

    def __len__(self):
        # type: () -> int
        return len(self.version)

    @overload
    def __getitem__(self, idx):
        # type: (int) -> Union[int, str]
        pass

    @overload
    def __getitem__(self, idx):
        # type: (slice) -> Version
        pass

    def __getitem__(self, idx):
        # type: (Union[int, slice]) -> Union[Union[int, str], Version]
        cls = type(self)

        if isinstance(idx, numbers.Integral):
            return self.version[idx]

        elif isinstance(idx, slice):
            string_arg = []

            pairs = zip(self.version[idx], self.separators[idx])
            for token, sep in pairs:
                string_arg.append(str(token))
                string_arg.append(str(sep))

            string_arg.pop()  # We don't need the last separator
            return cls(''.join(string_arg))

        message = '{cls.__name__} indices must be integers'
        raise TypeError(message.format(cls=cls))

    def __repr__(self):
        # type: () -> str
        return 'Version.parse({0!r})'.format(self.string)

    def __str__(self):
        # type: () -> str
        return self.string

    def __format__(self, format_spec):
        # type: (str) -> str
        return self.string.format(format_spec)

    @property
    def concrete(self):
        # type: () -> Version
        return self

    @coerced
    def __lt__(self, other):
        # type: (Version) -> bool
        """Version comparison is designed for consistency with the way RPM
           does things.  If you need more complicated versions in installed
           packages, you should override your package's version string to
           express it more sensibly.
        """
        if other is None:
            return False

        # Use tuple comparison assisted by VersionStrComponent for performance
        return self.version < other.version

    @coerced
    def __eq__(self, other):
        # type: (Any) -> bool
        return (other is not None and
                type(other) == Version and self.version == other.version)

    @coerced
    def __ne__(self, other):
        # type: (Any) -> bool
        return not (self == other)

    @coerced
    def __le__(self, other):
        # type: (Version) -> bool
        return self == other or self < other

    @coerced
    def __ge__(self, other):
        # type: (Version) -> bool
        return not (self < other)

    @coerced
    def __gt__(self, other):
        # type: (Version) -> bool
        return not (self == other) and not (self < other)

    def __hash__(self):
        # type: () -> int
        return hash(self.version)

    @coerced
    def __contains__(self, other):
        # type: (Version) -> bool
        if other is None:
            return False
        return other.satisfies(self)

    def is_predecessor(self, other):
        # type: (Version) -> bool
        """True if the other version is the immediate predecessor of this one.
           That is, NO versions v exist such that:
           (self < v < other and v not in self).
        """
        if len(self.version) != len(other.version):
            return False

        sl = self.version[-1]
        ol = other.version[-1]
        return (type(sl) == int and
                type(ol) == int and
                (ol - sl == 1))  # type: ignore[operator]

    def is_successor(self, other):
        # type: (Version) -> bool
        return other.is_predecessor(self)

    @coerced
    def overlaps(self, other):
        # type: (Version) -> bool
        return self in other or other in self

    @coerced
    def union(self, other):
        # type: (Version) -> VersionPredicate
        if self == other or other in self:
            return self
        elif self in other:
            return other
        else:
            return VersionList([self, other])

    @coerced
    def intersection(self, other):
        # type: (Version) -> VersionPredicate
        if self in other:  # also covers `self == other`
            return self
        elif other in self:
            return other
        else:
            return VersionList()


def _endpoint_only(fun):
    """We want to avoid logic that handles any type of version range, just endpoints."""
    @wraps(fun)
    def validate_endpoint_argument(self, other):
        assert isinstance(other, _VersionEndpoint), (
            "required two _VersionEndpoint arguments, received {0} and {1}"
            .format(self, other))
        return fun(self, other)
    return validate_endpoint_argument


class _VersionEndpoint(object):
    value = None                                            # type: Optional[Version]
    location = None                                         # type: str
    _negated = None                                         # type: bool

    _valid_endpoint_locations = frozenset([
        'left', 'right',
    ])                                                  # type: ClassVar[FrozenSet[str]]

    @classmethod
    def wildcard(cls, location):
        # type: (str) -> _VersionEndpoint
        return cls(value=None, location=location, negated=False)

    @property
    def is_wildcard(self):
        # type: () -> bool
        return self.value is None

    @property
    def polarity(self):
        # type: () -> bool
        return not self._negated

    def __init__(self, value, location, negated=False):
        # type: (Optional[Version], str, bool) -> None
        assert value is None or isinstance(value, Version), value
        assert location in self._valid_endpoint_locations, location

        self.value = value
        self.location = location
        self._negated = negated

    def __repr__(self):
        # type: () -> str
        return ("_VersionEndpoint(value={0!r}, location={1!r}, negated={2!r})"
                .format(self.value, self.location, self._negated))

    def __str__(self):
        # type: () -> str
        ver_str = '*' if self.is_wildcard else str(self.value)
        polarity = '+' if self.polarity else '-'
        locator = '<' if self.location == 'left' else '>'
        return '{0}{1}{2}'.format(ver_str, polarity, locator)

    def __hash__(self):
        # type: () -> int
        return hash((self.value, self.location))

    def __contains__(self, other):
        # type: (_VersionEndpoint) -> bool
        # return not (other < self or other > self)
        if self.value is None:
            return True
        if other.value is None:
            return False
        polarities_match = self.polarity == other.polarity
        if self.location == 'right':
            if other.location == 'left':
                return other.value < self.value or other.value in self.value
            if other.value in self.value:
                return polarities_match
            return other.value < self.value
        assert self.location == 'left', self
        if other.location == 'right':
            return other.value > self.value or other.value in self.value
        if other.value in self.value:
            return polarities_match
        return other.value > self.value

    def satisfies(self, other):
        # type: (_VersionEndpoint) -> bool
        return self in other

    def lowest(self):
        # type: () -> Optional[Version]
        if self.location == 'left':
            if self.value is None:
                return None
            return self.value.lowest()
        return None

    def highest(self):
        # type: () -> Optional[Version]
        if self.location == 'right':
            if self.value is None:
                return None
            return self.value.highest()
        return None

    def __eq__(self, other):
        # type: (Any) -> bool
        if not isinstance(other, _VersionEndpoint):
            return NotImplemented
        return (self.value == other.value and
                self.location == other.location and
                self.polarity == other.polarity)

    # TODO: consider @memoized since we impl __hash__?
    @_endpoint_only
    def __lt__(self, other):
        # type: (_VersionEndpoint) -> bool
        # assert not (
        #     self.location == 'right' or other.location == 'right'), (self, other)
        # assert self.location == other.location, (self, other)
        if self.value is None:
            return True
        if other.value is None:
            return False
        if self.location == other.location:
            if self.value == other.value:
                if self.polarity and not other.polarity:
                    return False if self.location == 'right' else True
                if other.polarity and not self.polarity:
                    return True if self.location == 'right' else False
        return self.value < other.value

    @_endpoint_only
    def __gt__(self, other):
        # type: (_VersionEndpoint) -> bool
        # assert not (
        #     self.location == 'left' or other.location == 'left'), (self, other)
        # assert self.location == other.location, (self, other)
        if self.value is None:
            return True
        if other.value is None:
            return False
        if self.location == other.location:
            if self.value == other.value:
                if self.polarity and not other.polarity:
                    return False if self.location == 'left' else True
                if other.polarity and not self.polarity:
                    return True if self.location == 'left' else False
        return self.value > other.value

    def __ne__(self, other):
        # type: (Any) -> bool
        if not isinstance(other, _VersionEndpoint):
            return NotImplemented
        return not (self == other)

    @_endpoint_only
    def __le__(self, other):
        # type: (_VersionEndpoint) -> bool
        return self == other or self < other

    @_endpoint_only
    def __ge__(self, other):
        # type: (_VersionEndpoint) -> bool
        return self == other or self < other


class _EndpointContainment(object):
    low_contained = None          # type: bool
    high_contained = None         # type: bool

    def __init__(
            self,
            self_low,                                       # type: _VersionEndpoint
            self_high,                                      # type: _VersionEndpoint
            other_low,                                      # type: _VersionEndpoint
            other_high,                                     # type: _VersionEndpoint
    ):
        # type: (...) -> None
        assert isinstance(self_low, _VersionEndpoint) and self_low.location == 'left'
        assert isinstance(self_high, _VersionEndpoint) and self_high.location == 'right'
        assert isinstance(other_low, _VersionEndpoint) and other_low.location == 'left'
        assert (isinstance(other_high, _VersionEndpoint) and
                other_high.location == 'right')
        self.low_contained = ((other_low in self_low) and (other_low in self_high))
        self.high_contained = ((other_high in self_low) and (other_high in self_low))
        # import pdb; pdb.set_trace()


class VersionRange(VersionPredicate['VersionRange']):
    start = None  # type: _VersionEndpoint
    end = None    # type: _VersionEndpoint

    @classmethod
    def from_single_version(cls, version):
        # type: (Version) -> VersionRange
        return cls(start=_VersionEndpoint(version, 'left'),
                   end=_VersionEndpoint(version, 'right'))

    @classmethod
    def parse(cls, string):
        # type: (str) -> VersionRange
        if string.startswith(':'):
            if string.startswith(':!'):
                if string.endswith('!:'):
                    # :!<x>!:
                    version = Version.parse(string[2:-2])
                    return VersionRange(
                        start=_VersionEndpoint(version, 'left', negated=True),
                        end=_VersionEndpoint(version, 'right', negated=True),
                    )
                assert not string.endswith(':'), string
                # :!<x>
                version = Version.parse(string[2:])
                return VersionRange(
                    start=_VersionEndpoint.wildcard('left'),
                    end=_VersionEndpoint(version, 'right', negated=True))
            if string.endswith(':'):
                # :
                # We ban :!<x>: and :<x>:.
                assert string == ':', string
                return VersionRange(
                    start=_VersionEndpoint.wildcard('left'),
                    end=_VersionEndpoint.wildcard('right'))
            # :<x>
            version = Version.parse(string[1:])
            return VersionRange(
                start=_VersionEndpoint.wildcard('left'),
                end=_VersionEndpoint(version, 'right'))
        if string.endswith(':'):
            if string.endswith('!:'):
                # <x>!:
                version = Version.parse(string[:-2])
                return VersionRange(
                    start=_VersionEndpoint(version, 'left', negated=True),
                    end=_VersionEndpoint.wildcard('right'))
            # <x>:
            version = Version.parse(string[:-1])
            return VersionRange(
                start=_VersionEndpoint(version, 'left'),
                end=_VersionEndpoint.wildcard('right'))
        if ':' in string:
            # <x>:<x> | <x>!:<x> | <x>:!<x> | <x>!:!<x>
            start_version, end_version = tuple(string.split(':'))
            if start_version.endswith('!'):
                start = _VersionEndpoint(Version.parse(start_version[:-1]), 'left',
                                         negated=True)
            else:
                start = _VersionEndpoint(Version.parse(start_version), 'left')
            if end_version.startswith('!'):
                end = _VersionEndpoint(Version.parse(end_version[1:]), 'right',
                                       negated=True)
            else:
                end = _VersionEndpoint(Version.parse(end_version), 'right')
            return VersionRange(start=start, end=end)
        # <x>
        version = Version.parse(string)
        return VersionRange.from_single_version(version)

    def __init__(self, start, end):
        # type: (_VersionEndpoint, _VersionEndpoint) -> None
        if (start.location != 'left') or (end.location != 'right') or (
                not start.is_wildcard and not end.is_wildcard and end < start):
            raise ValueError("Invalid Version range with start {0} and end {1}"
                             .format(start, end))
        self.start = start
        self.end = end

    @memoized
    def _endpoint_containment(self, other):
        # type: (VersionRange) -> _EndpointContainment
        return _EndpointContainment(
            self_low=self.start,
            self_high=self.end,
            other_low=other.start,
            other_high=other.end,
        )

    def lowest(self):
        # type: () -> Optional[Version]
        return self.start.value

    def highest(self):
        # type: () -> Optional[Version]
        return self.end.value

    @coerced
    def __lt__(self, other):
        # type: (VersionRange) -> bool
        """Sort VersionRanges lexicographically so that they are ordered first
           by start and then by end.  None denotes an open range, so None in
           the start position is less than everything except None, and None in
           the end position is greater than everything but None.
        """
        if other is None:
            return False

        s, o = self, other
        if s.start < o.start:
            return True
        if s.start > o.start:
            return False
        return s.end < o.end

    @coerced
    def __eq__(self, other):
        # type: (Any) -> bool
        return (other is not None and
                type(other) == VersionRange and
                self.start == other.start and self.end == other.end)

    @coerced
    def __ne__(self, other):
        # type: (Any) -> bool
        return not (self == other)

    @coerced
    def __le__(self, other):
        # type: (VersionRange) -> bool
        return self == other or self < other

    @coerced
    def __ge__(self, other):
        # type: (VersionRange) -> bool
        return not (self < other)

    @coerced
    def __gt__(self, other):
        # type: (VersionRange) -> bool
        # if other is None:
        #     return False

        # s, o = self, other
        # if s.start > o.start:
        #     return True
        # return s.end > o.end
        return not (self == other) and not (self < other)

    @property
    def concrete(self):
        # type: () -> Optional[Version]
        if (self.start == self.end and
            self.start.value is not None and
            self.end.value is not None):
            return self.start.value
        return None

    @coerced
    def __contains__(self, other):
        # type: (VersionRange) -> bool
        if other is None:
            return False

        in_lower = (other.start in self.start and
                    other.end in self.start)
        # in_lower = ((self.start == other.start) or
        #             self.start.value is None or
        #             (other.start.value is not None and (
        #                 (self.start < other.start) or
        #                 other.start in self.start)))
        if not in_lower:
            return False

        in_upper = (other.start in self.end and
                    other.end in self.end)
        # in_upper = ((self.end == other.end) or
        #             self.end.value is None or
        #             (other.end.value is not None and (
        #                 (self.end > other.end) or
        #                 other.end in self.end)))
        return in_upper

    @coerced
    def satisfies(self, other):
        # type: (VersionRange) -> bool
        """A VersionRange satisfies another if some version in this range
        would satisfy some version in the other range.  To do this it must
        either:

        a) Overlap with the other range
        b) The start of this range satisfies the end of the other range.

        This is essentially the same as overlaps(), but overlaps assumes
        that its arguments are specific.  That is, 4.7 is interpreted as
        4.7.0.0.0.0... .  This function assumes that 4.7 would be satisfied
        by 4.7.3.5, etc.

        Rationale:

        If a user asks for gcc@4.5:4.7, and a package is only compatible with
        gcc@4.7.3:4.8, then that package should be able to build under the
        constraints.  Just using overlaps() would not work here.

        Note that we don't need to check whether the end of this range
        would satisfy the start of the other range, because overlaps()
        already covers that case.

        Note further that overlaps() is a symmetric operation, while
        satisfies() is not.
        """
        return self in other
        # return (self.overlaps(other) or
        #         # if either self.start or other.end are None, then this can't
        #         # satisfy, or overlaps() would've taken care of it.
        #         not self.start.is_wildcard and
        #         not other.end.is_wildcard and
        #         self.start.satisfies(other.end))

    @coerced
    def overlaps(self, other):
        # type: (VersionRange) -> bool
        # containment = self._endpoint_containment(other)
        # return containment.low_contained or containment.high_contained
        return ((self.start <= other.end or
                 other.end in self.start or self.start in other.end) and
                (other.start <= self.end or
                 other.start in self.end or self.end in other.start))

    @coerced
    def union(self, other):
        # type: (VersionRange) -> VersionPredicate
        if not self.overlaps(other):
            if (self.end.value is not None and other.start.value is not None and
                self.end.value.is_predecessor(other.start.value)):
                return VersionRange(self.start, other.end)

            if (other.end.value is not None and self.start.value is not None and
                other.end.value.is_predecessor(self.start.value)):
                return VersionRange(other.start, self.end)

            return VersionList([self, other])

        # if we're here, then we know the ranges overlap.
        if self.start.is_wildcard or other.start.is_wildcard:
            start = _VersionEndpoint.wildcard('left')
        else:
            start = self.start
            # TODO: See note in intersection() about < and in discrepancy.
            if self.start in other.start or other.start < self.start:
                start = other.start

        if self.end.is_wildcard or other.end.is_wildcard:
            end = _VersionEndpoint.wildcard('right')
        else:
            end = self.end
            # TODO: See note in intersection() about < and in discrepancy.
            if other.end not in self.end:
                if end in other.end or other.end > self.end:
                    end = other.end

        return VersionRange(start, end)

    @coerced
    def intersection(self, other):
        # type: (VersionRange) -> VersionPredicate
        import pdb; pdb.set_trace()

        if self.overlaps(other):
            if self.start.is_wildcard:
                start = other.start
            else:
                start = self.start
                if not other.start.is_wildcard:
                    if other.start > start or other.start in start:
                        start = other.start

            if self.end.is_wildcard:
                end = other.end
            else:
                end = self.end
                # TODO: does this make sense?
                # This is tricky:
                #     1.6.5 in 1.6 = True  (1.6.5 is more specific)
                #     1.6 < 1.6.5  = True  (lexicographic)
                # Should 1.6 NOT be less than 1.6.5?  Hmm.
                # Here we test (not end in other.end) first to avoid paradox.
                if not other.end.is_wildcard and end not in other.end:
                    if other.end < end or other.end in end:
                        end = other.end

            if start in end and not start < end:
                return start.value
            if end in start and not end > start:
                return end.value

            return VersionRange(start, end)

        return VersionList.empty()

    def __hash__(self):
        # type: () -> int
        return hash((self.start, self.end))

    def __repr__(self):
        # type: () -> str
        return 'VersionRange.parse({0!r})'.format(str(self))

    def __str__(self):
        # type: () -> str
        # ( :!<x>!: | <x> | : )
        if self.start.value == self.end.value:
            if self.start.value is None or self.end.value is None:
                assert self.start.value is None and self.end.value is None, self.end
                assert self.start.polarity and self.end.polarity, (self.start, self.end)
                # :
                return ':'
            if self.start.polarity or self.end.polarity:
                assert self.start.polarity and self.end.polarity, (self.start, self.end)
                # <x>
                return str(self.start.value)
            assert not self.start.polarity and not self.end.polarity, (
                self.start, self.end)
            # :!<x>!:
            return ':!{0}!:'.format(self.start.value)
        # ( :!<x> | :<x> )
        if self.start.value is None:
            # Checked that self.start == self.end above.
            assert self.end.value is not None, self.end
            assert self.start.polarity, self
            # :<x>
            if self.end.polarity:
                return ':{0}'.format(self.end.value)
            # :!<x>
            return ':!{0}'.format(self.end.value)
        # ( <x>: | <x>!: )
        if self.end.value is None:
            assert self.start.value is not None, self.start
            assert self.end.polarity, self
            # <x>:
            if self.start.polarity:
                return '{0}:'.format(self.start.value)
            # <x>!:
            return '{0}!:'.format(self.start.value)
        # {0}!:!{1} => {0} < x < {1}
        if (not self.start.polarity and
            not self.end.polarity):
            return '{0}!:!{1}'.format(self.start.value, self.end.value)
        # {0}:!{1} => {0} <= x < {1}
        if not self.end.polarity:
            return '{0}:!{1}'.format(self.start.value, self.end.value)
        # {0}!:{1} => {0} < x <= {1}
        if not self.start.polarity:
            return '{0}!:{1}'.format(self.start.value, self.end.value)
        # {0}:{1} => {0} <= x <= {1}
        assert self.start.polarity and self.end.polarity
        return "{0}:{1}".format(self.start.value, self.end.value)


_VlistType = Optional[
    'Union[str, VersionPredicate, Iterable[Union[str, VersionPredicate]]]'
]


class VersionList(VersionPredicate['VersionList']):
    """Sorted, non-redundant list of Versions and VersionRanges."""
    versions = None  # type: List[Union[Version, VersionRange]]

    @classmethod
    def from_version_or_range(cls, version_or_range):
        # type: (Union[Version, VersionRange]) -> VersionList
        return cls([version_or_range])

    @classmethod
    def empty(cls):
        # type: () -> VersionList
        return cls(vlist=None)

    @classmethod
    def parse(cls, string):
        # type: (str) -> VersionList

        def parse_version_or_range(el):
            # type: (str) -> Union[Version, VersionRange]
            if ':' in el:
                return VersionRange.parse(el)
            return Version.parse(el)
        if ',' in string:
            elements = string.split(',')
            versions_or_ranges = [parse_version_or_range(el) for el in elements]
            return cls(versions_or_ranges)
        if string:
            return cls.from_version_or_range(parse_version_or_range(string))
        return cls.empty()

    def __init__(self, vlist=None):
        # type: (_VlistType) -> None
        self.versions = []
        if vlist is not None:
            if isinstance(vlist, string_types):
                vlist = _string_to_version(vlist)
                if isinstance(vlist, VersionList):
                    self.versions = vlist.versions
                else:
                    assert isinstance(vlist, (Version, VersionRange)), vlist
                    self.versions = [vlist]
            else:
                vlist = list(vlist)  # type: ignore[arg-type]
                for v in vlist:
                    self.add(ver(v))

    def add(self, version):
        # type: (VersionPredicate) -> None
        if isinstance(version, (Version, VersionRange)):
            # This normalizes single-value version ranges.
            if version.concrete:
                version = version.concrete

            i = bisect_left(list(self), version)

            while i - 1 >= 0 and version.overlaps(self[i - 1]):
                version = version.union(self[i - 1])
                del self.versions[i - 1]
                i -= 1

            while i < len(self) and version.overlaps(self[i]):
                version = version.union(self[i])
                del self.versions[i]

            assert isinstance(version, (Version, VersionRange)), version
            self.versions.insert(i, version)

        elif isinstance(version, VersionList):
            for v in version:
                self.add(v)

        else:
            raise TypeError("Can't add %s to VersionList" % type(version))

    @property
    def concrete(self):
        # type: () -> Optional[Version]
        if len(self) == 1:
            return self[0].concrete
        else:
            return None

    def copy(self):
        # type: () -> VersionList
        return VersionList(self)

    def lowest(self):
        # type: () -> Optional[Version]
        """Get the lowest version in the list."""
        if not self:
            return None
        else:
            return self[0].lowest()

    def highest(self):
        # type: () -> Optional[Version]
        """Get the highest version in the list."""
        if not self:
            return None
        else:
            return self[-1].highest()

    def highest_numeric(self):
        # type: () -> Optional[Version]
        """Get the highest numeric version in the list."""
        numeric_versions = list(filter(
            lambda v: str(v) not in infinity_versions,
            self.versions))  # type: List[VersionPredicate]
        if not any(numeric_versions):
            return None
        else:
            return numeric_versions[-1].highest()

    def preferred(self):
        # type: () -> Version
        """Get the preferred (latest) version in the list."""
        latest = self.highest_numeric()
        if latest is None:
            latest = self.highest()
        assert latest is not None
        return latest

    @coerced
    def overlaps(self, other):
        # type: (VersionList) -> bool
        if not other or not self:
            return False

        s = o = 0
        while s < len(self) and o < len(other):
            if self[s].overlaps(other[o]):
                return True
            elif self[s] < other[o]:
                s += 1
            else:
                o += 1
        return False

    def to_dict(self):
        # type: () -> Dict[str, Union[str, Iterable[str]]]
        """Generate human-readable dict for YAML."""
        if self.concrete:
            return syaml_dict([
                ('version', str(self[0]))
            ])
        else:
            return syaml_dict([
                ('versions', [str(v) for v in self])
            ])

    @staticmethod
    def from_dict(dictionary):
        # type: (Dict[str, Union[str, Iterable[str]]]) -> VersionList
        """Parse dict from to_dict."""
        if 'versions' in dictionary:
            return VersionList(dictionary['versions'])
        elif 'version' in dictionary:
            return VersionList([dictionary['version']])  # type: ignore[list-item]
        else:
            raise ValueError("Dict must have 'version' or 'versions' in it.")

    @coerced
    def satisfies(self, other, strict=False):
        # type: (VersionList, bool) -> bool
        """A VersionList satisfies another if some version in the list
           would satisfy some version in the other list.  This uses
           essentially the same algorithm as overlaps() does for
           VersionList, but it calls satisfies() on member Versions
           and VersionRanges.

           If strict is specified, this version list must lie entirely
           *within* the other in order to satisfy it.
        """
        if not other or not self:
            return False

        if strict:
            return self in other

        s = o = 0
        while s < len(self) and o < len(other):
            if self[s].satisfies(other[o]):
                return True
            elif self[s] < other[o]:
                s += 1
            else:
                o += 1
        return False

    @coerced
    def update(self, other):
        # type: (VersionList) -> None
        for v in other.versions:
            self.add(v)

    @coerced
    def union(self, other):
        # type: (VersionList) -> VersionPredicate
        result = self.copy()
        result.update(other)
        return result

    @coerced
    def intersection(self, other):
        # type: (VersionList) -> VersionPredicate
        # TODO: make this faster.  This is O(n^2).
        result = VersionList()
        for s in self:
            for o in other:
                result.add(s.intersection(o))
        return result

    @coerced
    def intersect(self, other):
        # type: (VersionList) -> bool
        """Intersect this spec's list with other.

        Return True if the spec changed as a result; False otherwise
        """
        isection = self.intersection(other)
        changed = (isection.versions != self.versions)
        self.versions = isection.versions
        return changed

    @coerced
    def __contains__(self, other):
        # type: (VersionList) -> bool
        if len(self) == 0:
            return False

        for version in other:
            i = bisect_left(self, other)  # type: ignore[arg-type]
            if i == 0:
                if version not in self[0]:
                    return False
            elif all(version not in v for v in self[i - 1:]):
                return False

        return True

    @overload
    def __getitem__(self, index):
        # type: (int) -> Union[Version, VersionRange]
        pass

    @overload
    def __getitem__(self, index):
        # type: (slice) -> VersionList
        pass

    def __getitem__(self, index):
        # type: (Union[int, slice]) -> Union[Version, VersionRange, VersionList]
        return self.versions[index]  # type: ignore[return-value]

    def __iter__(self):
        # type: () -> Iterator[Union[Version, VersionRange]]
        return iter(self.versions)

    def __reversed__(self):
        # type: () -> Iterator[VersionPredicate]
        return reversed(self.versions)

    def __len__(self):
        # type: () -> int
        return len(self.versions)

    def __bool__(self):
        # type: () -> bool
        return bool(self.versions)

    @coerced
    def __eq__(self, other):
        # type: (Any) -> bool
        return other is not None and self.versions == other.versions

    @coerced
    def __ne__(self, other):
        # type: (Any) -> bool
        return not (self == other)

    @coerced
    def __lt__(self, other):
        # type: (VersionList) -> bool
        return other is not None and self.versions < other.versions

    @coerced
    def __le__(self, other):
        # type: (VersionList) -> bool
        return self == other or self < other

    @coerced
    def __ge__(self, other):
        # type: (VersionList) -> bool
        return not (self < other)

    @coerced
    def __gt__(self, other):
        # type: (VersionList) -> bool
        return not (self == other) and not (self < other)

    def __hash__(self):
        # type: () -> int
        return hash(tuple(self.versions))

    def __str__(self):
        # type: () -> str
        return ",".join(str(v) for v in self.versions)

    def __repr__(self):
        # type: () -> str
        return str(self.versions)


def _string_to_version(string):
    # type: (str) -> VersionPredicate
    """Converts a string to a Version, VersionList, or VersionRange.
       This is private.  Client code should use ver().
    """
    string = string.replace(' ', '')

    if ',' in string:
        return VersionList(string.split(','))

    elif ':' in string:
        s, e = string.split(':')
        start = (_VersionEndpoint(Version(s), 'left')
                 if s else _VersionEndpoint.wildcard('left'))
        end = (_VersionEndpoint(Version(e), 'right')
               if e else _VersionEndpoint.wildcard('right'))
        return VersionRange(start, end)

    else:
        return Version(string)


def ver(obj):
    # type: (Any) -> VersionPredicate
    """Parses a Version, VersionRange, or VersionList from a string
       or list of strings.
    """
    if isinstance(obj, (list, tuple)):
        return VersionList(obj)
    elif isinstance(obj, string_types):
        return _string_to_version(obj)
    elif isinstance(obj, (int, float)):
        return _string_to_version(str(obj))
    elif type(obj) in (Version, VersionRange, VersionList):
        return obj
    else:
        raise TypeError("ver() can't convert %s to version!" % type(obj))


class VersionError(spack.error.SpackError):
    """This is raised when something is wrong with a version."""


class VersionChecksumError(VersionError):
    """Raised for version checksum errors."""
