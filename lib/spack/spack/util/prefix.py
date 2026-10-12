# Copyright Spack Project Developers. See COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

"""
This file contains utilities for managing the installation prefix of a package.
"""

import os
from pathlib import Path, PurePath
from typing import TYPE_CHECKING, Dict

if TYPE_CHECKING:
    from typing import Any, Iterable, Self


class _InnerPrefix:
    _anchor: str | None
    _tail: tuple[str, ...]
    __slots__ = ('_anchor', '_tail')
    def __getnewargs__(self) -> tuple[str | None, tuple[str, ...]]:
        return (self._anchor, tuple(self._tail))
    def __new__(cls, anchor: str | None, tail: Iterable[str]) -> Self:
        if anchor is not None:
            assert type(anchor) is str, anchor
            if anchor == '':
                anchor = None
            else:
                assert anchor.endswith(os.path.sep), anchor
        tail = tuple(tail)
        for el in tail:
            assert os.path.sep not in el, el
        ret = super().__new__(cls)
        ret._anchor = anchor
        ret._tail = tail
        return ret
    def __str__(self) -> str:
        if self._anchor is None:
            return os.path.sep.join(self._tail)
        return self._anchor + os.path.sep.join(self._tail)
    def __hash__(self) -> int:
        return hash(self.__getnewargs__())
    def __eq__(self, other: Any) -> bool:
        if type(other) is not self.__class__:
            return False
        if self._anchor is None and other._anchor is not None:
            return False
        if self._anchor is not None and other._anchor is None:
            return False
        return self._anchor == other._anchor and self._tail == other._tail
    def __ne__(self, other: Any) -> bool:
        return not self == other
    def join(self, name: str) -> Self:
        assert not name.startswith(os.path.sep), name
        return self.__class__(self._anchor,
                              self._tail + filter(None, name.split(os.path.sep)))
    @classmethod
    def from_path(cls, path: PurePath) -> Self:
        return cls(path.anchor, path._tail)
    @classmethod
    def from_str(cls, s: str) -> Self:
        return cls.from_path(PurePath(s))


class Prefix(str):
    """This class represents an installation prefix, but provides useful attributes for referring
    to directories inside the prefix.

    Attributes of this object are created on the fly when you request them, so any of the following
    are valid:

    >>> prefix = Prefix("/usr")
    >>> prefix.bin
    /usr/bin
    >>> prefix.lib64
    /usr/lib64
    >>> prefix.share.man
    /usr/share/man
    >>> prefix.foo.bar.baz
    /usr/foo/bar/baz
    >>> prefix.join("dashed-directory").bin64
    /usr/dashed-directory/bin64

    Prefix objects behave identically to strings. In fact, they subclass :class:`str`, so operators
    like ``+`` are legal::

        print("foobar " + prefix)

    This prints ``foobar /usr``. All of this is meant to make custom installs easy.
    """

    def __getattr__(self, name: str) -> "Prefix":
        """Concatenate a string to a prefix.

        Useful for strings that are valid variable names.

        Args:
            name: the string to append to the prefix

        Returns:
            the newly created installation prefix
        """
        return Prefix(os.path.join(self, name))

    def join(self, string: str) -> "Prefix":  # type: ignore[override]
        """Concatenate a string to a prefix.

        Useful for strings that are not valid variable names. This includes strings containing
        characters like ``-`` and ``.``.

        Args:
            string: the string to append to the prefix

        Returns:
            the newly created installation prefix
        """
        return Prefix(os.path.join(self, string))

    def __getstate__(self) -> Dict[str, str]:
        """Control how object is pickled.

        Returns:
            current state of the object
        """
        return self.__dict__

    def __setstate__(self, state: Dict[str, str]) -> None:
        """Control how object is unpickled.

        Args:
            new state of the object
        """
        self.__dict__.update(state)
