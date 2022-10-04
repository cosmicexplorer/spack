# Copyright 2013-2022 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

"""Type definitions for filesystem.py."""
from typing import Any, Iterable, TypeVar, Union
from typing_extensions import overload

from llnl.util.compat import Sequence


_Self = TypeVar("_Self")


class FileList(Sequence):

    files: List[str]

    def __init__(self, files: Union[str, Iterable[str]]) -> None: ...

    @property
    def directories(self) -> List[str]: ...

    @property
    def basenames(self) -> List[str]: ...

    @overload
    def __getitem__(self, item: int) -> str: ...

    @overload
    def __getitem__(self: _Self, item: slice) -> _Self: ...

    def __add__(self: _Self, other: Iterable[str]) -> _Self: ...

    def __radd__(self: _Self, other: Iterable[str]) -> _Self: ...

    def __eq__(self, other: Any) -> bool: ...

    def __len__(self) -> int: ...

    def joined(self, separator: str = " ") -> str: ...

    def __repr__(self) -> str: ...

    def __str__(self) -> str: ...


class HeaderList(FileList):

    include_regex: re.Pattern

    def __init__(self, files: Union[str, Iterable[str]]) -> None: ...

    @property
    def directories(self) -> List[str]: ...

    @directories.setter
    def directories(self, value: Union[str, Iterable[str]]) -> None: ...

    @property
    def headers(self) -> List[str]: ...

    @property
    def names(self) -> List[str]: ...

    @property
    def include_flags(self) -> str: ...

    @property
    def macro_definitions(self) -> str: ...

    @property
    def cpp_flags(self) -> str: ...

    def add_macro(self, macro: str) -> None: ...


def find_headers(
    headers: Union[str, Iterable[str]],
    root: str,
    recursive: bool = False,
) -> HeaderList: ...


def find_all_headers(root: str) -> HeaderList: ...


class LibraryList(FileList):

    @property
    def libraries(self) -> List[str]: ...

    @property
    def names(self) -> List[str]: ...

    @property
    def search_flags(self) -> str: ...

    @property
    def link_flags(self) -> str: ...

    @property
    def ld_flags(self) -> str: ...


def find_system_libraries(
    libraries: Union[str, Iterable[str]],
    shared: bool = True,
) -> LibraryList: ...


def find_libraries(
    libraries: Union[str, Iterable[str]],
    root: str,
    shared: bool = True,
    recursive: bool = False,
) -> LibraryList: ...


def find_all_shared_libraries(root: str, recursive: bool = False) -> LibraryList: ...


def find_all_static_libraries(root: str, recursive: bool = False) -> LibraryList: ...


def find_all_libraries(root: str, recursive: bool = False) -> LibraryList: ...
