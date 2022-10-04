# Copyright 2013-2022 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

"""Type definitions for path.py."""
import re
from typing import Any, Callable, Optional, TypeVar, Tuple
from typing_extensions import overload


def path_to_os_path(*pths: Any) -> Tuple[Any, ...]: ...


_T = TypeVar("_T")


@overload
def system_path_filter(_func: Callable[..., _T], arg_slice: None) -> Callable[..., _T]: ...


@overload
def system_path_filter(
    _func: None,
    arg_slice: slice,
) -> Callable[[Callable[..., _T]], Callable[..., _T]]: ...


class Path:
    unix: int
    windows: int
    platform_path: int


def format_os_path(path: str, mode: Path = Path.unix) -> str: ...


def convert_to_posix_path(path: str) -> str: ...


def convert_to_windows_path(path: str) -> str: ...


def convert_to_platform_path(path: str) -> str: ...
