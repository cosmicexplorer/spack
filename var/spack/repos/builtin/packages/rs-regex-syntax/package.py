# Copyright 2013-2024 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack.package import *


class RsRegexSyntax(CargoPackage):
    """This crate provides a robust regular expression parser."""

    homepage = "https://github.com/rust-lang/regex"
    git = "https://github.com/rust-lang/regex"
    # url = "https://github.com/BurntSushi/ripgrep/archive/11.0.2.tar.gz"

    maintainers("cosmicexplorer")

    license("MIT OR Unlicense")

    version("0.8.2", tag="regex-syntax-0.8.2")
