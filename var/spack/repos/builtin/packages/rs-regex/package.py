# Copyright 2013-2024 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack.package import *


class RsRegex(CargoPackage):
    """This crate provides routines for searching strings for matches
    of a regular expression (aka "regex").

    The regex syntax supported by this crate is similar to other regex
    engines, but it lacks several features that are not known how to
    implement efficiently. This includes, but is not limited to,
    look-around and backreferences. In exchange, all regex searches in
    this crate have worst case O(m * n) time complexity, where m is
    proportional to the size of the regex and n is proportional to the
    size of the string being searched.
    """

    homepage = "https://github.com/rust-lang/regex"
    git = "https://github.com/rust-lang/regex"
    # url = "https://github.com/BurntSushi/ripgrep/archive/11.0.2.tar.gz"

    maintainers("cosmicexplorer")

    license("MIT OR Unlicense")

    depends_on("rs-regex-automata")
    depends_on("rs-regex-syntax")

    version("1.10.3", tag="1.10.3")
