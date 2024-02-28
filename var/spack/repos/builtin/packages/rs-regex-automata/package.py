# Copyright 2013-2024 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack.package import *


class RsRegexAutomata(CargoPackage):
    """This crate exposes a variety of regex engines used by the regex
    crate. It provides a vast, sprawling and “expert” level API to
    each regex engine. The regex engines provided by this crate focus
    heavily on finite automata implementations and specifically
    guarantee worst case O(m * n) time complexity for all
    searches. (Where m ~ len(regex) and n ~ len(haystack).)
    """

    homepage = "https://github.com/rust-lang/regex"
    git = "https://github.com/rust-lang/regex"
    # url = "https://github.com/BurntSushi/ripgrep/archive/11.0.2.tar.gz"

    maintainers("cosmicexplorer")

    license("MIT OR Unlicense")

    version("0.4.5", tag="regex-automata-0.4.5")
