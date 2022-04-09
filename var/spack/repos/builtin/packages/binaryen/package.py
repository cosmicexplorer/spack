# Copyright 2013-2023 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

import os
import re

from spack.package import *


class Binaryen(CMakePackage):
    """Compiler infrastructure and toolchain library for WebAssembly"""

    homepage = "https://github.com/WebAssembly/binaryen"
    git = "https://github.com/WebAssembly/binaryen.git"
    url = "https://github.com/WebAssembly/binaryen/archive/refs/tags/version_105.tar.gz"

    version("105", sha256="c5ec27c157d3b33ce4360607cc6afe565fa490094237895db2162b3a7d667da2")
    version("101", sha256="5d7cdec89957549f01b7c93f080d08827c87bbd4789a34694c740d15d077c041")

    executables = (
        "^{}$".format(re.escape(exe))
        for exe in [
            "wasm-opt",
            "wasm-as",
            "wasm-dis",
            "wasm2js",
            "wasm-reduce",
            "wasm-shell",
            "wasm-emscripten-finalize",
            "wasm-ctor-eval",
            "binaryen.js",
        ]
    )

    @classmethod
    def determine_version(cls, exe_path):
        try:
            exe = Executable(exe_path)
            output = exe("--version", output=str, error=str)
            pattern = r"^{} version ([0-9]+)$".format(re.escape(os.path.basename(exe_path)))
            m = re.match(pattern, output)
            if m is None:
                return None
            (v,) = m.groups()
            return Version(v)
        except spack.util.executable.ProcessError:
            pass

        return None
