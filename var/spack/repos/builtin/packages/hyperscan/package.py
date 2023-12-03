# Copyright 2013-2023 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

import platform

from spack.package import *

_versions = {
    "v5.2.1": {
        "Linux-aarch64": (
            "d2ac1669154ec27b794b64d026ad09caecee6e5e17fd35107595a7517711d2b9",
            "https://github.com/kunpengcompute/hyperscan/archive/v5.2.1.aarch64.tar.gz",
        ),
        "Linux-x86_64": (
            "fd879e4ee5ecdd125e3a79ef040886978ae8f1203832d5a3f050c48f17eec867",
            "https://github.com/intel/hyperscan/archive/v5.2.1.tar.gz",
        ),
    }
}


class Hyperscan(CMakePackage):
    """High-performance regular expression matching library."""

    homepage = "https://www.hyperscan.io/"
    url = "https://github.com/intel/hyperscan/archive/v5.2.1.tar.gz"
    git = "https://github.com/intel/hyperscan.git"
    list_url = "https://github.com/intel/hyperscan/releases"

    version("v5.4.2", tag="v5.4.2")

    license("BSD-2-Clause")

    for ver, packages in _versions.items():
        key = "{0}-{1}".format(platform.system(), platform.machine())
        pkg = packages.get(key)
        if pkg:
            version(ver, sha256=pkg[0], url=pkg[1])

    depends_on("boost+exception+serialization+random+graph+container")
    depends_on("pcre@8.41+utf", when="+chimera")
    depends_on("ragel", type="build")

    variant("chimera", default=False, description="Build the chimera PCRE compat library.")
    variant("shared", default=False, description="Build shared libs")
    variant("static", default=True, description="Build static libs"),
    conflicts("~shared~static", msg="must build shared and/or static libs!")
    conflicts("+chimera+shared", msg="chimera does not allow shared libs!")

    # TODO: FAT_RUNTIME flag!

    patch("native-stream-api-2.patch")

    def cmake_args(self):
        args = []
        if '+chimera' in self.spec:
            pcre_stage = self.spec['pcre'].package.stage[0]
            pcre_stage.create()
            pcre_stage.fetch()
            pcre_stage.expand_archive()
            args.extend([
                self.define("PCRE_SOURCE", pcre_stage.source_path),
                self.define("BUILD_CHIMERA", "TRUE"),
            ])

        if '+shared+static' in self.spec:
            args.append(self.define("BUILD_STATIC_AND_SHARED", "ON"))
        elif '+shared' in self.spec:
            args.append(self.define("BUILD_SHARED_LIBS", "ON"))
        else:
            assert '+static' in self.spec
            args.append(self.define("BUILD_STATIC_LIBS", "ON"))

        return args
