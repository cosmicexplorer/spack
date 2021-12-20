# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from llnl.util.filesystem import install_tree

from spack import *
from spack.util.executable import Executable


class Pash(Package):
    """PaSh: Light-touch Data-Parallel Shell Processing."""

    homepage = "https://binpa.sh"
    url      = "https://github.com/binpash/pash/archive/refs/tags/v0.6.tar.gz"
    git      = "https://github.com/binpash/pash"

    maintainers = ['cosmicexplorer']

    version('0.6', sha256='59f584d9a38ec9da4eb6e67f7ea4905324aa8675e069540c180a28571d8c0b1d')

    depends_on('git', type='build')
    depends_on('libtool', type='build')
    depends_on('m4@1.4:', type='build')
    depends_on('automake', type='build')
    depends_on('curl', type='build')
    depends_on('pkg-config', type='build')
    depends_on('python')
    depends_on('py-pip', type='build')
    depends_on('libffi')
    depends_on('sed', type='build')
    depends_on('gmake', type='build')
    depends_on('autoconf', type='build')
    depends_on('gcc@10:', type='build')
    depends_on('bc', type='build')

    patch('install-wheel.patch')
    patch('fix-std-int-bool.patch')

    def install(self, spec, prefix):
        Executable('./scripts/setup-pash.sh')()
        install_tree('.', prefix)
