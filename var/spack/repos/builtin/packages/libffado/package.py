# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

# ----------------------------------------------------------------------------
# If you submit this package back to Spack as a pull request,
# please first remove this boilerplate and all FIXME comments.
#
# This is a template package file for Spack.  We've put "FIXME"
# next to all the things you'll want to change. Once you've handled
# them, you can save this file and test your package like this:
#
#     spack install libffado
#
# You can edit this file again by typing:
#
#     spack edit libffado
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Libffado(SConsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "http://ffado.org"
    url      = "http://ffado.org/files/libffado-2.4.4.tgz"

    maintainers = ['cosmicexplorer']

    version('2.4.4', sha256='a47178cdc8c0c91e91edbaabe23d19ca12a752cbcf81c27314adb27cc00d60f0')

    depends_on('libxmlpp@2.6.13:')
    depends_on('libraw1394@2.0.7:')
    depends_on('libiec61883@1.1.0:')
    depends_on('dbus@1.0:')
    depends_on('dbuscpp')
    depends_on('libconfig')

    def build_args(self, spec, prefix):
        # FIXME: Add arguments to pass to build.
        # FIXME: If not needed delete this function
        args = []
        return args
