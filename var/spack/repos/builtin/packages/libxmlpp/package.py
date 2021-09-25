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
#     spack install libxmlpp
#
# You can edit this file again by typing:
#
#     spack edit libxmlpp
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Libxmlpp(MesonPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://libxmlplusplus.github.io/libxmlplusplus/"
    url      = "https://github.com/libxmlplusplus/libxmlplusplus/archive/refs/tags/5.0.1.tar.gz"

    maintainers = ['cosmicexplorer']

    version('5.0.1', sha256='a2916814bed47ff60bfb010c58b1ab0390c79a9fa7ddfbb3e145c922e4ee7c0c')

    depends_on('libxml2')
    depends_on('glibmm@2.4', when='@2.6:3')
    depends_on('glibmm@2.68', when='@4:')
