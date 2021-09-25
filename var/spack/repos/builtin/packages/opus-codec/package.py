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
#     spack install opus-codec
#
# You can edit this file again by typing:
#
#     spack edit opus-codec
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class OpusCodec(CMakePackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://opus-codec.org"
    url      = "https://archive.mozilla.org/pub/opus/opus-1.3.1.tar.gz"

    maintainers = ['cosmicexplorer']

    version('1.3.1', sha256='65b58e1e25b2a114157014736a3d9dfeaad8d41be1c8179866f144a2fb44ff9d')
