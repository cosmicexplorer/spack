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
#     spack install libraw1394
#
# You can edit this file again by typing:
#
#     spack edit libraw1394
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Libraw1394(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://ieee1394.wiki.kernel.org/"
    url      = "https://www.kernel.org/pub/linux/libs/ieee1394/libraw1394-2.1.2.tar.gz"

    maintainers = ['cosmicexplorer']

    version('2.1.2', sha256='ddc4e32721cdfe680d964aaede68ac606a20cd17dd2ba70e2d7e0692086ab57c')
