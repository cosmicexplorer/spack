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
#     spack install libiec61883
#
# You can edit this file again by typing:
#
#     spack edit libiec61883
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Libiec61883(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://ieee1394.wiki.kernel.org/"
    url      = "https://www.kernel.org/pub/linux/libs/ieee1394/libiec61883-1.2.0.tar.gz"

    maintainers = ['cosmicexplorer']

    version('1.2.0', sha256='594dbdd4e391d8a4df740db573681b288eee0366e443e5d465febbefd24a5a32')

    depends_on('libraw1394@0.9.0:')
