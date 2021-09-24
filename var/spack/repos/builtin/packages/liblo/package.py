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
#     spack install liblo
#
# You can edit this file again by typing:
#
#     spack edit liblo
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Liblo(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "http://liblo.sourceforge.net/"
    git      = "git://github.com/radarsat1/liblo.git"

    # FIXME: Add a list of GitHub accounts to
    # notify when the package is updated.
    maintainers = ['cosmicexplorer']

    version('master')

    depends_on('autoconf', type='build')
    depends_on('automake', type='build')
    depends_on('libtool',  type='build')
    depends_on('m4',       type='build')

    def autoreconf(self, spec, prefix):
        autogen = Executable('./autogen.sh')
        autogen()
