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
#     spack install gtkiostream
#
# You can edit this file again by typing:
#
#     spack edit gtkiostream
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Gtkiostream(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://github.com/flatmax/gtkiostream"
    url      = "https://downloads.sourceforge.net/project/gtkiostream/Version%201.5.0/gtkiostream-1.5.0.tar.xz?ts=gAAAAABhTmFOKWqGRh1xmLasYEyOjPzuehWgFV8BBwGFcbEEPpcK44I_5NCFZvxDIjwoF1BC-XvnNyyPc0AX5Ipsa0gG7tmG5g%3D%3D&r=https%3A%2F%2Fsourceforge.net%2Fprojects%2Fgtkiostream%2Ffiles%2Flatest%2Fdownload"

    maintainers = ['cosmicexplorer']

    version('1.5.0', sha256='0c04b587a882e11a821e1f2b31054926b98a8983def9eb5c828d4ce88e1b8e2a')

    depends_on('autoconf', type='build')
    depends_on('automake', type='build')
    depends_on('libtool',  type='build')
    depends_on('m4',       type='build')

    def autoreconf(self, spec, prefix):
        # FIXME: Modify the autoreconf method as necessary
        autoreconf('--install', '--verbose', '--force')

    def configure_args(self):
        # FIXME: Add arguments other than --prefix
        # FIXME: If not needed delete this function
        args = []
        return args
