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
#     spack install dbuscpp
#
# You can edit this file again by typing:
#
#     spack edit dbuscpp
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Dbuscpp(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://sourceforge.net/projects/dbus-cplusplus/"
    url      = "https://downloads.sourceforge.net/project/dbus-cplusplus/dbus-c%2B%2B/0.9.0/libdbus-c%2B%2B-0.9.0.tar.gz?ts=gAAAAABhTl-Dg-m3IKClAcftlUt4btjUMcBgYiLrqeNztFTMZYe8gUtvAgtSq-IkIq5hwq5imKK29XUxGrplKdR7y-1rQzMa2Q%3D%3D&use_mirror=gigenet&r=https%3A%2F%2Fsourceforge.net%2Fprojects%2Fdbus-cplusplus%2Ffiles%2F"

    maintainers = ['cosmicexplorer']

    version('0.9.0', sha256='bc11ac297b3cb010be904c72789695543ee3fdf3d75cdc8225fd371385af4e61')

    depends_on('dbus')
