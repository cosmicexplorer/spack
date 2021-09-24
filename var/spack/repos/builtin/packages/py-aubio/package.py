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
#     spack install py-aubio
#
# You can edit this file again by typing:
#
#     spack edit py-aubio
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class PyAubio(PythonPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://aubio.org/"
    pypi      = "aubio/aubio-0.4.9.tar.gz"

    maintainers = ['cosmicexplorer']

    version('0.4.9', sha256='df1244f6c4cf5bea382c8c2d35aa43bc31f4cf631fe325ae3992c219546a4202')

    depends_on('py-numpy', type=('build', 'run'))
