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
#     spack install vamp-sdk
#
# You can edit this file again by typing:
#
#     spack edit vamp-sdk
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class VampSdk(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    # FIXME: Add a proper url for your package's homepage here.
    homepage = "https://vamp-plugins.org/"
    git      = "https://github.com/c4dm/vamp-plugin-sdk.git"

    maintainers = ['cosmicexplorer']

    version('master')

    depends_on('libsndfile')
