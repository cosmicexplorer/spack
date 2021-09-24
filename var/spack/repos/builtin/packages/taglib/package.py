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
#     spack install taglib
#
# You can edit this file again by typing:
#
#     spack edit taglib
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Taglib(CMakePackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://taglib.org"
    git      = "https://github.com/taglib/taglib.git"

    maintainers = ['cosmicexplorer']

    # FIXME: Add proper versions here.
    version('master')
