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
#     spack install mm-common
#
# You can edit this file again by typing:
#
#     spack edit mm-common
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class MmCommon(AutotoolsPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://gitlab.gnome.org/GNOME/mm-common"
    git      = "https://gitlab.gnome.org/GNOME/mm-common.git"

    maintainers = ['cosmicexplorer']

    version('master')

    def autoreconf(self, spec, prefix):
        autogen = Executable('./autogen.sh')
        autogen()

    def configure_args(self):
        return ['--enable-network']
