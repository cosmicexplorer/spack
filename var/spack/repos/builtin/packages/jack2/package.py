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
#     spack install jack2
#
# You can edit this file again by typing:
#
#     spack edit jack2
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Jack2(WafPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://jackaudio.org/downloads/"
    url      = "https://github.com/jackaudio/jack2/archive/v1.9.19.tar.gz"
    git      = "git://github.com/jackaudio/jack2.git"

    maintainers = ['cosmicexplorer']

    version('1.9.19', sha256='9030f4dc11773351b6ac96affd9c89803a5587ebc1b091e5ff866f433327e4b0')

    depends_on('pkg-config', type='build')
    depends_on('alsa-lib@1.0.18:')
    depends_on('libffado@1.999.17:')
    depends_on('gtkiostream@1.4.0:')
    depends_on('eigen@3.1.2:')
    depends_on('libsamplerate')
    depends_on('libsndfile')
    depends_on('readline')
    depends_on('gdbm')
    depends_on('opus-codec@0.8:')

    # FIXME: Override configure_args(), build_args(),
    # or install_args() if necessary.
