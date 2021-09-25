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
#     spack install aubio
#
# You can edit this file again by typing:
#
#     spack edit aubio
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Aubio(WafPackage):
    """FIXME: Put a proper description of your package here."""

    homepage = "https://aubio.org/"
    git      = "https://github.com/aubio/aubio"
    url      = "https://github.com/aubio/aubio/archive/refs/tags/0.4.9.tar.gz"

    maintainers = ['cosmicexplorer']

    version('0.4.9', sha256='0f09bee62f752d2be3a620966f020e72a027fed6838d7e9389e8305507f12455')

    depends_on('gmake', type='build')
    depends_on('python+pythoncmd', type='build')
    depends_on('gawk', type='build')
    depends_on('bash', type='build')
    depends_on('jack2')

    # The default script to download waf by verifying the gpg key doesn't appear
    # to work. This version checks it against the checksum 'c74055d7452540ad66c12d955c09f62a9fde0e23b0ab3c43984dc879b4bb51f4'.
    patch('waf-sha256sum-no-gpg.patch')
    # Manually patch 'python' -> 'python3'.
    patch('py3-command.patch')

    @run_before('configure')
    def expand_waf(self):
        make = which('make')
        make('expandwaf')
