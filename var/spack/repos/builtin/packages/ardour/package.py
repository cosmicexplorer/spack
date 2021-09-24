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
#     spack install ardour
#
# You can edit this file again by typing:
#
#     spack edit ardour
#
# See the Spack documentation for more information on packaging.
# ----------------------------------------------------------------------------

from spack import *


class Ardour(WafPackage):
    """Ardour is a Digital Audio Workstation for Linux, macOS, and Windows."""

    homepage = "https://ardour.org"
    git      = "git://git.ardour.org/ardour/ardour.git"

    maintainers = ['cosmicexplorer']

    version('7.0-pre0', tag='7.0-pre0')

    variant('optimize', default=True)
    variant('docs', default=False)
    variant('backtrace', default=False)
    variant('debug', default=False)
    variant('freedesktop', default=False)
    variant('profile', default=False)
    variant('lxvst', default=True)
    variant('vst3', default=True)
    variant('windows-vst', default=False)
    variant('program-name', default='ardour')

    depends_on('doxygen', when='+docs', type='build')
    depends_on('tar')
    depends_on('graphviz')
    depends_on('boost')
    depends_on('pkg-config', type=('build', 'link'))
    depends_on('alsa-lib')
    depends_on('glib@2.64:')
    depends_on('glibmm@2.32:')
    depends_on('libsndfile@1.0.18:')
    depends_on('curl@7.0.0:')
    depends_on('libarchive@3.0.0:')
    depends_on('liblo@0.26:')
    depends_on('taglib@1.9:')
    depends_on('vamp-sdk@2.1:')
    depends_on('rubberband')
    depends_on('fftw')
    depends_on('aubio@0.3.2:')
    depends_on('python+pythoncmd')

    def configure_args(self):
        return super(Ardour, self).configure_args() + [
            '--verbose',
            '--progress',
            '--cxx11',
        ] + (
            (['--optimize', '--fpu-optimization']
             if self.spec.variants['optimize'].value else []) +
            (['--docs'] if self.spec.variants['docs'].value else []) +
            (['--backtrace'] if self.spec.variants['backtrace'].value else []) +
            (['--debug-symbols'] if self.spec.variants['debug'].value else []) +
            (['--freedesktop'] if self.spec.variants['freedesktop'].value else []) +
            (['--profile', '--gprofile']
             if self.spec.variants['profile'] else []) +
            (['--lxvst'] if self.spec.variants['lxvst'] else ['--no-lxvst']) +
            (['--vst3'] if self.spec.variants['vst3'] else ['--no-vst3']) +
            (['--windows-vst'] if self.spec.variants['windows-vst'] else [])
        ) + ['--program-name={0}'.format(self.spec.variants['program-name'].value)]
