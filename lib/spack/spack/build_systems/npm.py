# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)
from typing import List  # novm

from llnl.util.filesystem import install_tree

from spack.directives import extends, variant
from spack.package import PackageBase, run_after
from spack.util.executable import which


class NpmPackage(PackageBase):
    """Specialized class for node.js packages which can be built using npm."""

    #: Phases of an npm package installation.
    phases = ['fetch_and_build', 'install_into_prefix']  # type: List[str]
    #: This attribute is used in UI queries that need to know the build
    #: system base class.
    build_system_class = 'NpmPackage'  # type: str

    build_time_test_callbacks = ['test']

    #: Package name, version, and extension on npmjs.com. This is the last component of the URL
    #: retrieved by executing the : command `npm view <package> dist.tarball`.
    npm = None  # type: str

    @property
    def package_name(self):
        if self.npm:
            return self.npm.split('-')[0]

    @property
    def homepage(self):
        if self.npm:
            return 'https://www.npmjs.com/package/{0}'.format(self.package_name)

    @property
    def url(self):
        if self.npm:
            return 'https://registry.npmjs.org/{0}/-/{1}'.format(self.package_name, self.npm)

    variant('resolver', default='yarn',
            description='Which resolver to use. This shouldn\'t matter for most use cases.',
            values=('npm', 'yarn'))

    extends('npm', when='resolver=npm', type='build')
    extends('yarn', when='resolver=yarn', type='build')

    @property
    def resolver(self):
        """An Executable instance for either `npm` or `yarn`."""
        resolver_name = self.spec.variants['resolver'].value
        if resolver_name == 'npm':
            return which('npm')
        assert resolver_name == 'yarn', (
            'expected resolver to be named npm or yarn: was {0}'.format(resolver_name))
        return which('yarn')

    def fetch_and_build(self, spec, prefix):
        """Runs `npm install` or `yarn install` in the source directory."""
        self.resolver('install')

    run_after('fetch_and_build')(PackageBase._run_default_build_time_test_callbacks)

    def install_into_prefix(self, spec, prefix):
        """Copies the contents of node_modules/ into the install prefix."""
        install_tree('node_modules', prefix)

    # Check that self.prefix is there after installation
    run_after('install_into_prefix')(PackageBase.sanity_check_prefix)

    run_after('install_into_prefix')(PackageBase._run_default_install_time_test_callbacks)

    def test(self):
        """???"""
        pass
