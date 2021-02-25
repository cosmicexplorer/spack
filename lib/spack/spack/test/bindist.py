# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)
import os
import sys

import pytest

import spack.binary_distribution as bindist
import spack.config
import spack.fetch_strategy
import spack.hooks.sbang as sbang
import spack.main
import spack.mirror
import spack.repo
import spack.spec_index
import spack.store
import spack.util.gpg
import spack.util.web as web_util

from spack.directory_layout import YamlDirectoryLayout
from spack.spec import Spec
from spack.spec_index import ConcretizedSpec

mirror_cmd = spack.main.SpackCommand('mirror')
install_cmd = spack.main.SpackCommand('install')
uninstall_cmd = spack.main.SpackCommand('uninstall')
buildcache_cmd = spack.main.SpackCommand('buildcache')


@pytest.fixture(scope='function')
def install_dir_non_default_layout(tmpdir):
    """Hooks a fake install directory with a non-default layout"""
    scheme = os.path.join(
        '${name}', '${version}',
        '${architecture}-${compiler.name}-${compiler.version}-${hash}'
    )
    real_store, real_layout = spack.store.store, spack.store.layout
    opt_dir = tmpdir.join('opt')
    spack.store.store = spack.store.Store(str(opt_dir))
    spack.store.layout = YamlDirectoryLayout(str(opt_dir), path_scheme=scheme)
    try:
        yield spack.store
    finally:
        spack.store.store = real_store
        spack.store.layout = real_layout


args = ['strings', 'file']
if sys.platform == 'darwin':
    args.extend(['/usr/bin/clang++', 'install_name_tool'])
else:
    args.extend(['/usr/bin/g++', 'patchelf'])


@pytest.mark.requires_executables(*args)
@pytest.mark.maybeslow
@pytest.mark.usefixtures(
    'mutable_default_config', 'cache_directory', 'install_dir_default_layout',
    'test_mirror'
)
def test_default_rpaths_create_install_default_layout(mirror_dir):
    """
    Test the creation and installation of buildcaches with default rpaths
    into the default directory layout scheme.
    """
    gspec, cspec = Spec('garply').concretized(), Spec('corge').concretized()

    # Install 'corge' without using a cache
    install_cmd('--no-cache', cspec.name)

    cspec_str = ConcretizedSpec(cspec).spec_string_name_hash_only

    # Create a buildache
    buildcache_cmd('create', '-au', '-d', mirror_dir, cspec_str)
    # Test force overwrite create buildcache (-f option)
    buildcache_cmd('create', '-auf', '-d', mirror_dir, cspec_str)

    # Create mirror index
    mirror_url = 'file://{0}'.format(mirror_dir)
    buildcache_cmd('update-index', '-d', mirror_url)
    # List the buildcaches in the mirror
    buildcache_cmd('list', '-alv')

    # Uninstall the package and deps
    gspec_str = ConcretizedSpec(gspec).spec_string_name_hash_only
    uninstall_cmd('-y', '--dependents', gspec_str)

    # Test installing from build caches
    buildcache_cmd('install', '-au', cspec_str)

    # This gives warning that spec is already installed
    buildcache_cmd('install', '-au', cspec_str)

    # Test overwrite install
    buildcache_cmd('install', '-afu', cspec_str)

    buildcache_cmd('keys', '-f')
    buildcache_cmd('list')

    buildcache_cmd('list', '-a')
    buildcache_cmd('list', '-l', '-v')


@pytest.mark.requires_executables(*args)
@pytest.mark.maybeslow
@pytest.mark.nomockstage
@pytest.mark.usefixtures(
    'mutable_default_config', 'cache_directory', 'install_dir_non_default_layout',
    'test_mirror'
)
def test_default_rpaths_install_nondefault_layout(mirror_dir):
    """
    Test the creation and installation of buildcaches with default rpaths
    into the non-default directory layout scheme.
    """
    cspec = Spec('corge').concretized()

    # Install some packages with dependent packages
    # test install in non-default install path scheme
    buildcache_cmd('install', '-au', cspec.name)

    # Test force install in non-default install path scheme
    buildcache_cmd('install', '-auf', cspec.name)


@pytest.mark.requires_executables(*args)
@pytest.mark.maybeslow
@pytest.mark.nomockstage
@pytest.mark.usefixtures(
    'mutable_default_config', 'cache_directory', 'install_dir_default_layout'
)
def test_relative_rpaths_create_default_layout(mirror_dir):
    """
    Test the creation and installation of buildcaches with relative
    rpaths into the default directory layout scheme.
    """

    gspec, cspec = Spec('garply').concretized(), Spec('corge').concretized()

    # Install 'corge' without using a cache
    install_cmd('--no-cache', cspec.name)

    # Create build cache with relative rpaths
    buildcache_cmd(
        'create', '-aur', '-d', mirror_dir, cspec.name
    )

    # Create mirror index
    mirror_url = 'file://%s' % mirror_dir
    buildcache_cmd('update-index', '-d', mirror_url)

    # Uninstall the package and deps
    uninstall_cmd('-y', '--dependents', gspec.name)


@pytest.mark.requires_executables(*args)
@pytest.mark.maybeslow
@pytest.mark.nomockstage
@pytest.mark.usefixtures(
    'mutable_default_config', 'cache_directory', 'install_dir_default_layout',
    'test_mirror'
)
def test_relative_rpaths_install_default_layout(mirror_dir):
    """
    Test the creation and installation of buildcaches with relative
    rpaths into the default directory layout scheme.
    """
    gspec, cspec = Spec('garply').concretized(), Spec('corge').concretized()

    # Install buildcache created with relativized rpaths
    buildcache_cmd('install', '-auf', cspec.name)

    # This gives warning that spec is already installed
    buildcache_cmd('install', '-auf', cspec.name)

    # Uninstall the package and deps
    uninstall_cmd('-y', '--dependents', gspec.name)

    # Install build cache
    buildcache_cmd('install', '-auf', cspec.name)

    # Test overwrite install
    buildcache_cmd('install', '-auf', cspec.name)


@pytest.mark.requires_executables(*args)
@pytest.mark.maybeslow
@pytest.mark.nomockstage
@pytest.mark.usefixtures(
    'mutable_default_config', 'cache_directory', 'install_dir_non_default_layout',
    'test_mirror'
)
def test_relative_rpaths_install_nondefault(mirror_dir):
    """
    Test the installation of buildcaches with relativized rpaths
    into the non-default directory layout scheme.
    """
    cspec = Spec('corge').concretized()

    # Test install in non-default install path scheme and relative path
    buildcache_cmd('install', '-auf', cspec.name)


@pytest.mark.skipif(not spack.util.gpg.has_gpg(),
                    reason='This test requires gpg')
def test_push_and_fetch_keys(mock_gnupghome):
    testpath = str(mock_gnupghome)

    mirror = os.path.join(testpath, 'mirror')
    mirrors = {'test-mirror': mirror}
    mirrors = spack.mirror.MirrorCollection(mirrors)
    mirror = spack.mirror.Mirror('file://' + mirror)

    gpg_dir1 = os.path.join(testpath, 'gpg1')
    gpg_dir2 = os.path.join(testpath, 'gpg2')

    # dir 1: create a new key, record its fingerprint, and push it to a new
    #        mirror
    with spack.util.gpg.gnupg_home_override(gpg_dir1):
        spack.util.gpg.create(name='test-key',
                              email='fake@test.key',
                              expires='0',
                              comment=None)

        keys = spack.util.gpg.public_keys()
        assert len(keys) == 1
        fpr = keys[0]

        bindist.push_keys(mirror, keys=[fpr], regenerate_index=True)

    # dir 2: import the key from the mirror, and confirm that its fingerprint
    #        matches the one created above
    with spack.util.gpg.gnupg_home_override(gpg_dir2):
        assert len(spack.util.gpg.public_keys()) == 0

        bindist.get_keys(mirrors=mirrors, install=True, trust=True, force=True)

        new_keys = spack.util.gpg.public_keys()
        assert len(new_keys) == 1
        assert new_keys[0] == fpr


@pytest.mark.requires_executables(*args)
@pytest.mark.maybeslow
@pytest.mark.nomockstage
@pytest.mark.usefixtures(
    'mutable_default_config', 'cache_directory', 'install_dir_non_default_layout',
    'test_mirror'
)
def test_built_spec_cache(mirror_dir):
    """ Because the buildcache list command fetches the buildcache index
    and uses it to populate the binary_distribution built spec cache, when
    this test calls get_mirrors_for_spec, it is testing the popluation of
    that cache from a buildcache index. """
    buildcache_cmd('list', '-a', '-l')

    gspec, cspec = Spec('garply').concretized(), Spec('corge').concretized()

    full_hash_map = {
        'garply': gspec.full_hash(),
        'corge': cspec.full_hash(),
    }

    gspec_results = bindist.get_mirrors_for_spec(gspec)

    gspec_mirrors = {}
    for result in gspec_results:
        s = result['spec']
        assert(s._full_hash == full_hash_map[s.name])
        assert(result['mirror_url'] not in gspec_mirrors)
        gspec_mirrors[result['mirror_url']] = True

    cspec_results = bindist.get_mirrors_for_spec(cspec, full_hash_match=True)

    cspec_mirrors = {}
    for result in cspec_results:
        s = result['spec']
        assert(s._full_hash == full_hash_map[s.name])
        assert(result['mirror_url'] not in cspec_mirrors)
        cspec_mirrors[result['mirror_url']] = True


def fake_full_hash(spec):
    # Generate an arbitrary hash that is intended to be different than
    # whatever a Spec reported before (to test actions that trigger when
    # the hash changes)
    return 'tal4c7h4z0gqmixb1eqa92mjoybxn5l6'


@pytest.mark.usefixtures(
    'install_mockery_mutable_config', 'mock_packages', 'mock_fetch',
    'test_mirror'
)
def test_spec_needs_rebuild(monkeypatch, tmpdir):
    """Make sure needs_rebuild properly compares remote full_hash
    against locally computed one, avoiding unnecessary rebuilds"""

    # Create a temp mirror directory for buildcache usage
    mirror_dir = tmpdir.join('mirror_dir')
    mirror_url = 'file://{0}'.format(mirror_dir.strpath)

    s = Spec('libdwarf').concretized()

    # Install a package
    install_cmd(s.name)

    # Put installed package in the buildcache
    buildcache_cmd('create', '-u', '-a', '-d', mirror_dir.strpath, s.name)

    rebuild = bindist.needs_rebuild(s, mirror_url, rebuild_on_errors=True)

    assert not rebuild

    # Now monkey patch Spec to change the full hash on the package
    monkeypatch.setattr(spack.spec.Spec, 'full_hash', fake_full_hash)

    rebuild = bindist.needs_rebuild(s, mirror_url, rebuild_on_errors=True)

    assert rebuild


def test_generate_indices_key_error(monkeypatch, capfd):

    def mock_list_url(url, recursive=False):
        print('mocked list_url({0}, {1})'.format(url, recursive))
        raise KeyError('Test KeyError handling')

    monkeypatch.setattr(web_util, 'list_url', mock_list_url)

    test_url = 'file:///fake/keys/dir'

    # Make sure generate_key_index handles the KeyError
    bindist.generate_key_index(test_url)

    err = capfd.readouterr()[1]
    assert 'Warning: No keys at {0}'.format(test_url) in err

    # Make sure generate_package_index handles the KeyError
    bindist.generate_package_index(test_url)

    err = capfd.readouterr()[1]
    assert 'Warning: No packages at {0}'.format(test_url) in err


def test_generate_indices_exception(monkeypatch, capfd):

    def mock_list_url(url, recursive=False):
        print('mocked list_url({0}, {1})'.format(url, recursive))
        raise Exception('Test Exception handling')

    monkeypatch.setattr(web_util, 'list_url', mock_list_url)

    test_url = 'file:///fake/keys/dir'

    # Make sure generate_key_index handles the Exception
    bindist.generate_key_index(test_url)

    err = capfd.readouterr()[1]
    expect = 'Encountered problem listing keys at {0}'.format(test_url)
    assert expect in err

    # Make sure generate_package_index handles the Exception
    bindist.generate_package_index(test_url)

    err = capfd.readouterr()[1]
    expect = 'Encountered problem listing packages at {0}'.format(test_url)
    assert expect in err


class DoNothing(object):
    def __call__(self):
        pass


@pytest.fixture(scope='function')
def discard_checksum(monkeypatch):
    monkeypatch.setattr(spack.fetch_strategy.URLFetchStrategy, 'check', DoNothing())


@pytest.mark.db
@pytest.mark.usefixtures('mock_fetch', 'mutable_default_config', 'discard_checksum')
def test_update_sbang(tmpdir, test_mirror, mutable_database, patch_spec_indices):
    """Test the creation and installation of buildcaches with default rpaths
    into the non-default directory layout scheme, triggering an update of the
    sbang.
    """
    scheme = os.path.join(
        '${name}', '${version}',
        '${architecture}-${compiler.name}-${compiler.version}-${hash}'
    )
    spec_str = 'old-sbang'
    # Concretize a package with some old-fashioned sbang lines.
    old_spec = Spec(spec_str).concretized()
    old_concretized = ConcretizedSpec(old_spec)
    old_spec_hash_str = old_concretized.spec_string_name_hash_only

    # Need a fake mirror with *function* scope.
    mirror_dir = test_mirror
    mirror_url = 'file://{0}'.format(mirror_dir)

    # Assume all commands will concretize old_spec the same way.
    install_cmd('--no-cache', old_spec.name)

    # Create a buildcache with the installed spec.
    buildcache_cmd('create', '-u', '-a', '-d', mirror_dir, old_spec_hash_str)

    # Need to force an update of the buildcache index
    buildcache_cmd('update-index', '-d', mirror_url)

    entry = spack.spec_index.local_spec_index.lookup_ensuring_single_match(
            old_concretized.into_hash())
    patch_spec_indices.intern_concretized_spec(entry.concretized_spec, entry.record)

    # Uninstall the original package.
    uninstall_cmd('-y', old_spec_hash_str)

    # Switch the store to the new install tree locations
    newtree_dir = tmpdir.join('newtree')
    s = spack.store.Store(str(newtree_dir))
    s.layout = YamlDirectoryLayout(str(newtree_dir), path_scheme=scheme)

    with spack.store.use_store(s):
        new_spec = Spec('old-sbang').concretized()
        assert new_spec.dag_hash() == old_spec.dag_hash()

        # Install package from buildcache
        buildcache_cmd('install', '-a', '-u', '-f', new_spec.name)

        # Continue blowing away caches
        bindist.clear_spec_cache()
        spack.stage.purge()

        # test that the sbang was updated by the move
        sbang_style_1_expected = '''{0}
#!/usr/bin/env python

{1}
'''.format(sbang.sbang_shebang_line(), new_spec.prefix.bin)
        sbang_style_2_expected = '''{0}
#!/usr/bin/env python

{1}
'''.format(sbang.sbang_shebang_line(), new_spec.prefix.bin)

        installed_script_style_1_path = new_spec.prefix.bin.join('sbang-style-1.sh')
        assert sbang_style_1_expected == \
            open(str(installed_script_style_1_path)).read()

        installed_script_style_2_path = new_spec.prefix.bin.join('sbang-style-2.sh')
        assert sbang_style_2_expected == \
            open(str(installed_script_style_2_path)).read()

        patch_spec_indices.location = spack.spec_index.IndexLocation.LOCAL()
        uninstall_cmd('-y', '/%s' % new_spec.dag_hash())
