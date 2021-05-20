# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

import copy
import os
import re

import pytest

from llnl.util.filesystem import touch, working_dir

import spack.config
import spack.repo
from spack.fetch_strategy import (ConfiguredGit, GitFetchStrategy, GitRef,
                                  FetcherConflict)
from spack.spec import Spec
from spack.stage import Stage
from spack.version import ver
from spack.util.executable import which
from spack.version import ver

pytestmark = pytest.mark.skipif(
    not which('git'), reason='requires git to be installed')


_mock_transport_error = 'Mock HTTP transport error'


@pytest.fixture(params=[None, '1.8.5.2', '1.8.5.1',
                        '1.7.10', '1.7.1', '1.7.0'])
def git_version(request, monkeypatch):
    """Tests GitFetchStrategy behavior for different git versions.

    GitFetchStrategy tries to optimize using features of newer git
    versions, but needs to work with older git versions.  To ensure code
    paths for old versions still work, we fake it out here and make it
    use the backward-compatibility code paths with newer git versions.
    """
    git = which('git', required=True)
    real_git_version = (
        spack.fetch_strategy.GitFetchStrategy.version_from_git(git))

    if request.param is None:
        # Don't patch; run with the real git_version method.
        yield real_git_version
    else:
        test_git_version = ver(request.param)
        if test_git_version > real_git_version:
            pytest.skip("Can't test clone logic for newer version of git.")

        # Patch the fetch strategy to think it's using a lower git version.
        # we use this to test what we'd need to do with older git versions
        # using a newer git installation.
        def get_test_git_version(_cls, _git):
            return test_git_version
        monkeypatch.setattr(ConfiguredGit, '_get_git_version',
                            # Need to explicitly bind the function to the class for py2.
                            get_test_git_version.__get__(ConfiguredGit))
        yield test_git_version


@pytest.fixture
def mock_bad_git(monkeypatch):
    """
    Test GitFetchStrategy behavior with a bad git command for git >= 1.7.1
    to trigger a SpackError.
    """
    def bad_git(*args, **kwargs):
        """Raise a SpackError with the transport message."""
        raise spack.error.SpackError(_mock_transport_error)

    # Patch the fetch strategy to think it's using a git version that
    # will error out when git is called.
    bad_git = ConfiguredGit(bad_git, ver('1.7.1'))
    monkeypatch.setattr(ConfiguredGit, 'from_executable', lambda _: bad_git)
    yield


def test_bad_git(tmpdir, mock_bad_git):
    """Trigger a SpackError when attempt a fetch with a bad git."""
    testpath = str(tmpdir)

    with pytest.raises(spack.error.SpackError):
        fetcher = GitFetchStrategy(git='file:///not-a-real-git-repo')
        with Stage(fetcher, path=testpath):
            fetcher.fetch()


@pytest.mark.parametrize("type_of_test", ['master', 'branch', 'tag', 'commit'])
@pytest.mark.parametrize("secure", [True, False])
def test_git_fetch(type_of_test,
                   secure,
                   mock_git_repository,
                   config,
                   mutable_mock_repo,
                   git_version,
                   patch_from_version_directive_for_git_ref):
    """Performs multiple operations in series for a given refspec.

    1. Fetch the repo using a git fetch strategy constructed with
       supplied args (they depend on type_of_test).
    2. Check if the test_file is in the checked out repository.
    3. Assert that the repository is at the revision supplied.
    4. Add and remove some files, then reset the repo, and
       ensure it's all there again.
    """
    # Retrieve the right test parameters
    t = mock_git_repository.checks[type_of_test]
    h = mock_git_repository.hash

    if type_of_test == 'master':
        patch_from_version_directive_for_git_ref(GitRef.branch('master'))
    elif type_of_test == 'branch':
        patch_from_version_directive_for_git_ref(GitRef.branch(t.revision))
    elif type_of_test == 'tag':
        patch_from_version_directive_for_git_ref(GitRef.tag(t.revision))
    else:
        assert type_of_test == 'commit', type_of_test
        patch_from_version_directive_for_git_ref(GitRef.commit(t.revision))

    # Construct the package under test
    spec = Spec('git-test')
    spec.concretize()
    pkg = spack.repo.get(spec)
    pkg.versions[ver('git')] = t.args

    # Enter the stage directory and check some properties
    with pkg.stage:
        with spack.config.override('config:verify_ssl', secure):
            pkg.do_stage()

        with working_dir(pkg.stage.source_path):
            assert h('HEAD') == h(t.revision)

            file_path = os.path.join(pkg.stage.source_path, t.file)
            assert os.path.isdir(pkg.stage.source_path)
            assert os.path.isfile(file_path)

            os.unlink(file_path)
            assert not os.path.isfile(file_path)

            untracked_file = 'foobarbaz'
            touch(untracked_file)
            assert os.path.isfile(untracked_file)

        # A restage will delete the stage directory, so we need to get out of the above
        # working_dir() scope and then re-acquire it at the same path.
        with spack.config.override('config:verify_ssl', secure):
            pkg.do_restage()

        with working_dir(pkg.stage.source_path):
            assert not os.path.isfile(untracked_file)

            assert os.path.isdir(pkg.stage.source_path)
            assert os.path.isfile(file_path)

            assert h('HEAD') == h(t.revision)


@pytest.mark.parametrize("type_of_test", ['branch', 'commit'])
def test_debug_fetch(mock_packages, type_of_test, mock_git_repository, config):
    """Fetch the repo with debug enabled."""
    # Retrieve the right test parameters
    t = mock_git_repository.checks[type_of_test]

    # Construct the package under test
    spec = Spec('git-test')
    spec.concretize()
    pkg = spack.repo.get(spec)
    pkg.versions[ver('git')] = t.args

    # Fetch then ensure source path exists
    with pkg.stage:
        with spack.config.override('config:debug', True):
            pkg.do_fetch()
            assert os.path.isdir(pkg.stage.source_path)


def test_needs_stage():
    """Trigger a NoStageError when attempt a fetch without a stage."""
    with pytest.raises(spack.fetch_strategy.NoStageError,
                       match=r"set_stage.*before calling fetch"):
        fetcher = GitFetchStrategy(git='file:///not-a-real-git-repo', branch='master')
        fetcher.fetch()


@pytest.mark.parametrize("get_full_repo", [True, False])
def test_get_full_repo(get_full_repo, git_version, mock_git_repository,
                       config, mutable_mock_repo):
    """Ensure that we can clone a full repository."""

    if git_version < ver('1.7.1'):
        pytest.skip('Not testing get_full_repo for older git {0}'.
                    format(git_version))

    secure = True
    type_of_test = 'tag-branch'

    t = mock_git_repository.checks[type_of_test]

    spec = Spec('git-test')
    spec.concretize()
    pkg = spack.repo.get(spec)
    args = copy.copy(t.args)
    args['get_full_repo'] = get_full_repo
    pkg.versions[ver('git')] = args

    with pkg.stage:
        with spack.config.override('config:verify_ssl', secure):
            pkg.do_stage()

            with working_dir(pkg.stage.source_path):
                # `git branch` will occasionally print out a '+' at the start of
                # a branch, which isn't relevant for us and appears to change across git
                # versions.
                branches\
                    = [re.sub(r'^\+', ' ', branch_line)
                       for branch_line in
                       mock_git_repository.git_exe('branch', '-a', output=str)
                       .splitlines()]
                git_log_lines\
                    = mock_git_repository.\
                    git_exe('log', '--graph',
                            '--pretty=format:%h -%d %s (%ci) <%an>',
                            '--abbrev-commit',
                            output=str).splitlines()

                commits = [re.sub(r'\* ([a-z0-9]+) .*$', r'\1', log_line)
                           for log_line in git_log_lines]

        if get_full_repo:
            assert branches[0:2] == ['* (no branch)', '  master']
            assert branches[2].startswith('  spack-internal-'), branches
            assert branches[3:] == ['  tag-branch', '  test-branch']
            assert len(commits) == 2
        else:
            assert branches[0] == '* (no branch)'
            assert branches[1].startswith('  spack-internal-'), branches
            assert branches[2:] == ['  tag-branch']
            assert len(commits) == 2


@pytest.mark.disable_clean_stage_check
@pytest.mark.parametrize("submodules", [True, False])
def test_gitsubmodule(submodules, mock_git_repository, config,
                      mutable_mock_repo):
    """
    Test GitFetchStrategy behavior with submodules
    """
    type_of_test = 'tag-branch'
    t = mock_git_repository.checks[type_of_test]

    # Construct the package under test
    spec = Spec('git-test')
    spec.concretize()
    pkg = spack.repo.get(spec)
    args = copy.copy(t.args)
    args['submodules'] = submodules
    pkg.versions[ver('git')] = args
    pkg.do_stage()
    with working_dir(pkg.stage.source_path):
        for submodule_count in range(2):
            file_path = os.path.join(pkg.stage.source_path,
                                     'third_party/submodule{0}/r0_file_{0}'
                                     .format(submodule_count))
            if submodules:
                assert os.path.isfile(file_path)
            else:
                assert not os.path.isfile(file_path)


@pytest.mark.disable_clean_stage_check
def test_gitsubmodules_delete(mock_git_repository, config, mutable_mock_repo):
    """
    Test GitFetchStrategy behavior with submodules_delete
    """
    type_of_test = 'tag-branch'
    t = mock_git_repository.checks[type_of_test]

    # Construct the package under test
    spec = Spec('git-test')
    spec.concretize()
    pkg = spack.repo.get(spec)
    args = copy.copy(t.args)
    args['submodules'] = True
    args['submodules_delete'] = ['third_party/submodule0',
                                 'third_party/submodule1']
    pkg.versions[ver('git')] = args
    pkg.do_stage()
    with working_dir(pkg.stage.source_path):
        file_path = os.path.join(pkg.stage.source_path,
                                 'third_party/submodule0')
        assert not os.path.isdir(file_path)
        file_path = os.path.join(pkg.stage.source_path,
                                 'third_party/submodule1')
        assert not os.path.isdir(file_path)


def test_invalid_git_fetch_strategy_parsing():
    """Trigger a FetcherConflict when parsing version() is ambiguous or malformed."""
    # Does not raise.
    _ = GitFetchStrategy(git='file:///not-a-real-git-repo', branch='master',
                         submodules=True, submodules_delete=['something'],
                         get_full_repo=True)
    _ = GitFetchStrategy(git='file:///not-a-real-git-repo', branch='master',
                         submodules=False, submodules_delete=None,
                         get_full_repo=False)
    _ = GitFetchStrategy(git='file:///not-a-real-git-repo', version_name='master',
                         submodules=False, submodules_delete=None,
                         get_full_repo=False)
    # Raises for invalid version() specifications.
    with pytest.raises(FetcherConflict, match=r"Exactly one of commit, tag, or branch"):
        GitFetchStrategy(git='file:///not-a-real-git-repo')
    with pytest.raises(FetcherConflict, match=r"Exactly one of commit, tag, or branch"):
        GitFetchStrategy(git='file:///not-a-real-git-repo', tag='asdf', branch='fdsa')
    with pytest.raises(FetcherConflict, match=r"Exactly one of commit, tag, or branch"):
        GitFetchStrategy(git='file:///not-a-real-git-repo', commit='asdf', tag='fdsa')
    with pytest.raises(FetcherConflict, match=r"Exactly one of commit, tag, or branch"):
        GitFetchStrategy(git='file:///not-a-real-git-repo', tag='asdf', branch='fdsa')
    # Raises for invalid information on how to prepare the checkout for the spack stage.
    with pytest.raises(FetcherConflict, match=r"submodules=.*must be a bool"):
        GitFetchStrategy(git='file:///not-a-real-git-repo', branch='master',
                         submodules='True')
    with pytest.raises(FetcherConflict,
                       match=r"submodules_delete=.*must be a list of str"):
        GitFetchStrategy(git='file:///not-a-real-git-repo', branch='master',
                         submodules_delete='something')
    with pytest.raises(FetcherConflict, match=r"get_full_repo=.*must be a bool"):
        GitFetchStrategy(git='file:///not-a-real-git-repo', branch='master',
                         get_full_repo='True')
