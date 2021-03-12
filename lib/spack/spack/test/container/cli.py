# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)
import llnl.util.filesystem as fs
import spack.main
import spack.container


containerize = spack.main.SpackCommand('containerize')


image_data = spack.container.image_data()


class Wrapper(object):
    def __init__(self, inner):
        self.inner = inner

    def __call__(self):
        return self.inner


def test_command(default_config, container_config_dir, capsys, monkeypatch):
    monkeypatch.setattr(spack.container, 'image_data', Wrapper(image_data))
    with capsys.disabled():
        with fs.working_dir(container_config_dir):
            output = containerize()
    assert 'FROM spack/ubuntu-bionic' in output
