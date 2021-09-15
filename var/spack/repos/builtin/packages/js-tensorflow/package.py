# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from llnl.util.filesystem import working_dir

from spack.build_systems.npm import NpmPackage
from spack.util.executable import which


class JsTensorflow(NpmPackage):
    """A WebGL accelerated JavaScript library for training and deploying ML models."""

    homepage = "https://www.tensorflow.org/js"
    # npm      = "tfjs-3.9.0.tgz"
    url      = "https://github.com/tensorflow/tfjs/archive/tfjs-v3.9.0.tar.gz"

    maintainers = ['cosmicexplorer']

    version('3.9.0', sha256='54df817fa668d228495a35c5a714ac015bf06a189cf430d2e42cc3b132076b7a')
