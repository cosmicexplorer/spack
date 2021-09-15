# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack import *


class PyMtcnn(PythonPackage):
    """Implementation of the MTCNN face detector for Keras in Python3.4+. It is written from
    scratch, using as a reference the implementation of MTCNN from David Sandberg (FaceNet’s MTCNN)
    in Facenet. It is based on the paper Zhang, K et al. (2016)."""

    homepage = "https://github.com/ipazc/mtcnn"
    pypi = "mtcnn/mtcnn-0.1.1.tar.gz"
    git = "https://github.com/ipazc/mtcnn.git"

    maintainers = ['cosmicexplorer']

    version('master', branch='master')
    version('0.1.1', sha256='d0957274584be62cb83d4a089041f8ee3cf3b1893e45f01ed3356f94a381302b')

    variant('cuda', default=False,
            description='Enable GPU computation on CUDA platforms with openCV.')

    depends_on('python@3.4:', type=('build', 'run'))
    depends_on('py-setuptools', type='build')
    depends_on('py-keras@2.0.0:', type='run')

    with when('+cuda'):
        depends_on('opencv@4.1.0:+python3+cuda', type='run')
    with when('~cuda'):
        depends_on('opencv@4.1.0:+python3~cuda', type='run')
