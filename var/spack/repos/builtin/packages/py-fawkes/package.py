# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack import *


class PyFawkes(PythonPackage):
    """Fawkes is a privacy protection system developed by researchers at
    SANDLab, University of Chicago."""

    homepage = "https://sandlab.cs.uchicago.edu/fawkes/"
    pypi = "fawkes/fawkes-1.0.4.tar.gz"
    git = "https://github.com/Shawn-Shan/fawkes"

    maintainers = ['cosmicexplorer']

    version('master', branch='master')
    version('1.0.4', sha256='a2e899806b6e7913b3adca47e76e32728748de41524a18086b02782e248cc62f')

    variant('cuda', default=False,
            description='Enable GPU computation on CUDA platforms using TensorFlow.')

    depends_on('python@3.5:', type=('build', 'run'))
    depends_on('py-setuptools', type='build')
    depends_on('py-numpy@1.19.5:', type='run')
    depends_on('py-keras@2.4.3', type='run')
    depends_on('py-pillow@7.0.0:', type='run')
    depends_on('py-bleach@2.1.0:', type='run')
    with when('+cuda'):
        depends_on('py-tensorflow@2.4.1+cuda', type='run')
        depends_on('py-mtcnn+cuda', type='run')
    with when('~cuda'):
        depends_on('py-tensorflow@2.4.1~cuda', type='run')
        depends_on('py-mtcnn~cuda', type='run')
