# Copyright 2013-2022 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack import *


class Mailutils(AutotoolsPackage):
    """Mailutils is a swiss army knife of electronic mail handling.
    It offers a rich set of utilities and daemons for processing e-mail."""

    homepage = "https://mailutils.org/"
    url      = "https://ftp.gnu.org/gnu/mailutils/mailutils-3.13.tar.gz"

    maintainers = ['cosmicexplorer']

    version('3.13', sha256='41234389452805e5a47cec4fd57c61feee0cdaa6de94d0ded0cd33e778f58de2')

    depends_on('libiconv')
    depends_on('gettext')
    depends_on('readline')
    depends_on('gnutls')
    depends_on('gdbm')
    depends_on('berkeley-db')
    depends_on('guile')
    depends_on('texinfo', type='build')
    depends_on('ncurses+termlib')

    def configure_args(self):
        return [
            'LIBS=-ltinfo',
            '--with-dbm',
            '--with-gdbm',
            '--with-berkeley-db',
            '--with-guile',
        ]
