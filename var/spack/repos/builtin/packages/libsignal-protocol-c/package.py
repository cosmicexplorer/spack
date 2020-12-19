# Copyright 2013-2020 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack import *


class LibsignalProtocolC(CMakePackage):
    """Cryptographic library implementing the Signal Protocol."""

    homepage = "https://github.com/signalapp/libsignal-protocol-c"
    url      = "https://github.com/signalapp/libsignal-protocol-c/archive/v2.3.3.tar.gz"

    version('2.3.3', sha256='c22e7690546e24d46210ca92dd808f17c3102e1344cd2f9a370136a96d22319d')
