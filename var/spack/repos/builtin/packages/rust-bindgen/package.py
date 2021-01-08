# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack import *
import os


class RustBindgen(Package):
    """The rust programming language toolchain"""
    homepage = "http://www.rust-lang.org"
    url = "https://github.com/rust-lang/rust-bindgen/archive/v0.56.0.tar.gz"

    version('0.20.5', sha256='4f5236e7979d262c43267afba365612b1008b91b8f81d1efc6a8a2199d52bb37')
    version('0.56.0', sha256='1bff9abe671cd99c74510f0121fb5a1c250a311dc518f9528507444001f6b929')

    extends("rust")
    depends_on("llvm")

    def install(self, spec, prefix):
        env = dict(os.environ)
        env['LIBCLANG_PATH'] = os.path.join(spec['llvm'].prefix, 'lib')
        cargo = which('cargo')

        # TODO: make a 'cargo' build system!
        # assert 'cargo' in spec
        # spec['cargo'].version for --path .!
        cargo('install', '--path', '.', '--root', prefix, env=env)
