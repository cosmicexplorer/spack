target(
    name='heavier-test-deps',
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'var/spack/repos/builtin',
    ],
)

python_tests(
    sources=[
        '**/*.py',
        '!**/__init__.py',
        '!build_env.py',
        '!ci.py',
        '!commands.py',
        '!config.py',
        '!deprecate.py',
        '!dev_build.py',
        '!env.py',
        '!external.py',
        '!flake8.py',
        '!info.py',
        '!install.py',
        '!is_git_repo.py',
        '!list.py',
        '!load.py',
        '!pkg.py',
        '!test.py',
        '!url.py',
        '!unit_test.py',
        '!versions.py',
        '!view.py',
    ],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
    ],
)

python_tests(
    name='needs-zlib',
    sources=['build_env.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'var/spack/repos/builtin/packages/zlib',
    ]
)

python_tests(
    name='long-running',
    sources=['ci.py', 'deprecate.py', 'dev_build.py', 'env.py', 'load.py', 'view.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
    ],
    tags = {'long-running'},
)

python_tests(
    name='needs-completion',
    sources=['commands.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'share/spack',
    ],
)

python_tests(
    name='needs-mpileaks',
    sources=['config.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'lib/spack/spack/test:mpileaks-deps',
    ],
)

python_tests(
    name='needs-cmake-gcc-openssl',
    sources=['external.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'var/spack/repos/builtin/packages/cmake',
        'var/spack/repos/builtin/packages/gcc',
        'var/spack/repos/builtin/packages/openssl',
    ]
)

python_tests(
    name='needs-full-git-repo',
    sources=['flake8.py', 'is_git_repo.py', 'test.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
    ],
    # TODO: Use --local-execution-root-dir to do this safely! Create a temp dir, make
    # a symbolic link to the spack .git dir, then use the temp dir as the execution
    # root dir!
    tags = {'needs-full-git-repo'},
)

python_tests(
    name='needs-trilinos',
    sources=['info.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'lib/spack/spack/test:mpi-deps',
        'lib/spack/spack/test:python-deps',
        'var/spack/repos/builtin/packages/boost',
        'var/spack/repos/builtin/packages/cloverleaf3d',
        'var/spack/repos/builtin/packages/dealii',
        'var/spack/repos/builtin/packages/hdf5',
        'var/spack/repos/builtin/packages/kokkos',
        'var/spack/repos/builtin/packages/trilinos',
        'var/spack/repos/builtin/packages/xsdk',
    ]
)

python_tests(
    name='needs-cloverleaf3d-libelf-numpy',
    sources=['list.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'lib/spack/spack/test:python-deps',
        'var/spack/repos/builtin/packages/cloverleaf3d',
        'var/spack/repos/builtin/packages/hdf5',
        'var/spack/repos/builtin/packages/libelf',
        'var/spack/repos/builtin/packages/mfem',
        'var/spack/repos/builtin/packages/nek5000',
        'var/spack/repos/builtin/packages/perl-file-copy-recursive',
        'var/spack/repos/builtin/packages/py-numpy',
    ]
)

python_tests(
    name='needs-some-git-info',
    sources=['pkg.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        '//:git-files',
    ]
)

python_tests(
    name='needs-every-package',
    sources=['url.py'],
    dependencies=[
        ':heavier-test-deps',
    ],
    tags = {'long-running'},
)

python_tests(
    name='needs-every-package-and-full-git-repo',
    sources=['install.py'],
    dependencies=[
        ':heavier-test-deps',
    ],
    tags = {'long-running', 'needs-full-git-repo', 'temporarily-broken-todo'},
)


python_tests(
    name='needs-other-source-files',
    # TODO: unit-test is still broken!
    sources=['unit_test.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'lib/spack/spack/test:spec-semantics',
    ],
    tags = {'temporarily-broken-todo'},
)

python_tests(
    name='needs-opengl-graphviz',
    sources=['versions.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'var/spack/repos/builtin/packages/bzip2',
        'var/spack/repos/builtin/packages/converge',
        'var/spack/repos/builtin/packages/graphviz',
        'var/spack/repos/builtin/packages/opengl',
        'var/spack/repos/builtin/packages/zlib',
    ]
)
