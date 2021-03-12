target(
    name='heavier-test-deps',
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
        'var/spack/repos/builtin',
    ],
)

python_tests(
    sources=['**/*.py'],
    dependencies=[
        ':heavier-test-deps',
    ],
)
