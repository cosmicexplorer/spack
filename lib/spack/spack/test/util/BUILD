python_tests(
    sources=['*.py', '!editor.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
    ],
)

python_tests(
    # TODO: This still fails!
    name='needs-idk',
    sources=['editor.py'],
    dependencies=[
        'lib/spack/spack/test:basic-test-deps',
    ],
    tags = {'temporarily-broken-todo'},
)
