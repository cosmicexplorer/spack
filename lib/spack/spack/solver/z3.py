from __future__ import absolute_import, print_function

import code
import collections
import itertools
import re
from contextlib import contextmanager
# from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple, Union

from z3 import *

from spack.solver.asp import Timer as _Timer


class Timer(_Timer):
    def __init__(self):
        _Timer.__init__(self)
        self.superphase = ''

    def phase(self, name, sep='/'):
        return _Timer.phase(self, self.superphase + sep + name)

    @contextmanager
    def nested_phase(self, subname, sep='/'):
        orig = self.superphase
        self.superphase += sep
        self.superphase += subname
        try:
            self.phase('', sep=sep)
            yield self
        finally:
            self.superphase = orig
            self.phase('')

### Generate the model.

# From ExprRef.__doc__ in z3.py:
"""Constraints, formulas and terms are expressions in Z3.

Expressions are ASTs. Every expression has a sort.
There are three main kinds of expressions:
function applications, quantifiers and bounded variables.
A constant is a function application with 0 arguments.
For quantifier free problems, all expressions are
function applications.
"""
Z3Expr = ExprRef


RepoSort, repos = EnumSort('RepoSort', ['spack', 'pypi', 'sonatype'])
(spack, pypi, sonatype) = repos
cur_repo = Const('cur_repo', RepoSort)

PackageNameSort, names = EnumSort('PackageNameSort', ['a', 'b', 'c'])
(a, b, c) = names

name_try_repo_map = {
    spack: [a, b],
    pypi: [c],
    sonatype: [],
}

# Versions need to be normalized to the semver 3-tuple to be lexicographically sorted!
# TODO: We currently allow "trailing garbage" in the string, captured in the 4th group, without
# interpreting it.
semver_input_versions_pattern = re.compile(r'^([0-9]+)((\.[0-9]+)*)(.*?)$')

def version_columns(version_string):
    # type: (str) -> Tuple[int, int, int]
    semver_match = semver_input_versions_pattern.match(version_string)
    if semver_match:
        major = int(semver_match.group(1))
        subs_string = semver_match.group(2)
        # Remove initial '.', then split by the other '.'s.
        subs = [int(sub) for sub in subs_string[1:].split('.')]
        if len(subs) < 2:
            # Pad out to three zeros.
            subs = [0, 0]
        # Otherwise, capture only the first 3 numeric versions.
        return (major,) + tuple(subs[:2])
    else:
        raise TypeError('received unknown version string: {}'.format(version_string))

Semver3Sort, mk_version, (ver1, ver2, ver3) = TupleSort(
    'Semver3Sort',
    [IntSort(), IntSort(), IntSort()])

VariantNameSort, variant_names = EnumSort('VariantNameSort', ['release', 'debug', 'idk'])
(release, debug, idk) = variant_names

default_variants_try_map = {
    release: (False, True),
    debug: (0, 1),
    idk: ('idk1', 'idk2'),
}

variant_single_value = Function('variant_single_value', VariantNameSort, BoolSort())

VariantSourceSort, variant_sources = EnumSort('VariantSourceSort', ['spec', 'py', 'yaml'])
(spec, py, yaml) = variant_sources

DepSpecStrategySort, strategies = EnumSort('DepSpecStrategySort', ['low', 'high', 'neither'])
(low, high, neither) = strategies

DepSpecSort, mk_dep_spec, (get_low, get_high, get_strategy) = TupleSort(
    'DepSpecSort',
    [Semver3Sort, Semver3Sort, DepSpecStrategySort],
)

variant_try_value_map = {
    release: [(None, py, False), True],
    debug: [(None, yaml, 0), 3],
    idk: [(None, py, 'idk1'), (None, yaml, 'idk2'), 'idk3'],
}
variant_for_spec_try_map = {
    a: {
        '0.0.1': {
            'variants': [None, release, (release, idk), debug],
            'dependencies': {
                b: {
                    'low': '1.0.0',
                    'high': '2.0.0',
                    'prefer': low,
                },
            },
        },
        '1.0.0': {
            'variants': [None, release, (release, idk), debug],
            'dependencies': {
                b: {
                    'low': '1.0.0',
                    'high': '2.0.0',
                    'prefer': low,
                },
            },
        },
        '1.5.2': {
            'variants': [None, debug],
            'dependencies': {
                b: {
                    'low': '2.1.3',
                    'high': '2.1.3',
                    'prefer': neither,
                },
            },
            'conflicts': {
                c: '3.1.3',
            },
        },
    },
    b: {
        '1.0.0': {
            'variants': [None, debug],
            'dependencies': {
                c: {
                    'low': '2.0.0',
                    'high': '3.0.0',
                    'prefer': low,
                },
            },
        },
        '1.0.1': {
            'variants': [None, debug],
            'dependencies': {
                c: {
                    'low': '3.0.0',
                    'high': '4.0.0',
                    'prefer': low,
                },
            },
        },
        '2.0.0': {
            'variants': [None, debug, idk],
            'dependencies': {
                c: {
                    'low': '3.1.2',
                    'high': '3.1.2',
                    'prefer': neither,
                },
            },
            'conflicts': {
                c: '3.0.0',
            },
        },
        '2.1.3': {
            'variants': [None, debug],
            'dependencies': {
                c: {
                    'low': '3.1.3',
                    'high': '3.1.3',
                    'prefer': neither,
                },
            },
        },
    },
    c: {
        '2.3.5': {
            'variants': [None, idk],
            'dependencies': {},
        },
        '3.0.0': {
            'variants': [None, idk, debug],
            'dependencies': {},
        },
        '3.1.2': {
            'variants': [None, idk],
            'dependencies': {},
        },
        '3.1.3': {
            'variants': [None, idk, debug],
            'dependencies': {},
        },
    },
}

package_version_try_map = dict(
    (k, [version_columns(v) for v, _ in ver.items()])
    for k, ver in variant_for_spec_try_map.items()
)

_ExplicitValue = Datatype('ExplicitValueSort')
_ExplicitValue.declare('integer', ('value', IntSort()))
_ExplicitValue.declare('string', ('value', StringSort()))
_ExplicitValue.declare('boolean', ('value', BoolSort()))
ExplicitValueSort = _ExplicitValue.create()

_VariantValue = Datatype('VariantValue')
_VariantValue.declare('none')
_VariantValue.declare('some', ('inner', ExplicitValueSort))
VariantValueSort = _VariantValue.create()

cur_variant_value = Const('cur_variant_value', VariantValueSort)


def as_variant_value(arg):
    if arg is None:
        return VariantValueSort.none
    if isinstance(arg, bool):
        return VariantValueSort.some(ExplicitValueSort.boolean(BoolVal(arg)))
    if isinstance(arg, int):
        return VariantValueSort.some(ExplicitValueSort.integer(IntVal(arg)))
    if isinstance(arg, str):
        return VariantValueSort.some(ExplicitValueSort.string(StringVal(arg)))
    print('using {} directly...'.format(arg))
    return arg

def as_variant_source(arg):
    if isinstance(arg, tuple):
        if len(arg) == 2:
            assert arg[1] in variant_sources
            return arg[1]
        if len(arg) == 3:
            assert arg[1] in variant_sources
            return arg[1]
    assert 'should never get here2!'


def as_variant_description(**kwargs):
    inner_values = []
    for name, value in kwargs.items():
        if value is None:
            continue
        if isinstance(value, bool):
            inner_values.append("{}{}".format(('+' if value else '~'),
                                              name))
        else:
            inner_values.append("+{}={}".format(name, value))
    inner = ', '.join(inner_values)
    return "[{}]".format(inner)

VariantValueMapSort = Datatype('VariantValueMapSort')
VariantValueMapSort.declare('empty')
VariantValueMapSort.declare('multi',
                            ('name', VariantNameSort),
                            ('value', VariantValueSort),
                            ('cdr', VariantValueMapSort))
VariantValueMapSort = VariantValueMapSort.create()

def as_variant_map(variant_pairs):
    # print('variant_pairs: {}'.format(variant_pairs))
    cur_map = VariantValueMapSort.empty
    for name, value in variant_pairs:
        if name is None:
            continue
        value = process_variant_for_spec(value)[0]
        value = as_variant_value(value)
        tup = (
            name,
            value,
            cur_map,
        )
        # print(tup)
        cur_map = VariantValueMapSort.multi(
            name,
            value,
            cur_map,
        )
    return cur_map

variant_for_map = Function('variant_for_map',
                           VariantValueMapSort, VariantNameSort, VariantValueSort)

SinglePackageIdentity, mk_spec, (get_spec_name, get_spec_version, get_spec_variants) = TupleSort(
    'SinglePackageIdentity',
    [PackageNameSort, Semver3Sort, VariantValueMapSort])
cur_pkg = Const('cur_pkg', SinglePackageIdentity)

dependency_matches_version_spec = Function('dependency_matches_version_spec',
                                           DepSpecSort, Semver3Sort, BoolSort())
use_this_dependency = Function('use_this_dependency',
                                              SinglePackageIdentity, SinglePackageIdentity, BoolSort())

variant_for_spec = Function('variant_for_spec', SinglePackageIdentity, VariantNameSort, VariantValueSort)
get_dep_specs = Function('get_dep_specs', SinglePackageIdentity, SetSort(DepSpecSort))

variant_get_value = Function('variant_get_value', SinglePackageIdentity, VariantNameSort, VariantValueSort)
variant_get_source = Function('variant_get_source', SinglePackageIdentity, VariantNameSort, VariantSourceSort)
spec_has_variant = Function('spec_has_variant', SinglePackageIdentity, VariantNameSort, BoolSort())

use_package = Function('use_package', SinglePackageIdentity, BoolSort())

repo_has_package = Function('repo_has_package', SinglePackageIdentity, RepoSort, BoolSort())
use_repo_package = Function('use_repo_package', SinglePackageIdentity, RepoSort, BoolSort())

def process_variant_for_spec(variant_value):
    if isinstance(variant_value, tuple):
        assert len(variant_value) == 3
        assert variant_value[0] is None
        real_value = variant_value[2]
        source = variant_value[1]
    else:
        real_value = variant_value
        source = spec
    return (real_value, source)

def static_or_quantified_assumptions(all_packages):
    """Explicitly enumerate some function values over all packages and all variant names."""
    all_packages = frozenset(all_packages)
    assumptions = []

    for pkg in all_packages:
        # Assume all specified variants are of matching value.
        for dep_pkg in all_packages:
            if not dep_pkg == pkg:
                for v_name in variant_names:
                    assumptions.append(
                        Implies(
                            # ...in all *transitive* dependencies.
                            And([use_package(pkg),
                                 use_package(dep_pkg),
                                 spec_has_variant(pkg, v_name),
                                 spec_has_variant(dep_pkg, v_name)]),
                            (variant_get_value(pkg, v_name) == variant_get_value(dep_pkg, v_name)),
                        )
                    )

        # Fill in variant source specifications.
        for v_name in variant_names:
            assumptions.append(
                (variant_for_spec(pkg, v_name) == (
                           variant_for_map(get_spec_variants(pkg), v_name)))
            )
            assumptions.append(
                Implies((variant_get_source(pkg, v_name) == py),
                        (variant_get_value(pkg, v_name) == (
                            as_variant_value(default_variants_try_map[v_name][0]))))
            )
            assumptions.append(
                Implies((variant_get_source(pkg, v_name) == yaml),
                        (variant_get_value(pkg, v_name) == (
                            as_variant_value(default_variants_try_map[v_name][1]))))
            )
            assumptions.append(
                Implies((variant_get_source(pkg, v_name) == spec),
                               (variant_get_value(pkg, v_name) == (
                                   variant_for_spec(pkg, v_name))))
            )

    return assumptions

def build_assumptions(with_conflict=False):
    assumptions = []  # type: List[Z3Expr]

    pkg_mapping = {}
    pkg_inverse_mapping = collections.defaultdict(lambda: collections.defaultdict(list))
    pkg_repos = collections.defaultdict(list)

    def all_variants(pkg_name, v_tup):
        # type: (PackageNameSort, Tuple[int, int, int]) -> Iterator[SinglePackageIdentity]
        for pkg, _vmap in pkg_inverse_mapping[pkg_name][v_tup]:
            yield pkg

    all_packages_by_name = {}

    deps_table = collections.defaultdict(list)
    conflicts_table = collections.defaultdict(lambda: collections.defaultdict(list))
    variants_table = collections.defaultdict(dict)

    # Iterate over every package!
    for name, version_map in variant_for_spec_try_map.items():
        for version_string, dep_var_spec in version_map.items():
            v_tup = version_columns(version_string)
            version = mk_version(*v_tup)

            for all_variant_names in dep_var_spec['variants']:
                if all_variant_names is None:
                    all_variant_names = []
                else:
                    if not isinstance(all_variant_names, tuple):
                        all_variant_names = (all_variant_names,)

                variant_specs = [
                    dict(zip(all_variant_names,
                             [process_variant_for_spec(v_val) for v_val in values]))
                    for values in
                    itertools.product(*tuple(variant_try_value_map[n] for n in all_variant_names))
                ]
                # print(variant_specs)

                for v_spec_sourced in variant_specs:
                    v_spec = dict((k, v[0]) for k, v in v_spec_sourced.items())
                    variant_value_map = as_variant_map(v_spec.items())
                    v_sources = dict((k, v[1]) for k, v in v_spec_sourced.items())
                    # print(v_spec)
                    # print(v_sources)

                    # Fill in variant values for this map.
                    for v_name, v_value in v_spec.items():
                        v_value = as_variant_value(v_value)
                        assumptions.extend([
                            (variant_for_map(variant_value_map, v_name) == v_value),
                        ])


                    pkg = mk_spec(name, version, variant_value_map)
                    variants_table[pkg] = v_spec.copy()
                    # Fill in the appropriate variant sources for this package.
                    for v_name, v_source in v_sources.items():
                        assumptions.append(variant_get_source(pkg, v_name) == v_source)

                    # Fill in the named variants in this spec.
                    v_keys = list(v_spec.keys())
                    not_v_keys = (set(variant_names) - set(v_keys))
                    assumptions.extend([
                        spec_has_variant(pkg, v_name)
                        for v_name in v_keys
                    ] + [
                        Not(spec_has_variant(pkg, not_v_name))
                        for not_v_name in not_v_keys
                    ])

                    kwarg_spec = dict((n.sexpr(), v) for n, v in v_spec.items())
                    variant_description = as_variant_description(**kwarg_spec)

                    var_string = ("{name}=={version}+{var}"
                                  .format(name=name,
                                          version=version_string,
                                          var=variant_description))
                    pkg_bool_var = Bool(var_string)
                    assumptions.append(use_package(pkg) == pkg_bool_var)
                    all_packages_by_name[var_string] = (pkg, pkg_bool_var)
                    pkg_mapping[pkg] = (name, version, pkg_bool_var, variant_value_map)
                    pkg_inverse_mapping[name][v_tup].append((pkg, variant_value_map))

                    for repo in repos:
                        if name in name_try_repo_map[repo]:
                            assumptions.append(repo_has_package(pkg, repo))
                            pkg_repos[pkg].append(repo)
                        else:
                            assumptions.append(Not(repo_has_package(pkg, repo)))

                    deps = dep_var_spec['dependencies']
                    for dep_name, this_dep_spec in deps.items():
                        low_tup = version_columns(this_dep_spec['low'])
                        low_version = mk_version(*low_tup)
                        high_tup = version_columns(this_dep_spec['high'])
                        high_version = mk_version(*high_tup)
                        prefer_strategy = this_dep_spec['prefer']

                        dep_spec = mk_dep_spec(low_version, high_version, prefer_strategy)

                        deps_table[pkg].append((dep_name, dep_spec, low_tup, high_tup, prefer_strategy))

                    if with_conflict:
                        conflicts = dep_var_spec.get('conflicts', {})
                        if not conflicts:
                            continue
                        variants = dep_var_spec.get('variants', [])
                        for p_name in names:
                            if p_name in conflicts:
                                conflicts_table[pkg][p_name].append((
                                    conflicts[p_name],
                                    variants,
                                ))

    # print(all_packages_by_name)
    all_packages = set()
    for _str, (pkg, _var) in all_packages_by_name.items():
        all_packages.add(pkg)

    for pkg, pkg_repos in pkg_repos.items():
        # The repo must contain the package in order for us to use it!
        assumptions.extend(
            Implies(
                use_repo_package(pkg, r),
                repo_has_package(pkg, r),
            )
            for r in pkg_repos
        )

        # Checking that any package we consume comes from exactly one repo.
        assumptions.extend(
            Implies(
                use_repo_package(pkg, r),
                Not(use_repo_package(pkg, s)),
            )
            for r, s in itertools.product(pkg_repos, repeat=2)
            if not s == r
        )

    for pkg, dep_specs in deps_table.items():
        for dep_name, dep_spec, low_end, high_end, strategy in dep_specs:
            low_version = mk_version(*low_end)
            high_version = mk_version(*high_end)
            # Here's where we provide dependency ranges!
            all_other_versions = package_version_try_map[dep_name]
            all_dep_packages = dict(
                (other, list(all_variants(dep_name, other)))
                for other in all_other_versions
            )
            assumptions.append(
                Implies(use_package(pkg), Or([
                    use_this_dependency(pkg, dep)
                    for _v_tup, all_deps in all_dep_packages.items()
                    for dep in all_deps
                ]))
            )
            for other, all_possible_deps in all_dep_packages.items():
                other_version = mk_version(*other)
                if strategy == low:
                    assumptions.append(
                        dependency_matches_version_spec(dep_spec, other_version) == (
                            (other >= low_end) and (other < high_end))
                    )
                elif strategy == high:
                    assumptions.append(
                        dependency_matches_version_spec(dep_spec, other_version) == (
                            (other <= high_end) and (other >  low_end))
                    )
                else:
                    assert strategy == neither
                    assumptions.append(
                        dependency_matches_version_spec(dep_spec, other_version) == (
                            (other == low_end) and (low_end == high_end) and (strategy == neither))
                    )

                for dep_pkg in all_possible_deps:
                    assumptions.append(
                        Implies(
                            use_this_dependency(pkg, dep_pkg),
                            dependency_matches_version_spec(dep_spec, other_version),
                        )
                    )
                    assumptions.append(
                        Implies(
                            use_this_dependency(pkg, dep_pkg),
                            And([
                                use_package(pkg),
                                use_package(dep_pkg),
                            ]),
                        )
                    )
                    # Assume only a single other package is chosen (for this particular package).
                    assumptions.extend(
                        Implies(
                            use_this_dependency(pkg, dep_pkg),
                            Not(use_this_dependency(pkg, not_dep)),
                        )
                        for not_dep in all_packages
                        if not not_dep == dep_pkg
                    )

                    # TODO: Here's where we try to make a set!
                    # assumptions.append(
                    #     Iff(
                    #         And([use_package(pkg), use_package(dep_pkg)]),
                    #         IsMember(dep_spec, get_dep_specs(pkg)),
                    #     )
                    # )

    # NB: This is just parsing the conflicts as specified in 'conflicts' in variant_for_spec_try_map!
    for pkg, conflicts in conflicts_table.items():
        for conflict_name, conflict_infos in conflicts.items():
            for conflict_version, child_variants in conflict_infos:
                c_v_tup = version_columns(conflict_version)

                for conflict_pkg in all_variants(conflict_name, c_v_tup):
                    assumptions.append(
                        Implies(
                            use_package(pkg),
                            Not(use_package(conflict_pkg)),
                        )
                    )

    assumptions.extend(static_or_quantified_assumptions(all_packages))


    return (assumptions, (pkg_mapping, pkg_inverse_mapping), conflicts_table, deps_table, all_packages_by_name)



### Execute the model.

def install_check(problems, timer=Timer(), solver=None):
    # type: (Iterable[Z3Expr], Optional[Solver]) -> Solver
    with timer.nested_phase('solve'):
        if solver is None:
            solver = Solver()
        result = solver.check(problems)
        truths = []
        unsat_core = []
        if result == sat:
            m = solver.model()
            for x in m:
                if is_true(m[x]):
                    # x is a Z3 declaration
                    # x() returns the Z3 expression
                    # x.name() returns a string
                    if x.name() == str(x()):
                        truth = x.name()
                    else:
                        truth = "name: {name} == value: {value}".format(name=x.name(), value=x())
                    truths.append(truth)
        elif result == unsat:
            unsat_core = solver.unsat_core()
        return (solver, result, truths, unsat_core)


def ground_check(grounder, solver=None, timer=Timer(), with_conflict=False):
    # type: (List[Z3Expr], Optional[Solver], bool) -> Tuple[BoolVarsDict, List[Bool], Solver]
    with timer.nested_phase('build assumptions'):
        (assumptions, pkg_mappings, conflicts_table, deps_table, all_packages_by_name) = build_assumptions(
            with_conflict=with_conflict)
    with timer.nested_phase('install check'):
        grounds_maybe = list(grounder(all_packages_by_name))
        print('grounds: {}'.format(grounds_maybe))
        all_exprs = assumptions + grounds_maybe
        (s, result, truths, unsat_core) = install_check(all_exprs, timer=timer, solver=solver)
        if result == sat:
            print('TRUTHS:\n{}'.format('\n'.join(truths)))
        elif result == unknown:
            print('UNKNOWN:\n{}'.format(s.reason_unknown()))
        elif result == unsat:
            print('UNSAT_CORE():\n{}'.format(s.unsat_core()))
        else:
            raise OSError('unrecognized result {}'.format(result))
        return (s, all_exprs, pkg_mappings, result, truths, unsat_core, conflicts_table, grounds_maybe, deps_table)


def solve(timer=Timer(), interact=False):
    # TODO: this only makes it fail to find solutions for all tactics I've tried.
    # robust_tactic = Then(
    #                      Tactic('macro-finder'),
    #                      Tactic('smt'),
    #                      Tactic('symmetry-reduce'),
    #                      Tactic('smt'),
    # )

    with timer.nested_phase('solve 1'):
        s1, e1, m1, r1, tr1, u1, c1, g1, dt1 = ground_check((lambda by_name: [by_name['a==1.5.2+[+debug=0]'][1]]),
                                                            timer=timer,
                                                            # solver=robust_tactic.solver(),
                                                            with_conflict=False)
        with timer.nested_phase('check 1'):
            if not r1 == sat:
                if interact:
                    print('ERROR: NOT SAT! SHOULD BE!')
                    code.interact(local=locals())
                else:
                    assert r1 == sat, r1

    with timer.nested_phase('solve 2'):
        s2, e2, m2, r2, tr2, u2, c2, g2, dt2 = ground_check((lambda by_name: [by_name['a==1.5.2+[+debug=0]'][1]]),
                                                            timer=timer,
                                                            # solver=robust_tactic.solver(),
                                                            with_conflict=True)
        with timer.nested_phase('check 2'):
            # TODO: make this correct!
            if not r2 == unsat:
                if interact:
                    print('ERROR: NOT \'unsat\'! SHOULD  BE!')
                    code.interact(local=locals())
                else:
                    assert r2 == unsat

    timer.write()

    if interact:
        code.interact(local=locals())

if __name__ == '__main__':
    solve(interact=True)
