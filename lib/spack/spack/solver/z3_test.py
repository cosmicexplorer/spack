from __future__ import absolute_import, print_function

import code
import collections
import itertools
# from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple, Union

from z3 import *


# Z3Expr = Union[Bool, And, Or, Not, Implies]

def DependsOn(pack, deps):
    # type: (SpecSort, Iterable[SpecSort]) -> Z3Expr
    return And([ Implies(use_package(pack), use_package(dep)) for dep in deps ])


def Conflict(packs):
    # type: (Iterable[Z3Expr]) -> Z3Expr
    return Or([ Not(pack) for pack in packs ])


def Iff(a, b):
    return And([
        Implies(a, b),
        Implies(b, a),
    ])


def Uniquely(domain_expr_fun, finite_domain):
    finite_domain = list(finite_domain)
    pairs = [
        (k, v)
        for k, v in itertools.product(finite_domain, repeat=2)
        if not k == v
    ]
    return And([
        Implies(domain_expr_fun(k), Not(domain_expr_fun(v)))
        for k, v in pairs
    ])


def UniquelyMap(cur_expr, domain_expr_fun, finite_domain):
    finite_domain = list(finite_domain)
    return And([
        Implies(cur_expr, Or([
            domain_expr_fun(el)
            for el in finite_domain
        ])),
        Uniquely(domain_expr_fun, finite_domain),
    ])


assumptions = []  # type: List[Z3Expr]

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

# These all need to be normalized to the semver 3-tuple to be lexicographically sorted!
def version_columns(version_string):
    return tuple(int(n) for n in version_string.split('.'))

Semver3Sort, mk_version, (ver1, ver2, ver3) = TupleSort(
    'Semver3Sort',
    [IntSort(), IntSort(), IntSort()])

VariantNameSort, variant_names = EnumSort('VariantNameSort', ['release', 'debug', 'idk'])
(release, debug, idk) = variant_names

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
                b: '2.1.3',
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
            'variants': [None, debug],
            'dependencies': {
                c: {
                    'low': '3.1.2',
                    'high': '3.1.2',
                    'prefer': neither,
                },
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
            'variants': [None, idk],
            'dependencies': {},
        },
        '3.1.2': {
            'variants': [None, idk],
            'dependencies': {},
        },
        '3.1.3': {
            'variants': [None, idk],
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

variant_default_value_from_package_py = Function('variant_default_value_from_package_py',
                                                  VariantNameSort, VariantValueSort)
variant_default_value_from_packages_yaml = Function('variant_default_value_from_packages_yaml',
                                                    VariantNameSort, VariantValueSort)

def as_variant_value(arg):
    if arg is None:
        return VariantValueSort.none
    if isinstance(arg, bool):
        return VariantValueSort.some(ExplicitValueSort.boolean(arg))
    if isinstance(arg, int):
        return VariantValueSort.some(ExplicitValueSort.integer(arg))
    if isinstance(arg, str):
        return VariantValueSort.some(ExplicitValueSort.string(StringVal(arg)))
    return arg

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

_VariantValueMap = Datatype('VariantValueMap')
_VariantValueMap.declare('empty')
_VariantValueMap.declare('multi',
                         ('name', VariantNameSort),
                         ('value', VariantValueSort),
                         ('cdr', _VariantValueMap))
VariantValueMapSort = _VariantValueMap.create()

def as_variant_map(variant_pairs):
    cur_map = VariantValueMapSort.empty
    for name, value in variant_pairs:
        (cur_value, _) = process_variant_for_spec(value)
        cur_map = VariantValueMapSort.multi(name, as_variant_value(cur_value), cur_map)
    return cur_map

variant_for_map = Function('variant_for_map',
                           VariantValueMapSort, VariantNameSort, VariantValueSort)

SpecSort, mk_spec, (get_spec_name, get_spec_version, get_spec_variants) = TupleSort(
    'SpecSort',
    [PackageNameSort, Semver3Sort, VariantValueMapSort])
cur_pkg = Const('cur_pkg', SpecSort)

dependency_matches_package_version = Function('dependency_matches_package_version',
                                              SpecSort, DepSpecSort, Semver3Sort, BoolSort())
variant_for_spec = Function('variant_for_spec', SpecSort, VariantNameSort, VariantValueSort)
get_dep_specs = Function('get_dep_specs', SpecSort, SetSort(DepSpecSort))
has_dependency = Function('has_dependency', SpecSort, SpecSort, BoolSort())

variant_get_value = Function('variant_get_value', SpecSort, VariantNameSort, VariantValueSort)
variant_get_source = Function('variant_get_source', SpecSort, VariantNameSort, VariantSourceSort)
spec_has_variant = Function('spec_has_variant', SpecSort, VariantNameSort, BoolSort())

use_package = Function('use_package', SpecSort, BoolSort())

repo_has_package = Function('repo_has_package', SpecSort, RepoSort, BoolSort())
use_repo_package = Function('use_repo_package', SpecSort, RepoSort, BoolSort())

def process_variant_for_spec(variant_value):
    if isinstance(variant_value, tuple) and variant_value and variant_value[0] is None:
        real_value = as_variant_value(variant_value[2])
        source = variant_value[1]
    else:
        real_value = as_variant_value(variant_value)
        source = spec
    return (real_value, source)


def build_assumptions(with_conflict=False):
    assumptions = []  # type: List[Z3Expr]

    bool_vars = collections.defaultdict(lambda: collections.defaultdict(list))
    pkg_mapping = {}
    pkg_inverse_mapping = collections.defaultdict(dict)
    pkg_repos = collections.defaultdict(list)

    deps_table = collections.defaultdict(list)
    conflicts_table = collections.defaultdict(list)
    variants_table = collections.defaultdict(dict)

    vs = Const('vs', VariantSourceSort)
    vn = Const('vn', VariantNameSort)
    vv = Const('vv', VariantValueSort)
    pkg1 = Const('pkg1', SpecSort)
    pkg2 = Const('pkg2', SpecSort)

    repo1 = Const('repo1', RepoSort)
    pn1 = Const('pn1', PackageNameSort)
    pn2 = Const('pn2', PackageNameSort)
    assumptions.extend([
        # The repo must contain the package in order for us to use it!
        ForAll([pkg1, repo1], Implies(use_repo_package(pkg1, repo1),
                                      repo_has_package(pkg1, repo1))),
        # Checking that any package we consume comes from exactly one repo.
        ForAll([pkg1],
               Uniquely(lambda repo: repo_has_package(pkg1, repo),
                        repos)),
        # FIXME: Checking uniqueness by name!
        ForAll([pkg1, pkg2],
               Implies(
                   And([(get_spec_name(pkg1) == get_spec_name(pkg2)),
                        (pkg1 != pkg2),
                        use_package(pkg1)]),
                   Not(use_package(pkg2))))
    ])

    ver1 = Const('ver1', Semver3Sort)
    ver2 = Const('ver2', Semver3Sort)
    ver_ret = Const('ver_ret', Semver3Sort)
    strat1 = Const('strat1', DepSpecStrategySort)
    dep_spec1 = Const('dep_spec1', DepSpecSort)
    assumptions.extend([
        # ForAll([ver1, ver2, ver_ret],
        #        Implies(And([ver_ret >= ver1, ver_ret < ver2]),
        #                dependency_matches_version(mk_dep_spec(ver1, ver2, low), ver_ret))),
        # ForAll([ver1, ver2, ver_ret],
        #        Implies(And([ver_ret <= ver2, ver_ret > ver1]),
        #                dependency_matches_version(mk_dep_spec(ver1, ver2, high), ver_ret))),
        # ForAll([ver1, ver2, ver_ret],
        #        Implies(And([(ver_ret == ver1), (ver1 == ver2)]),
        #            dependency_matches_version(mk_dep_spec(ver1, ver2, neither), ver_ret))),
    ])
    assumptions.extend([
        ForAll([dep_spec1, pkg1],
               Iff(IsMember(dep_spec1, get_dep_specs(pkg1)),
                   dependency_matches_package_version(pkg1, dep_spec1, ver_ret)))
        for strat in strategies
    ])

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
                             list((v_val, process_variant_for_spec(v_val))
                                  for v_val in values)))
                    for values in
                    itertools.product(*tuple(variant_try_value_map[n] for n in all_variant_names))
                ]

                for v_spec_sourced in variant_specs:
                    v_spec = dict((k, v[0]) for k, v in v_spec_sourced.items())
                    variant_value_map = as_variant_map(v_spec.items())
                    v_sources = dict((k, v[1][1]) for k, v in v_spec_sourced.items())

                    # Fill in variant values for this map.
                    for v_name, v_value in v_spec.items():
                        (real_value, _source) = process_variant_for_spec(v_value)
                        assumptions.extend([
                            (variant_for_map(variant_value_map, v_name) == real_value),
                            (variant_for_spec(pkg, v_name) == real_value),
                        ])

                    pkg = mk_spec(name, version, variant_value_map)
                    variants_table[pkg] = v_spec.copy()
                    # Fill in the appropriate variant sources for this package.
                    for v_name, v_source in v_sources.items():
                        cur_assertion = (variant_get_source(pkg, v_name) == v_source)
                        assumptions.append(cur_assertion)

                    # Fill in the named variants in this spec.
                    assumptions.extend([
                        spec_has_variant(pkg, v_name)
                        for v_name in v_spec.keys()
                    ] + [
                        Not(spec_has_variant(pkg, not_v_name))
                        for not_v_name in (set(variant_names) - set(v_spec.keys()))
                    ])

                    assumptions.extend([
                        # Fill in variant source specifications.
                        Implies((variant_get_source(pkg, v_name) == v_source),
                                {
                                    py: (lambda: (variant_get_value(pkg, v_name) == variant_default_value_from_package_py(
                                        v_name))),
                                    yaml: (lambda: (variant_get_value(pkg, v_name) == variant_default_value_from_packages_yaml(
                                                       v_name))),
                                    spec: (lambda: (variant_get_value(pkg, v_name) == variant_for_spec(pkg1, v_name))),
                                }[v_source]())
                        for v_name, v_source in v_sources.items()
                    ])

                    kwarg_spec = dict((n.sexpr(), v) for n, v in v_spec.items())
                    variant_description = as_variant_description(**kwarg_spec)
                    pkg_bool_var = Bool("{name}=={version}+{var}"
                                        .format(name=name,
                                                version=version_string,
                                                var=variant_description))
                    assumptions.append(Iff(pkg_bool_var, use_package(pkg)))

                    pkg_mapping[pkg] = (name, version, pkg_bool_var, variant_value_map)
                    pkg_inverse_mapping[name][v_tup] = (pkg, variant_value_map)

                    for repo in repos:
                        if name in name_try_repo_map[repo]:
                            assumptions.append(repo_has_package(pkg, repo))
                            pkg_repos[pkg].append(repo)
                            bool_vars[repo][name.sexpr()].append(pkg_bool_var)
                        else:
                            assumptions.append(Not(repo_has_package(pkg, repo)))

                    for dep_name, this_dep_spec in dep_var_spec['dependencies'].items():
                        low_version = mk_version(*version_columns(this_dep_spec['low']))
                        high_version = mk_version(*version_columns(this_dep_spec['high']))
                        prefer_strategy = this_dep_spec['prefer']

                        dep_spec = mk_dep_spec(low_version, high_version, prefer_strategy)

                        deps_table[pkg].append((dep_name, dep_spec))

                        assumptions.extend([
                            # Fill in dependency specifications.
                            IsMember(dep_spec, get_dep_specs(pkg)),
                            # Fill in dependency assumptions.
                            Implies(use_package(pkg), Or([
                                dependency_matches_package_version(
                                    pkg, dep_spec, mk_version(*other_version)
                                )
                                for other_version in package_version_try_map[dep_name]
                            ])),
                        ])

                    if with_conflict:
                        for conflict_name, conflict_version in dep_var_spec.get('conflicts', {}).items():
                            conflicts_table[pkg].append((conflict_name, conflict_version))

    for pkg, dep_specs in deps_table.items():
        for dep_name, dep_spec in dep_specs:
            assumptions.append(
                UniquelyMap(
                    use_package(pkg),
                    (lambda other: has_dependency(pkg, pkg_inverse_mapping[dep_name][other][0])),
                    package_version_try_map[dep_name])
            )

            low_end = get_low(dep_spec)
            high_end = get_high(dep_spec)
            strategy = get_strategy(dep_spec)

            for other in package_version_try_map[dep_name]:
                other_version = mk_version(*other)
                assumptions.extend([
                    dependency_matches_package_version(pkg, dep_spec, other_version),
                    Implies(
                        And([
                            other_version >= low_end,
                            other_version < high_end,
                            strategy == low,
                        ]),
                        dependency_matches_package_version(pkg, dep_spec, other_version)),
                    Implies(
                        And([
                            other_version <= high_end,
                            other_version >  low_end,
                            strategy == high,
                        ]),
                        dependency_matches_package_version(pkg, dep_spec, other_version)),
                    Implies(
                        And([
                            other_version == low_end,
                            low_end == high_end,
                            strategy = neither,
                        ]),
                        dependency_matches_package_version(pkg, dep_spec, other_version)),
                ])

                dep_pkg = pkg_inverse_mapping[dep_name][other][0]
                for v_name, v_value in variants_table[pkg].items():
                    assumptions.append(
                        Iff(has_dependency(pkg, dep_pkg),
                            And([
                                use_package(pkg),
                                use_package(dep_pkg),
                                spec_has_variant(pkg, v_name),
                                spec_has_variant(dep_pkg, v_name),
                                (variant_get_value(pkg, v_name) == variant_get_value(dep_pkg, v_name)),
                            ]))
                    )

    for pkg, conflicts in conflicts_table.items():
        for conflict_name, conflict_version in conflicts:
            conflicting_pkg_entries = pkg_inverse_mapping[conflict_name]
            (conflicting_package, _map) = conflicting_pkg_entries[
                version_columns(conflict_version)
            ]
            assumptions.append(
                Conflict([use_package(pkg), use_package(conflicting_package)]))

    return (assumptions, pkg_inverse_mapping)

# BoolVarsDict = Dict[RepoSort, Dict[str, List[Bool]]]

def install_check(problems, solver=None):
    # type: (Iterable[Z3Expr], Optional[Solver]) -> Solver
    if solver is None:
        solver = Solver()
    result = solver.check(problems)
    if result == sat:
        m = solver.model()
        r = []
        for x in m:
            if is_true(m[x]):
                # x is a Z3 declaration
                # x() returns the Z3 expression
                # x.name() returns a string
                r.append("name: {name} == value: {value}".format(name=x.name(), value=x()))
        print('\n'.join(r))
    else:
        print("'{}' installation profile".format(result))
    return solver


def ground_check(grounder, solver=None, with_conflict=False):
    # type: (List[Z3Expr], Optional[Solver], bool) -> Tuple[BoolVarsDict, List[Bool], Solver]
    (assumptions, pkg_inverse_mapping) = build_assumptions(with_conflict=with_conflict)
    all_exprs = assumptions + list(grounder(pkg_inverse_mapping))
    s = install_check(all_exprs, solver=solver)
    return (s, all_exprs, pkg_inverse_mapping)

robust_tactic = Then(TryFor(Tactic('horn-simplify'), 5000),
                     TryFor(Tactic('macro-finder'), 1000),
                     TryFor(Tactic('sat'), 10000))


s1, e1, m1 = ground_check(lambda m: [use_package(m[a][(1, 5, 2)][0])],
                          solver=robust_tactic.solver(),
                          with_conflict=False)

s2, e2, m1 = ground_check(lambda m: [use_package(m[a][(1, 5, 2)][0])],
                          solver=robust_tactic.solver(),
                          with_conflict=True)
core2 = s2.unsat_core()
print("s2.unsat_core():\n{}".format('\n'.join(str(e) for e in core2)))

code.interact(local=locals())
