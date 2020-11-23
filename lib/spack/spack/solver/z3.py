from __future__ import absolute_import, print_function

import code
import collections
import itertools
from abc import ABC, abstractmethod
from contextlib import contextmanager
# from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple, Union

from z3 import *

from spack.solver.asp import *


class Timer(Timer):
    def __init__(self):
        super().__init__()
        self.superphase = ''

    def phase(self, name, sep='/'):
        return super().phase(self.superphase + sep + name)

    @contextmanager
    def nested_phase(self, subname, sub_phase='<subphase>', sep='/'):
        orig = self.superphase
        self.superphase += sep
        self.superphase += subname
        try:
            self.phase(sub_phase, sep=sep)
            yield self
        finally:
            self.superphase = orig
            self.phase('')

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

variant_default_value_from_package_py = Function('variant_default_value_from_package_py',
                                                  VariantNameSort, VariantValueSort)
variant_default_value_from_packages_yaml = Function('variant_default_value_from_packages_yaml',
                                                    VariantNameSort, VariantValueSort)

def as_variant_value(arg):
    if arg is None:
        return VariantValueSort.none
    if isinstance(arg, bool):
        return VariantValueSort.some(ExplicitValueSort.boolean(BoolVal(arg)))
    if isinstance(arg, int):
        return VariantValueSort.some(ExplicitValueSort.integer(IntVal(arg)))
    if isinstance(arg, str):
        return VariantValueSort.some(ExplicitValueSort.string(StringVal(arg)))
    if isinstance(arg, tuple) and len(arg) == 3:
        if arg[1] in variant_sources:
            arg = arg[2]
        else:
            arg = arg[1]
        if isinstance(arg, int):
            return as_variant_value(arg)
        elif isinstance(arg, str):
            return as_variant_value(arg)
        return VariantValueSort.some(ExplicitValueSort.any(AnyConst))
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

SpecSort, mk_spec, (get_spec_name, get_spec_version, get_spec_variants) = TupleSort(
    'SpecSort',
    [PackageNameSort, Semver3Sort, VariantValueMapSort])
cur_pkg = Const('cur_pkg', SpecSort)

def specs_like(name, ver, var_map):
    yield mk_spec(name, ver, var_map)
    while not var_map is VariantValueMapSort.empty:
        yield mk_spec(
            name, ver, VariantValueMapSort.cdr(var_map))

dependency_matches_package_version = Function('dependency_matches_package_version',
                                              SpecSort, DepSpecSort, Semver3Sort, BoolSort())
variant_for_spec = Function('variant_for_spec', SpecSort, VariantNameSort, VariantValueSort)
get_dep_specs = Function('get_dep_specs', SpecSort, SetSort(DepSpecSort))

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

    pkg_mapping = {}
    pkg_inverse_mapping = collections.defaultdict(dict)
    pkg_repos = collections.defaultdict(list)

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
                    v_keys = list(v_spec.keys())
                    not_v_keys = (set(variant_names) - set(v_keys))
                    assumptions.extend([
                        spec_has_variant(pkg, v_name)
                        for v_name in v_keys
                    ] + [
                        Not(spec_has_variant(pkg, not_v_name))
                        for not_v_name in not_v_keys
                    ])

                    assumptions.extend([
                        # Fill in variant source specifications.
                        Implies((variant_get_source(pkg, v_name) == v_source),
                                {
                                    py: (lambda: (variant_get_value(pkg, v_name) == variant_default_value_from_package_py(
                                        v_name))),
                                    yaml: (lambda: (variant_get_value(pkg, v_name) == variant_default_value_from_packages_yaml(
                                                       v_name))),
                                    spec: (lambda: (variant_get_value(pkg, v_name) == variant_for_spec(pkg, v_name))),
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
                        else:
                            assumptions.append(Not(repo_has_package(pkg, repo)))

                    deps = dep_var_spec['dependencies']
                    for dep_name, this_dep_spec in deps.items():
                        low_version = mk_version(*version_columns(this_dep_spec['low']))
                        high_version = mk_version(*version_columns(this_dep_spec['high']))
                        prefer_strategy = this_dep_spec['prefer']

                        dep_spec = mk_dep_spec(low_version, high_version, prefer_strategy)

                        deps_table[pkg].append((dep_name, dep_spec))

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
        for dep_name, dep_spec in dep_specs:
            low_end = get_low(dep_spec)
            high_end = get_high(dep_spec)
            strategy = get_strategy(dep_spec)

            # Here's where we provide dependency ranges!
            for other in package_version_try_map[dep_name]:
                other_version = mk_version(*other)
                assumptions.append(
                    Implies(
                        And([
                            (other_version >= low_end),
                            (other_version < high_end),
                            (strategy == low),
                        ]),
                        dependency_matches_package_version(pkg, dep_spec, other_version),
                    )
                )
                assumptions.append(
                    Implies(
                        And([
                            (other_version <= high_end),
                            (other_version >  low_end),
                            (strategy == high),
                        ]),
                        dependency_matches_package_version(pkg, dep_spec, other_version),
                    )
                )

                assumptions.append(
                    Implies(
                        And([
                            (other_version == low_end),
                            (low_end == high_end),
                            (strategy == neither),
                        ]),
                        dependency_matches_package_version(pkg, dep_spec, other_version),
                    )
                )

                dep_pkg = pkg_inverse_mapping[dep_name][other][0]
                other_pkgs_by_name = [v[0] for k, v in pkg_inverse_mapping[dep_name].items()
                                      if k != other]

                assumptions.append(
                    Xor(
                        use_package(dep_pkg),
                        Or([
                            use_package(op)
                            for op in other_pkgs_by_name
                        ]),
                    )
                )

                # TODO: Here's where we try to make a set!
                # assumptions.append(
                #     Iff(
                #         And([use_package(pkg), use_package(dep_pkg)]),
                #         IsMember(dep_spec, get_dep_specs(pkg)),
                #     )
                # )

                assumptions.extend(
                    Implies(
                        And([use_package(pkg), use_package(dep_pkg),
                             spec_has_variant(pkg, v_name),
                             spec_has_variant(dep_pkg, v_name)]),
                        (variant_get_value(pkg, v_name) == variant_get_value(dep_pkg, v_name)),
                    )
                    for v_name, v_value in variants_table[pkg].items()
                )

    for pkg, conflicts in conflicts_table.items():
        for conflict_name, conflict_infos in conflicts.items():
            for conflict_version, child_variants in conflict_infos:
                c_v_tup = version_columns(conflict_version)
                conflicting_package = pkg_inverse_mapping[conflict_name][c_v_tup][0]
                parent_variants = (
                    variant_for_spec_try_map[conflict_name][conflict_version].get('variants', []))
                # FIXME: just intersecting variants for now!
                relevant_variants = list(set(child_variants) & set(parent_variants))

                variant_specs = [
                    dict(zip(relevant_variants,
                             list((v_val, process_variant_for_spec(v_val))
                                 for v_val in values)))
                    for values in
                    itertools.product(*tuple(
                        variant_try_value_map[n]
                        for n in relevant_variants
                        if n is not None
                    ))
                ]

                for v_spec_sourced in variant_specs:
                    v_spec = dict((k, v[0]) for k, v in v_spec_sourced.items())
                    variant_value_map = as_variant_map(v_spec.items())
                    # print('map: {}'.format(variant_value_map))

                    for v_name, v_value in v_spec.items():
                        if v_name is None:
                            continue
                        v_value = as_variant_value(v_value)
                        # print('v_name: {}, v_value2: {}'.format(v_name, v_value))

                        assumptions.append(
                            (v_value == variant_for_map(variant_value_map, v_name)),
                        )

                        for s in specs_like(
                            conflict_name,
                            mk_version(*c_v_tup),
                            variant_value_map,
                        ):
                            assumptions.append(
                                (variant_for_spec(s, v_name) == v_value)
                            )

    return (assumptions, (pkg_mapping, pkg_inverse_mapping), conflicts_table, deps_table)

# BoolVarsDict = Dict[RepoSort, Dict[str, List[Bool]]]

def install_check(problems, solver=None):
    # type: (Iterable[Z3Expr], Optional[Solver]) -> Solver
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
                truths.append("name: {name} == value: {value}".format(name=x.name(), value=x()))
    elif result == unsat:
        unsat_core = solver.unsat_core()
    return (solver, result, truths, unsat_core)


def ground_check(grounder, solver=None, with_conflict=False):
    # type: (List[Z3Expr], Optional[Solver], bool) -> Tuple[BoolVarsDict, List[Bool], Solver]
    (assumptions, pkg_mappings, conflicts_table, deps_table) = build_assumptions(
        with_conflict=with_conflict)
    grounds_maybe = list(grounder(pkg_mappings))
    print('grounds: {}'.format(grounds_maybe))
    all_exprs = assumptions + grounds_maybe
    (s, result, truths, unsat_core) = install_check(all_exprs, solver=solver)
    if result == sat:
        print('TRUTHS:\n{}'.format('\n'.join(truths)))
    elif result == unknown:
        print('UNKNOWN:\n{}'.format(s.reason_unknown()))
    elif result == unsat:
        print('UNSAT_CORE():\n{}'.format(s.unsat_core()))
    else:
        raise OSError('unrecognized result {}'.format(result))
    return (s, all_exprs, pkg_mappings, result, truths, unsat_core, conflicts_table, grounds_maybe, deps_table)


robust_tactic = Then(
                     Tactic('macro-finder'),
                     Tactic('smt'),
                     Tactic('symmetry-reduce'),
                     Tactic('smt'),
)

s1, e1, m1, r1, tr1, u1, c1, g1, dt1 = ground_check((lambda _: [use_package(
    mk_spec(a, mk_version(1, 5, 2), as_variant_map([(idk, 'idk2'), (debug, 2)])),
)]),
                                                    # solver=robust_tactic.solver(),
                                                    with_conflict=False)


code.interact(local=locals())

s2, e2, m2, r2, tr2, u2, c2, g2, dt2 = ground_check((lambda _: [use_package(
    mk_spec(a, mk_version(1, 5, 2), as_variant_map([(idk, 'idk2'), (debug, 2)])),
)]),
                                                    # solver=robust_tactic.solver(),
                                                    with_conflict=True)

core2 = s2.unsat_core()

code.interact(local=locals())
