from __future__ import absolute_import, print_function

import code
import collections
import itertools
# from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple, Union

from z3 import *


# Z3Expr = Union[Bool, And, Or, Not, Implies]

def DependsOn(pack, deps):
    # type: (Z3Expr, Union[Iterable[Z3Expr], Z3Expr]) -> Z3Expr
    if is_expr(deps):
        return Implies(pack, deps)
    else:
        return And([ Implies(pack, dep) for dep in deps ])


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

# These all need to be normalized to the semver 3-tuple to be lexicographically sorted!
version_strings = ['0.0.1', '1.0.0', '1.5.2', '1.5.3', '2.5.4', '3.0.0', '3.0.1']
versions = [tuple(int(n) for n in el.split('.')) for el in version_strings]
VersionSort, mk_version, (ver1, ver2, ver3) = TupleSort('VersionSort',
                                                        [IntSort(), IntSort(), IntSort()])

SemverPackageSort, mk_pkg, (pkg1, pkg2) = TupleSort('SemverPackage', [PackageNameSort, VersionSort])
cur_pkg = Const('cur_pkg', SemverPackageSort)

use_package = Function('use_package', SemverPackageSort, BoolSort())

repo_has_package = Function('repo_has_package', SemverPackageSort, RepoSort, BoolSort())
use_repo_package = Function('use_repo_package', SemverPackageSort, RepoSort, BoolSort())

bool_vars = collections.defaultdict(lambda: collections.defaultdict(list))
pkg_mapping = {}
pkg_inverse_mapping = collections.defaultdict(dict)
pkg_repos = collections.defaultdict(list)
pkg_vars = collections.defaultdict(list)

# FIXME: assume all packages have all versions!
for name, v_tup in itertools.product(names, versions):
    pkg_vars[name].append(v_tup)

    version = mk_version(*v_tup)
    pkg = mk_pkg(name, version)
    pkg_mapping[pkg] = (name, v_tup)
    pkg_inverse_mapping[name.sexpr()][v_tup] = pkg

    version_str = '.'.join(str(n) for n in v_tup)
    pkg_bool_var = Bool("{name}=={version}".format(name=name, version=version_str))
    assumptions.append(Iff(pkg_bool_var, use_package(pkg)))

    # FIXME: assume all repos have all packages!
    for repo in repos:
        assumptions.append(repo_has_package(pkg, repo))
        pkg_repos[pkg].append(repo)
        # The repo must contain the package in order for us to use it!
        assumptions.append(
            Implies(use_repo_package(pkg, repo), repo_has_package(pkg, repo))
        )
        bool_vars[repo][name.sexpr()].append(pkg_bool_var)

for name in names:
    versions_for_name = pkg_vars[name.sexpr()]
    assumptions.append(
        Uniquely((lambda v2_tup: use_package(mk_pkg(name, mk_version(*v2_tup)))),
                 versions_for_name)
    )

for pkg, cur_repos in pkg_repos.items():
    assumptions.append(
        UniquelyMap(use_package(pkg),
                    (lambda repo: use_repo_package(pkg, repo)),
                    cur_repos)
    )

# BoolVarsDict = Dict[RepoSort, Dict[str, List[Bool]]]

def fake_bool_vars(with_conflict=False):
    # type: (bool) -> List[Z3Expr]
    ab_bc_deps = [
        Implies(use_package(mk_pkg(name, mk_version(*v_tup))),
                use_package(mk_pkg(names[(j + 1) % len(names)],
                                   mk_version(*(versions[(i + 1) % len(versions)])))))
        for (j, name), (i, v_tup) in itertools.product(
            enumerate(names),
            enumerate(versions))
        if name is not c
    ]

    ac_conflicts = []
    if with_conflict:
        ac_conflicts.extend(
            Implies(use_package(mk_pkg(name, mk_version(*v_tup))),
                    Not(use_package(mk_pkg(names[(j + 2) % len(names)],
                                           mk_version(*(versions[(i + 2) % len(versions)]))))))
            for (j, name), (i, v_tup) in itertools.product(
                enumerate(names),
                enumerate(versions))
        )

    return (ab_bc_deps + ac_conflicts)


def install_check(problems, solver=None):
    # type: (Iterable[Z3Expr], Optional[Solver]) -> Solver
    if solver is None:
        t = Tactic('horn')
        solver = t.solver()
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


def ground_check(ground, solver=None, with_conflict=False):
    # type: (List[Z3Expr], Optional[Solver], bool) -> Tuple[BoolVarsDict, List[Bool], Solver]
    all_deps = fake_bool_vars(with_conflict=with_conflict)
    all_exprs = (assumptions + all_deps + ground)
    s = install_check(all_exprs, solver=solver)
    return (s, all_exprs)


s1, e1 = ground_check([bool_vars[spack][a.sexpr()][0]],
                      solver=Solver(),
                      with_conflict=False)

s2, e2 = ground_check([bool_vars[spack][a.sexpr()][0]],
                      solver=Solver(),
                      with_conflict=True)
core2 = s2.unsat_core()
print("s2.unsat_core():\n{}".format('\n'.join(str(e) for e in core2)))

code.interact(local=locals())
