#!/usr/bin/env python3
"""Independent finite-set and native-output checks; not an arbitrary-tree decision.

Products are never truncated. Enumerating finite values only tests implications
on that corpus; it is not an UNSAT/entailment oracle for arbitrary trees.
"""
from __future__ import annotations

import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path
from typing import Any

Expr = tuple
BOT: Expr = ('bot',)
Tree = frozenset[str]


def var(i: int) -> Expr:
    return ('var', i)


def prod(l: Expr, r: Expr) -> Expr:
    return ('prod', l, r)


@lru_cache(maxsize=None)
def product_tree(l: Tree, r: Tree) -> Tree:
    return frozenset({''} | {'0' + w for w in l} | {'1' + w for w in r})


def evaluate(e: Expr, rho: tuple[Tree, ...]) -> Tree:
    if e[0] == 'var':
        return rho[e[1]]
    if e[0] == 'bot':
        return frozenset()
    return product_tree(evaluate(e[1], rho), evaluate(e[2], rho))


def pairs(e: Expr) -> list[tuple[Expr, Expr]]:
    if e[0] != 'prod':
        return []
    return [(e[1], e[2])] + pairs(e[1]) + pairs(e[2])


def has_bot(e: Expr) -> bool:
    return e[0] == 'bot' or (e[0] == 'prod' and (has_bot(e[1]) or has_bot(e[2])))


def product_count(e: Expr) -> int:
    return 0 if e[0] != 'prod' else 1 + product_count(e[1]) + product_count(e[2])


def small_exprs(n: int) -> list[Expr]:
    leaves = [BOT] + [var(i) for i in range(n)]
    return leaves + [prod(l, r) for l in leaves for r in leaves]


def fixtures() -> list[tuple[int, list[tuple[Expr, Expr]], Expr, Expr]]:
    out = []
    for n in range(3):
        for s in small_exprs(n):
            for t in small_exprs(n):
                out += [(n, [], s, t), (n, [(s, t)], BOT, BOT)]
    x, y = var(0), var(1)
    out += [
        (2, [(prod(prod(x, BOT), prod(x, BOT)), y)], x, y),
        (1, [(prod(x, BOT), x)], x, BOT),
        (0, [(prod(BOT, BOT), BOT)], BOT, BOT),
        (2, [(BOT, x)], y, x),
    ]
    return out


def compile_case(case: tuple) -> tuple[dict[str, Any], list, int]:
    n, gamma, s, t = case
    forest = [s, t] + [e for c in gamma for e in c]
    ps = [p for e in forest for p in pairs(e)]
    b = int(any(has_bot(e) for e in forest))
    first = {}
    for j, p in enumerate(ps):
        first.setdefault(p, n + b + j)

    def ref(e: Expr) -> int:
        if e[0] == 'var':
            assert 0 <= e[1] < n
            return e[1]
        if e[0] == 'bot':
            assert b == 1
            return n
        return first[(e[1], e[2])]

    cs = [['B', n]] if b else []
    for j, (l, r) in enumerate(ps):
        p = n + b + j
        cs += [['U', p, ref(l), ref(r)], ['D', ref(l), ref(r), p]]
    definition_count = len(cs)
    cs += [['L', ref(l), ref(r)] for l, r in gamma]
    result = dict(n=n, total=n + b + len(ps), left=ref(s), right=ref(t), clauses=cs)
    assert len(ps) == sum(product_count(e) for e in forest)
    assert definition_count == 2 * len(ps) + b
    assert len(cs) == len(gamma) + definition_count
    assert all(0 <= v < result['total'] for c in cs for v in c[1:])
    return result, ps, b


def holds(c: list, eta: tuple[Tree, ...]) -> bool:
    tag, *v = c
    if tag == 'B':
        return not eta[v[0]]
    if tag == 'L':
        return eta[v[0]] <= eta[v[1]]
    if tag == 'U':
        return eta[v[0]] <= product_tree(eta[v[1]], eta[v[2]])
    if tag == 'D':
        return product_tree(eta[v[0]], eta[v[1]]) <= eta[v[2]]
    raise ValueError(tag)


def original_models(gamma: list, rho: tuple[Tree, ...]) -> bool:
    return all(evaluate(l, rho) <= evaluate(r, rho) for l, r in gamma)


def canonical(case: tuple, ps: list, b: int, rho: tuple[Tree, ...]) -> tuple[Tree, ...]:
    return rho + ((frozenset(),) if b else ()) + tuple(evaluate(prod(l, r), rho) for l, r in ps)


def finite_values() -> list[Tree]:
    # Exactly the five prefix-closed product sets with node-address length < 2.
    return [frozenset(), frozenset({''}), frozenset({'', '0'}),
            frozenset({'', '1'}), frozenset({'', '0', '1'})]


def semantic_checks(cases: list) -> dict[str, int]:
    stats = dict(fixtures=len(cases), original_valuations=0, original_models=0,
                 arbitrary_extended_valuations=0, definition_models=0,
                 normalized_models=0, exact_query_set_checks=0,
                 max_added_variables=0, max_clauses=0)
    values = finite_values()
    for case in cases:
        n, gamma, s, t = case
        compiled, ps, b = compile_case(case)
        cs = compiled['clauses']
        dc = 2 * len(ps) + b
        stats['max_added_variables'] = max(stats['max_added_variables'], len(ps) + b)
        stats['max_clauses'] = max(stats['max_clauses'], len(cs))
        for rho in itertools.product(values, repeat=n):
            eta = canonical(case, ps, b, rho)
            old = original_models(gamma, rho)
            assert all(holds(c, eta) for c in cs[:dc])
            assert all(holds(c, eta) for c in cs) == old
            assert eta[:n] == rho
            assert eta[compiled['left']] == evaluate(s, rho)
            assert eta[compiled['right']] == evaluate(t, rho)
            stats['original_valuations'] += 1
            stats['original_models'] += int(old)
            stats['exact_query_set_checks'] += 1
        assert len(values) ** compiled['total'] <= 15625, 'corpus resource contract exceeded'
        for eta in itertools.product(values, repeat=compiled['total']):
            stats['arbitrary_extended_valuations'] += 1
            if not all(holds(c, eta) for c in cs[:dc]):
                continue
            stats['definition_models'] += 1
            rho = eta[:n]
            # Stronger than just checking valuations satisfying all premises.
            assert eta == canonical(case, ps, b, rho)
            assert eta[compiled['left']] == evaluate(s, rho)
            assert eta[compiled['right']] == evaluate(t, rho)
            stats['exact_query_set_checks'] += 1
            full = all(holds(c, eta) for c in cs)
            assert full == original_models(gamma, rho)
            stats['normalized_models'] += int(full)
    return stats


def mutation_guards() -> list[str]:
    empty, root = frozenset(), frozenset({''})
    larger = product_tree(root, empty)
    # Removing a lower definition admits the all-bottom model of an impossible premise.
    case = (0, [(prod(BOT, BOT), BOT)], BOT, BOT)
    c, _, _ = compile_case(case)
    eta = (empty,) * c['total']
    assert not all(holds(x, eta) for x in c['clauses'])
    assert all(holds(x, eta) for x in c['clauses'] if x[0] != 'D')
    # Removing an upper definition admits an oversized proxy and original variable.
    case = (1, [(var(0), prod(BOT, BOT))], BOT, BOT)
    c, _, _ = compile_case(case)
    eta = (larger, empty, larger)
    assert not original_models(case[1], eta[:1])
    assert all(holds(x, eta) for x in c['clauses'] if x[0] != 'U')
    # The query is not a premise: the ground product/bottom query has a countermodel.
    case = (0, [], prod(BOT, BOT), BOT)
    c, ps, b = compile_case(case)
    eta = canonical(case, ps, b, ())
    assert all(holds(x, eta) for x in c['clauses'])
    assert not eta[c['left']] <= eta[c['right']]
    assert not all(holds(x, eta) for x in c['clauses'] + [['L', c['left'], c['right']]])
    # An original generated-looking variable must not become the bottom proxy.
    case = (2, [(BOT, var(0))], var(1), var(0))
    c, ps, b = compile_case(case)
    eta = canonical(case, ps, b, (empty, root))
    assert c['left'] == 1 and c['right'] == 0
    assert all(holds(x, eta) for x in c['clauses'])
    assert not eta[1] <= eta[0]
    return ['missing_lower', 'missing_upper', 'query_as_premise', 'fresh_collision']


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-output', type=Path)
    args = parser.parse_args()
    cases = fixtures()
    matched = 0
    if args.lean_output is not None:
        actual = [json.loads(line) for line in args.lean_output.read_text().splitlines() if line.strip()]
        expected = [compile_case(case)[0] for case in cases]
        assert len(actual) == len(expected), (len(actual), len(expected))
        for i, (a, e) in enumerate(zip(actual, expected)):
            assert a == e, (i, a, e)
        matched = len(actual)
    result = dict(status='PASS', semantic_corpus=semantic_checks(cases),
                  native_lean_outputs_matched=matched,
                  mutation_guards=mutation_guards(),
                  seed=None,
                  limits=dict(finite_values=5, max_extended_valuations_per_case=15625,
                              products_truncated=False,
                              arbitrary_tree_completeness_claim=False),
                  infinite_models='Separate Lean theorem; see build status, not finite enumeration')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
