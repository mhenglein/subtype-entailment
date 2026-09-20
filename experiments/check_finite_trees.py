#!/usr/bin/env python3
"""E056: independent growth-language and complete small finite-SAT checks."""
from __future__ import annotations

import argparse
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT))
import finite_trees as finite
import regular_countermodel as regular
from experiments import check_stack_summary as oracle


def threshold_hot(system):
    """Independent Pre* oracle for accepted words of length at least n.

    In an n-state epsilon NFA, accepting n letters forces a consuming cycle.
    Initial controls are unrestricted. Check prefixes of exactly n letters by
    reverse-system reachability to empty; check arbitrary Pop continuations by
    original-system reachability from empty to any stack. No SCC algorithm.
    """
    def convert(s):
        return oracle.System(s.size, frozenset(s.epsilon),
            frozenset((a,p,q) for p,a,q in s.push),
            frozenset((a,p,q) for p,a,q in s.pop))
    reverse, forward = convert(system.reverse()), convert(system)
    empty_pre = [oracle.predecessor(reverse, m, ()) for m in range(system.size)]
    any_pre = [oracle.predecessor(forward, r, None) for r in range(system.size)]
    result = set()
    for word in product((0,1), repeat=system.size):
        for r in range(system.size):
            if any(empty_pre[r](q,word) for q in range(system.size)):
                result.update(m for m in range(system.size) if any_pre[r](m,()))
    return result


def shapes(height):
    if height == 0:
        return [frozenset()]
    smaller = shapes(height-1)
    return [frozenset()] + [product_tree(l,r) for l,r in product(smaller,repeat=2)]


def product_tree(left, right):
    return frozenset({()} | {(0,)+w for w in left} | {(1,)+w for w in right})


def holds(constraint, valuation):
    tag, *xs = constraint
    if tag == 'leq':
        return valuation[xs[0]] <= valuation[xs[1]]
    if tag == 'denial':
        return not valuation[xs[0]]
    if tag == 'lower':
        return product_tree(valuation[xs[0]],valuation[xs[1]]) <= valuation[xs[2]]
    return valuation[xs[0]] <= product_tree(valuation[xs[1]],valuation[xs[2]])


def normalized_system(constraints, n):
    independent = oracle.system_of(constraints,n)
    forced = {c[3] for c in constraints if c[0]=='lower'}
    denied = {c[1] for c in constraints if c[0]=='denial'}
    system = regular.System(n,set(independent.eps),
        {(p,a,q) for a,p,q in independent.push},
        {(p,a,q) for a,p,q in independent.pop},forced,denied,0,0)
    return system, independent


def run():
    rng=random.Random(5803)
    counts={'growth_systems':0, 'consuming_systems':0,
            'finite_sat_inputs':0, 'finite_sat_yes':0, 'growth_unsat':0,
            'denial_unsat_without_growth':0, 'finite_valuations':0}
    for _ in range(300):
        n=rng.randrange(1,5)
        eps={(p,q) for p in range(n) for q in range(n) if rng.random()<.13}
        push={(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random()<.09}
        pop={(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random()<.09}
        system=regular.System(n,eps,push,pop,{q for _,_,q in push},set(),0,0)
        actual=finite.growth_analysis(system)
        assert set(actual['hot']) == threshold_hot(system)
        counts['growth_systems']+=1
        counts['consuming_systems']+=actual['has_consuming_cycle']
    # Every subset of at most three normalized clauses on one/two controls.
    # In the no-growth case the least forced-root closure has height <= n.
    # Thus height <= n is complete for SAT, not an asserted entailment bound.
    for n in (1,2):
        clauses=([('leq',p,q) for p,q in product(range(n),repeat=2)] +
            [(tag,p,q,r) for tag in ('lower','upper') for p,q,r in product(range(n),repeat=3)] +
            [('denial',p) for p in range(n)])
        valuations=list(product(shapes(n),repeat=n))
        valid_for={c:{i for i,v in enumerate(valuations) if holds(c,v)} for c in clauses}
        for size in range(4):
            for constraints in combinations(clauses,size):
                candidates=set(range(len(valuations)))
                for c in constraints:
                    candidates &= valid_for[c]
                actual=bool(candidates)
                system,independent=normalized_system(constraints,n)
                growth=finite.growth_analysis(system)['has_consuming_cycle']
                arb_sat=True
                for denied in system.denied:
                    predecessor=oracle.predecessor(independent,denied,None)
                    if any(predecessor(p,()) for p in system.forced):
                        arb_sat=False
                expected=not growth and arb_sat
                assert actual == expected, (constraints,actual,expected)
                counts['finite_sat_inputs']+=1
                counts['finite_sat_yes']+=actual
                counts['growth_unsat']+=growth
                counts['denial_unsat_without_growth']+=not growth and not arb_sat
                counts['finite_valuations']+=len(valuations)
    return {'status':'PASS','seed':5803,'counts':counts,
            'scope':'300 finite-system infiniteness comparisons and complete finite-SAT census for <=3 clauses on 1/2 controls',
            'completeness':'Finite-SAT height <= n follows from no consuming cycle and the least forced-root closure. No fixed-height entailment bound is asserted.',
            'trust':'Independent ordinary Python checks; no Lean classifier equivalence is claimed.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'tmp/finite-tree-experiment.json')
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))


if __name__=='__main__':
    main()
