"""Reproduce the modular counterexamples to Q002/Q003 and constant pump counts.

Finite regressions and exact finite-graph searches are recorded separately from
all-parameter written proofs. No resource limit is interpreted as NO.
"""
import hashlib
import itertools
import json
from pathlib import Path

from border_lab import Sandwich, witness, border_witness, sufficient, word_budget, words
from denial_bridge import build, reduced, Canonical
from terminal_realization import realize
from modular_sync_family import (make_family, word_from_counts, predicted_witness,
                                 agreement_profile, reverse_profile,
                                 delete_intervals, uniform_shrink_intervals)

ROOT = Path(__file__).resolve().parents[1]


def encode(instance):
    return dict(delta=instance.delta, final=sorted(instance.final),
                flags=sorted(instance.flags), bad=sorted(instance.bad),
                start=instance.start, alphabet=instance.alphabet)


def exact_budget_check(family):
    I, expected = family.instance, family.exact_budget
    rows = []
    for budget in range(expected + 1):
        for L in range(budget + 1):
            D = budget - L
            answer = Sandwich(I, L, D, True).search(max_states=200000)
            rows.append(dict(L=L, D=D, **answer))
            if answer['status'] == 'UNKNOWN':
                raise AssertionError('Resource cap: exact-budget regression is inconclusive')
            if budget < expected:
                assert answer['status'] == 'NO'
            elif answer['status'] == 'YES':
                w = answer['word']
                assert witness(I, w) and border_witness(I, w) and sufficient(I, w, L, D)
                assert predicted_witness(family, w)
    assert any(row['status'] == 'YES' for row in rows)
    return rows


def main():
    counts = dict(binary_words=0, exponent_vectors=0, uniform_word_budgets=0,
                  exact_budget_searches=0, canonical_models=0, bridge_word_checks=0,
                  profile_vectors=0, deletion_sets=0)
    primary = make_family((2, 3))
    I = primary.instance
    w = word_from_counts((6, 6))
    assert len(I.delta) == 8 and primary.exact_budget == 7 and len(w) == 14
    expected_profile = agreement_profile(I, w)
    assert expected_profile == reverse_profile(I, w)
    accepted_shorter = 0
    dominated_shorter = []
    for candidate in words('01', len(w)):
        expected = predicted_witness(primary, candidate)
        assert witness(I, candidate) == border_witness(I, candidate) == expected
        counts['binary_words'] += 1
        if I.admissible(candidate) and len(candidate) < len(w):
            accepted_shorter += 1
            if agreement_profile(I, candidate) <= expected_profile:
                dominated_shorter.append(candidate)
    assert not dominated_shorter
    primary_rows = exact_budget_check(primary)
    counts['exact_budget_searches'] += len(primary_rows)

    tuples = [(1, 1), (1, 2), (2, 2), (3, 2), (3, 4), (3, 5),
              (2, 3, 1), (1, 2, 3), (2, 3, 5)]
    family_rows = []
    for periods in tuples:
        F = make_family(periods)
        # Complete independent checks over this finite exponent rectangle.
        for multipliers in itertools.product(range(1, 5), repeat=len(periods)):
            ns = tuple(a * p for a, p in zip(multipliers, periods))
            v = word_from_counts(ns)
            assert witness(F.instance, v) == border_witness(F.instance, v) == (len(set(ns)) == 1)
            counts['exponent_vectors'] += 1
        for a in (1, 2):
            N = a * F.common_period
            v = word_from_counts((N,) * len(periods))
            assert witness(F.instance, v) and border_witness(F.instance, v)
            assert word_budget(F.instance, v) == (len(periods)-1) * (N+1)
            counts['uniform_word_budgets'] += 1
        searches = exact_budget_check(F) if F.exact_budget <= 16 else []
        counts['exact_budget_searches'] += len(searches)
        family_rows.append(dict(periods=periods, states=len(F.instance.delta),
                                least_positive_common_length=F.common_period,
                                exact_budget_from_proof=F.exact_budget,
                                shortest_length_from_proof=F.shortest_length,
                                completed_graph_searches=len(searches),
                                maximum_graph_states=max((r['states'] for r in searches), default=None)))

    # The actual 17-variable subtype instance, checked by exact regular-language operations.
    R = realize(I)
    status, bridge = build(R.variables, R.constraints, R.alpha, R.beta)
    assert status == 'SAT' and R.variables == 17 and len(R.constraints) == 21
    small, _ = reduced(bridge, R.alpha, R.beta)
    candidates = set(words('01', 6))
    candidates.update(word_from_counts((2*a, 3*b)) for a in range(1, 6) for b in range(1, 6))
    for v in sorted(candidates, key=lambda s: (len(s), s)):
        expected = predicted_witness(primary, v)
        assert witness(bridge.instance, v) == witness(small, v) == expected
        counts['bridge_word_checks'] += 1
        assert (not Canonical(R.variables, R.constraints, R.alpha, R.beta, v).errors()) == expected
        counts['canonical_models'] += 1
    assert not Canonical(R.variables, R.constraints, R.alpha, R.beta, w).errors()
    counts['canonical_models'] += 1

    # All r blocks must be edited together in the periods=(1,...,1) specialization.
    pump_rows = []
    for r in range(2, 8):
        F = make_family((1,) * r)
        source = word_from_counts((3,) * r)
        P = agreement_profile(F.instance, source)
        assert P == reverse_profile(F.instance, source)
        good = []
        for ns in itertools.product(range(1, 4), repeat=r):
            v = word_from_counts(ns)
            assert (agreement_profile(F.instance, v) <= P) == (len(set(ns)) == 1)
            counts['profile_vectors'] += 1
            if len(v) < len(source) and agreement_profile(F.instance, v) <= P:
                changed = sum(n != 3 for n in ns)
                assert changed == r
                good.append(v)
        intervals = uniform_shrink_intervals(r, 3, 1)
        v = delete_intervals(F.instance, source, intervals)
        assert v == word_from_counts((1,) * r) and agreement_profile(F.instance, v) == P
        pump_rows.append(dict(blocks=r, states=len(F.instance.delta), source=source,
                              source_budget=word_budget(F.instance, source), minimum_disjoint_deletions=r,
                              replacement=v, replacement_budget=word_budget(F.instance, v),
                              intervals=intervals, shorter_dominated_words=len(good)))
        # Enumerate every zero-, one-, and two-loop deletion on the r=3 witness.
        if r == 3:
            c = F.instance.run(source)
            loops = [(a,b) for a in range(len(source)) for b in range(a+1,len(source)) if c[a] == c[b]]
            sets = [()] + [(loop,) for loop in loops]
            sets += [(x,y) for x in loops for y in loops if x[1] <= y[0]]
            for cuts in sets:
                out = delete_intervals(F.instance, source, cuts)
                if cuts:
                    assert not agreement_profile(F.instance, out) <= P
                counts['deletion_sets'] += 1

    growth = []
    for m in range(2, 13):
        F = make_family(range(1, m+1))
        k = len(F.instance.delta)
        assert k == 1 + m*(m+3)//2
        assert F.common_period * (m+1) >= 2**m
        growth.append(dict(m=m, states=k, subtype_variables=2*k+1,
                           lcm=F.common_period, exact_budget_from_proof=F.exact_budget,
                           shortest_length_from_proof=F.shortest_length))
    hashes = {}
    for path in ('border_lab.py', 'terminal_realization.py', 'denial_bridge.py'):
        data = (ROOT/'experiments'/path).read_bytes()
        hashes[path] = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    result = dict(status='PASS', counts=counts, dependency_git_blobs=hashes,
                  primary=dict(instance=encode(I), word=w, run=I.run(w), budget=7,
                               rejected_bound=6, accepted_shorter_words=accepted_shorter,
                               profile_dominated_shorter_words=dominated_shorter,
                               all_budget_splits=primary_rows,
                               subtype_variables=R.variables, subtype_constraints=R.constraints,
                               query=[R.alpha,R.beta], full_summary_states=len(bridge.instance.delta),
                               reduced_summary_states=len(small.delta)),
                  other_families=family_rows, multi_pump=pump_rows, superpolynomial_family=growth,
                  proof_status='Written all-length proofs; not Lean-checked or independently reviewed',
                  limitations='Finite tests are regressions; growth formulas for unsearched parameters rely on the written proof. No unrestricted decision is claimed.')
    destination=ROOT/'results'/'modular-synchronization.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status=result['status'], counts=counts,
                         primary_budget=7, primary_states=8, primary_word=w,
                         exact_negative_lower_budget_splits=sum(r['L']+r['D']<7 for r in primary_rows),
                         subtype_variables=R.variables, full_summary_states=len(bridge.instance.delta)), indent=2))


if __name__ == '__main__':
    main()
