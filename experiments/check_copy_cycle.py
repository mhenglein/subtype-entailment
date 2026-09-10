"""Deterministic finite checks for the all-length copy-cycle arguments.

Finite samples are NOT a nonrationality proof; the note supplies that proof.
The filtered solver is exact only for its supplied shared-block family.
"""
import hashlib
import itertools
import json
import random
from collections import Counter
from pathlib import Path
from border_lab import Instance, witness, border_witness, words
from copy_cycle import (UNARY_FLAGS, unary_instance, copy_instance, candidate,
                        parse_candidate, predicts_unary, equal_coefficient,
                        two_flag_coefficient, accelerate_copy_cycle, block)

ROOT = Path(__file__).resolve().parents[1]


def accepted_through(I, limit):
    pending = [('', I.start)]
    while pending:
        w, p = pending.pop()
        if p in I.final:
            yield w
        if len(w) < limit:
            for a, q in enumerate(I.delta[p]):
                if q >= 0:
                    pending.append((w+str(a), q))


def dictionary_dfa(dictionary):
    paths, table, final = {'': 0}, [[-1, -1]], set()
    for w in sorted(set(dictionary)):
        prefix = ''
        for a in w:
            nxt = prefix+a
            if nxt not in paths:
                paths[nxt] = len(table)
                table.append([-1, -1])
            table[paths[prefix]][int(a)] = paths[nxt]
            prefix = nxt
        final.add(paths[prefix])
    return Instance(tuple(map(tuple, table)), frozenset(final))


def length_dfa(length):
    return Instance(tuple((q+1, q+1) if q < length else (-1, -1)
                          for q in range(length+1)), frozenset({length}))


def main():
    rng = random.Random(2026091071)
    counts = Counter()
    U, C = unary_instance(), copy_instance()
    flags = tuple(sorted(UNARY_FLAGS))
    variants = [unary_instance(frozenset(flags[i] for i in range(3) if mask >> i & 1))
                for mask in range(8)]
    for w in words('01', 16):
        parsed = parse_candidate(w)
        expected = parsed is not None and all(u == parsed[1] for u in parsed[0])
        assert C.admissible(w) == (parsed is not None)
        assert witness(C, w) == border_witness(C, w) == expected
        counts['raw_general_words'] += 1
        for I in variants:
            assert witness(I, w) == border_witness(I, w) == predicts_unary(w, I.flags)
            counts['raw_unary_annotation_words'] += 1
    vocabulary = tuple(w for w in words('01', 3) if w)
    for m in range(1, 4):
        for _ in range(450):
            early = tuple(rng.choice(vocabulary) for _ in range(m))
            last = rng.choice(vocabulary)
            w = candidate(early, last)
            assert parse_candidate(w) == (early, last)
            assert witness(C, w) == border_witness(C, w) == all(u == last for u in early)
            counts['data_tuples'] += 1
    for m in range(1, 5):
        for ns in itertools.product(range(1, 5), repeat=m):
            for n in range(1, 5):
                w = candidate(('1'*v for v in ns), '1'*n)
                for I in variants:
                    assert witness(I, w) == border_witness(I, w) == predicts_unary(w, I.flags)
                    counts['unary_tuple_annotations'] += 1

    # Complete accepted-language enumeration, not only words expected positive.
    observed = Counter()
    two = Counter()
    I2 = unary_instance({(2, 4), (1, 3)})
    one = unary_instance({(2, 4)})
    one_observed = Counter()
    for w in accepted_through(U, 42):
        assert parse_candidate(w, unary=True) is not None
        for I, store in ((U, observed), (I2, two), (one, one_observed)):
            yes = witness(I, w)
            assert yes == border_witness(I, w) == predicts_unary(w, I.flags)
            store[len(w)] += int(yes)
        counts['complete_accepted_words'] += 1
    for length in range(43):
        assert observed[length] == equal_coefficient(length)
        assert two[length] == two_flag_coefficient(length)
        counts['enumerated_length_coefficients'] += 2

    # Independent coefficient expansion of the one-flag series in t=z^2:
    # t^3 sum_{a>=2} t^a/(1-t-t^a).
    one_formula = [0]*22
    for a in range(2, 22):
        inverse = [0]*22
        inverse[0] = 1
        for j in range(1, 22):
            inverse[j] = inverse[j-1] + (inverse[j-a] if j >= a else 0)
        for j in range(22-3-a):
            one_formula[3+a+j] += inverse[j]
    for j in range(22):
        assert one_observed[2*j] == one_formula[j], (j, one_observed[2*j], one_formula[j])
        counts['one_flag_series_coefficients'] += 1

    # Coefficients derived independently by enumerating factor pairs.
    factor = Counter()
    for a in range(2, 501):
        for b in range(2, 501//a+1):
            factor[2*a*b+2] += 1
    for N in range(1, 501):
        got = equal_coefficient(2*N+2)
        assert got == factor[2*N+2]
        composite = N >= 4 and any(N % d == 0 for d in range(2, int(N**.5)+1))
        assert (got > 0) == composite
        counts['factor_coefficients'] += 1

    # Every code block used by acceleration is unbordered and primitive.
    for u in (w for w in words('01', 8) if w):
        B = block(u)
        assert all(B[:j] != B[-j:] for j in range(1, len(B)))
        counts['unbordered_blocks'] += 1
    for u in (w for w in words('01', 2) if w):
        B = block(u)
        for v in words('01', 10):
            expected = bool(v) and len(v) % len(B) == 0 and v == B*(len(v)//len(B))
            assert (bool(v) and v+B == B+v) == expected
            counts['commutation_words'] += 1
    assert '11'+'1111' == '1111'+'11' and len('11') % len('1111') != 0
    counts['primitivity_guards'] += 1

    # Complete independent oracle for all total 2-state binary filters.
    totals = Counter()
    for tr in itertools.product(range(2), repeat=4):
        for mask in range(4):
            D = Instance((tr[:2], tr[2:]), frozenset(q for q in range(2) if mask >> q & 1))
            # At most (d+1)^d=9 actions. The data automaton has one state.
            # Any accepting data action has a positive representative <=18;
            # here use a distinct, complete REGULAR parity-length oracle:
            # direct graph of actions is avoided by enumerating all data words
            # only through 4: two-state total DFA transformations form at most
            # the four maps on two states, with identity/data-code transitions.
            candidate_found = any(D.admissible(candidate((u,)*m, u))
                                  for u in words('01', 4) if u for m in (1, 2))
            out = accelerate_copy_cycle(D, max_states=None, max_work=None, max_output_length=None)
            assert (out['status'] == 'YES') == candidate_found, (D, out)
            assert out['status'] != 'UNKNOWN'
            totals[out['status']] += 1
            counts['two_state_filters'] += 1
    # For each modulus every residue class is a complete cyclic oracle.
    modulo = Counter()
    for d in range(1, 17):
        for residue in range(d):
            D = Instance(tuple(((q+1) % d, (q+1) % d) for q in range(d)), frozenset({residue}))
            expected = any((2*a*b+2) % d == residue for a in range(2, d+2) for b in range(2, d+2))
            out = accelerate_copy_cycle(D, max_states=None, max_work=None, max_output_length=None)
            assert (out['status'] == 'YES') == expected, (d, residue, out)
            modulo[out['status']] += 1
            counts['modular_filters'] += 1
    # Complete finite-domain oracles, including regular constraints on data.
    finite = Counter()
    good_pool = [candidate((u,)*m, u) for u in vocabulary for m in (1, 2, 3)]
    for trial in range(90):
        selected = set(rng.sample(good_pool, rng.randrange(0, 6)))
        selected.update(''.join(rng.choice('01') for _ in range(rng.randrange(0, 20)))
                        for _ in range(rng.randrange(1, 7)))
        data_words = set(rng.sample(vocabulary, rng.randrange(0, len(vocabulary)+1)))
        if trial % 3 == 0:
            data_words.add('')  # Empty data remains excluded by the family.
        D, L = dictionary_dfa(selected), dictionary_dfa(data_words)
        expected = False
        for w in selected:
            parsed = parse_candidate(w)
            expected |= bool(parsed is not None and parsed[1] in data_words and witness(C, w))
            counts['finite_filter_words'] += 1
        out = accelerate_copy_cycle(D, L, max_states=None, max_work=None, max_output_length=None)
        assert (out['status'] == 'YES') == expected and out['status'] != 'UNKNOWN', (trial, out)
        finite[out['status']] += 1
        counts['finite_filters'] += 1
    exact = []
    for N in range(2, 25):
        D = length_dfa(2*N+2)
        out = accelerate_copy_cycle(D, max_states=None, max_work=None, max_output_length=None)
        assert (out['status'] == 'YES') == (equal_coefficient(2*N+2) > 0)
        exact.append(dict(N=N, length=2*N+2, status=out['status']))
        counts['exact_length_filters'] += 1

    ALL = Instance(((0, 0),), frozenset({0}))
    caps = []
    for kw in (dict(max_states=1), dict(max_work=1), dict(max_output_length=1)):
        out = accelerate_copy_cycle(ALL, **kw)
        assert out['status'] == 'UNKNOWN'
        caps.append(out['reason'])
        counts['caps'] += 1
    try:
        accelerate_copy_cycle(unary_instance())
        raise AssertionError('Flagged filter was accepted')
    except ValueError:
        counts['input_guards'] += 1

    # Selected exact arbitrary-tree semantic checks, not finite-depth trees.
    from terminal_realization import realize
    from denial_bridge import Canonical
    semantic = []
    for I, cases in ((U, [(('1',), '1'), (('1','1'), '1'), (('1',), '11'),
                          (('11',), '1')]),
                     (C, [(('01',), '01'), (('01','01'), '01'),
                          (('01',), '10'), (('10','01'), '01')])):
        R = realize(I)
        for prior, tail in cases:
            w = candidate(prior, tail)
            errors = Canonical(R.variables, R.constraints, R.alpha, R.beta, w).errors()
            assert (not errors) == witness(I, w)
            counts['canonical_paths'] += 1
        semantic.append(dict(states=len(I.delta), variables=R.variables,
                             constraints=len(R.constraints)))
    # Source capture's one-visit normalization has no target-wise dual.
    T = Instance(((2,-1),(4,3),(1,3),(0,2),(-1,-1)), frozenset({4}),
                 frozenset({(0,2),(1,2),(3,2)}))
    assert witness(T,'01100') and border_witness(T,'01100')
    assert not witness(T,'000')
    one_visit = set()
    for w in accepted_through(T, 12):
        if T.run(w).count(2) <= 1:
            one_visit.add(w)
        assert witness(T,w) == border_witness(T,w)
        counts['single_target_words'] += 1
    assert one_visit == {'000'}
    raw = (ROOT/'experiments/border_lab.py').read_bytes()
    return dict(status='PASS', seed=2026091071,
                base='2e431ff3d74d3ab1268866f86e24fd835ffe7fda',
                counts=dict(counts), two_state_filters=dict(totals), modular_filters=dict(modulo),
                finite_filters=dict(finite), exact_length_filters=exact, cap_guards=caps,
                simplest=accelerate_copy_cycle(ALL), semantic_realizations=semantic,
                single_target_fixture=dict(delta=T.delta, flags=sorted(T.flags), witness='01100',
                                           sole_one_visit_candidate='000'), unary_table=U.delta,
                unary_flags=sorted(U.flags), general_table=C.delta, general_flags=sorted(C.flags),
                coefficient_rows=[dict(length=2*N+2, equal=equal_coefficient(2*N+2),
                                       two_flags=two_flag_coefficient(2*N+2)) for N in range(4, 31)],
                border_lab_blob=hashlib.sha1(('blob %d\0'%len(raw)).encode()+raw).hexdigest(),
                proof_status='Written proofs; not independently reviewed or Lean-checked',
                scope='Fixed explicit families and supplied regular filters, not unrestricted BorderAvoid')


if __name__ == '__main__':
    result = main()
    target = ROOT/'results/copy-cycle.json'
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status','counts','two_state_filters','modular_filters','finite_filters')}, indent=2))
