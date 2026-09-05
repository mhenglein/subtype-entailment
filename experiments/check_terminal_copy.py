"""E029: exact small certificates and independent checks for C046-C049.

Run: python3 experiments/check_terminal_copy.py
The all-parameter results rest on written proofs, not these finite tests.
"""
import hashlib
import itertools
import json
import random
from pathlib import Path

from border_lab import (Instance, Sandwich, border_witness, sufficient,
                        witness, word_budget, words)
from terminal_copy import (DFA, agreement_profile, binary_encode, copy_instance,
                           encode_word, intersection_witness, lcm, lcm_instance)
from terminal_realization import realize
from topfree_bridge import (BottomDenial, NormalizedSystem, ProductLower,
                            ProductUpper, VariableLeq, canonical_countermodel,
                            is_satisfiable)

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026090546


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def as_system(realization):
    forms = {'denial': BottomDenial, 'upper': ProductUpper,
             'lower': ProductLower, 'leq': VariableLeq}
    return NormalizedSystem(forms[t[0]](*t[1:]) for t in realization.constraints)


def copy_formula(automata, word):
    blocks = word.split('#')
    return (len(blocks) == len(automata) + 1 and blocks[-1] == ''
            and len(set(blocks[:-1])) == 1
            and all(m.accepts(u) for m, u in zip(automata, blocks[:-1])))


def decode(word):
    inverse = {'00': '0', '01': '1', '10': '#'}
    if len(word) % 2:
        return None
    try:
        return ''.join(inverse[word[i:i+2]] for i in range(0, len(word), 2))
    except KeyError:
        return None


def independent_intersection(automata):
    """Backward fixed point on the full Cartesian graph; no word cutoff."""
    states = tuple(itertools.product(*(range(len(m.delta)) for m in automata)))
    good = {s for s in states if all(q in m.final for m, q in zip(automata, s))}
    changed = True
    while changed:
        changed = False
        for s in states:
            if s in good:
                continue
            if any(tuple(m.delta[q][a] for m, q in zip(automata, s)) in good
                   for a in range(2)):
                good.add(s)
                changed = True
    return tuple(m.start for m in automata) in good


def check_small():
    I = lcm_instance((2, 3))
    target = ('1'*6 + '0')*2
    assert len(I.delta) == 8 and len(I.flags) == 5
    assert witness(I, target) and border_witness(I, target)
    assert word_budget(I, target) == 7
    rows = []
    for budget in range(8):
        for L in range(budget + 1):
            D = budget - L
            result = Sandwich(I, L, D, True).search(max_states=200000)
            assert result['status'] != 'UNKNOWN'
            if budget < 7:
                assert result['status'] == 'NO'
            if result['status'] == 'YES':
                assert witness(I, result['word']) and border_witness(I, result['word'])
                assert sufficient(I, result['word'], L, D)
            rows.append(dict(L=L, D=D, **result))
    assert any(r['status'] == 'YES' for r in rows)

    profile = agreement_profile(I, target)
    maximal = Instance(I.delta, I.final,
                       frozenset(itertools.product(range(8), repeat=2)) - profile)
    assert I.flags <= maximal.flags and witness(maximal, target)
    maximal_lower = []
    for budget in range(7):
        for L in range(budget + 1):
            result = Sandwich(maximal, L, budget-L, True).search(max_states=200000)
            assert result['status'] == 'NO'
            maximal_lower.append(result['states'])

    checked = accepted = shorter = 0
    positive = []
    for w in words('01', 14):
        checked += 1
        # An independent closed-form specification, including malformed words.
        parts = w.split('0')
        predicted = (len(parts) == 3 and parts[-1] == ''
                     and parts[0] == parts[1] and len(parts[0]) > 0
                     and len(parts[0]) % 6 == 0)
        assert witness(I, w) == border_witness(I, w) == predicted
        if predicted:
            positive.append(w)
        if I.admissible(w):
            accepted += 1
            if len(w) < len(target):
                shorter += 1
                assert not agreement_profile(I, w) <= profile
    assert positive == [target]

    R = realize(I)
    system = as_system(R)
    assert R.variables == 17 and len(R.constraints) == 21 and is_satisfiable(system)
    model_checks = yes_models = 0
    model_metadata = None
    candidates = [('1'*a+'0')+('1'*b+'0')
                  for a in range(2, 13, 2) for b in range(3, 13, 3)]
    candidates += ['', '0', '1', '10', '1010', target]
    for w in candidates:
        model = canonical_countermodel(system, R.alpha, R.beta, w)
        assert (model.status == 'YES') == witness(I, w), (w, model.status, model.errors)
        assert model.status != 'UNSAT'
        model_checks += 1
        yes_models += model.status == 'YES'
        if w == target:
            model_metadata = model.model.as_finite_automaton_data()
    return dict(states=8, delta=I.delta, final=sorted(I.final), flags=sorted(I.flags),
                shortest_witness=target, shortest_length=14, exact_budget=7,
                refuted_bound=6, splits=rows, lower_splits_exhausted=28,
                maximum_search_states=max(r['states'] for r in rows),
                maximal_preserving_flags=len(maximal.flags),
                maximal_lower_splits_exhausted=len(maximal_lower),
                words_checked=checked, accepted_words=accepted,
                shorter_accepted_words=shorter, shorter_dominated_words=0,
                subtype_variables=R.variables, subtype_constraints=R.constraints,
                subtype_query=[R.alpha, R.beta], canonical_checks=model_checks,
                canonical_positive_checks=yes_models, target_model=model_metadata)


def check_family():
    families = list(itertools.product(range(1, 7), repeat=2))
    families += list(itertools.product(range(1, 5), repeat=3))
    comparisons = positives = 0
    for periods in families:
        I = lcm_instance(periods)
        assert len(I.delta) == 1 + len(periods) + sum(periods)
        choices = [range(p, 13, p) for p in periods]
        for exponents in itertools.product(*choices):
            word = ''.join('1'*a + '0' for a in exponents)
            predicted = len(set(exponents)) == 1
            assert witness(I, word) == border_witness(I, word) == predicted
            comparisons += 1
            if predicted:
                expected = (len(periods)-1) * (exponents[0]+1)
                assert word_budget(I, word) == expected
                assert sufficient(I, word, 0, expected)
                positives += 1
    rows = []
    for periods in ((1,1), (1,2), (2,2), (2,3), (2,4), (3,4), (1,2,3)):
        I = lcm_instance(periods)
        exact = (len(periods)-1)*(lcm(periods)+1)
        exhausted = maximum = 0
        for budget in range(exact):
            for L in range(budget+1):
                result = Sandwich(I, L, budget-L, True).search(max_states=200000)
                assert result['status'] == 'NO', (periods, L, budget-L, result)
                maximum = max(maximum, result['states'])
                exhausted += 1
        result = Sandwich(I, 0, exact, True).search(max_states=200000)
        assert result['status'] == 'YES'
        assert witness(I, result['word']) and word_budget(I, result['word']) == exact
        rows.append(dict(periods=periods, states=len(I.delta), exact_budget=exact,
                         lower_splits=exhausted, max_lower_graph_states=maximum,
                         positive=result))
    # Larger numerical values follow the written formula; no giant word is built.
    formula_rows = [dict(periods=p, states=1+len(p)+sum(p), lcm=lcm(p),
                         shortest_length=len(p)*(lcm(p)+1),
                         exact_budget=(len(p)-1)*(lcm(p)+1))
                    for p in ((2,3,5), (2,3,5,7), (2,3,5,7,11))]
    return dict(families=len(families), candidate_words=comparisons,
                positive_budget_checks=positives, exact_search_families=rows,
                larger_formula_only_examples=formula_rows)


def check_copy():
    rng = random.Random(SEED)
    # Include empty words, empty languages, and conflicting singleton languages.
    all_words = DFA(((0, 0),), frozenset({0}))
    empty = DFA(((-1, -1),), frozenset())
    just_empty = DFA(((-1, -1),), frozenset({0}))
    zero = DFA(((1, -1), (-1, -1)), frozenset({1}))
    one = DFA(((-1, 1), (-1, -1)), frozenset({1}))
    fixtures = [(all_words, all_words), (empty, all_words),
                (just_empty, just_empty), (zero, one), (zero, zero),
                (all_words, all_words, all_words)]
    for case in range(120):
        r = 2 + case % 2
        automata = []
        for _ in range(r):
            k = rng.randrange(1, 5)
            delta = tuple(tuple(rng.randrange(-1, k) for _ in range(2)) for _ in range(k))
            final = frozenset(q for q in range(k) if rng.random() < .5)
            automata.append(DFA(delta, final, rng.randrange(k)))
        fixtures.append(tuple(automata))

    count = {'tuples': 0, 'block_candidates': 0, 'block_witnesses': 0,
             'arbitrary_binary_words': 0, 'product_yes': 0, 'product_no': 0,
             'canonical_checks': 0, 'canonical_yes': 0}
    sizes = {'max_ternary_states': 0, 'max_binary_states': 0, 'max_flags': 0}
    for index, automata in enumerate(fixtures):
        I = copy_instance(automata)
        J = binary_encode(I)
        assert len(I.delta) == 1 + len(automata) + 2*sum(len(m.delta) for m in automata)
        assert len(J.delta) <= 3*len(I.delta)
        assert all(set(J.delta[f]) == {-1} for f in J.final)
        sizes['max_ternary_states'] = max(sizes['max_ternary_states'], len(I.delta))
        sizes['max_binary_states'] = max(sizes['max_binary_states'], len(J.delta))
        sizes['max_flags'] = max(sizes['max_flags'], len(J.flags))
        count['tuples'] += 1
        pool = tuple(words('01', 3 if len(automata) == 2 else 2))
        for blocks in itertools.product(pool, repeat=len(automata)):
            w = '#'.join(blocks) + '#'
            expected = len(set(blocks)) == 1 and all(m.accepts(u) for m,u in zip(automata, blocks))
            encoded = encode_word(w)
            assert witness(I, w) == border_witness(I, w) == expected, (index, blocks)
            assert witness(J, encoded) == border_witness(J, encoded) == expected
            count['block_candidates'] += 1
            count['block_witnesses'] += expected
        if index < 24:
            for encoded in words('01', 8):
                w = decode(encoded)
                expected = w is not None and copy_formula(automata, w)
                assert witness(J, encoded) == border_witness(J, encoded) == expected
                count['arbitrary_binary_words'] += 1

        answer = intersection_witness(automata)
        truth = independent_intersection(automata)
        assert answer['status'] == ('YES' if truth else 'NO')
        count['product_yes' if truth else 'product_no'] += 1
        if truth:
            u = answer['word']
            assert all(m.accepts(u) for m in automata)
            w = (u+'#')*len(automata)
            assert witness(I, w) and witness(J, encode_word(w))
        if index < 10:
            R = realize(J)
            system = as_system(R)
            assert is_satisfiable(system)
            candidates = [('#')*len(automata), ('0#')*len(automata),
                          '1#' + ('0#')*(len(automata)-1)]
            if truth:
                candidates.append((answer['word']+'#')*len(automata))
            for w in candidates:
                path = encode_word(w)
                model = canonical_countermodel(system, R.alpha, R.beta, path)
                assert model.status != 'UNSAT'
                assert (model.status == 'YES') == copy_formula(automata, w)
                count['canonical_checks'] += 1
                count['canonical_yes'] += model.status == 'YES'
    # Caps are never reported as NO, and acceptance is checked before expansion.
    assert intersection_witness((zero, zero), max_states=1)['status'] == 'UNKNOWN'
    assert intersection_witness((just_empty, just_empty), max_states=1)['status'] == 'YES'
    assert intersection_witness((empty, empty), max_states=1)['status'] == 'NO'
    invalid = [lambda: lcm_instance(()), lambda: lcm_instance((2,0)),
               lambda: lcm_instance((True,3)), lambda: copy_instance((zero,)),
               lambda: DFA((), frozenset()), lambda: DFA(((2,-1),),frozenset()),
               lambda: binary_encode(lcm_instance((2,3))), lambda: encode_word('x'),
               lambda: intersection_witness((zero,)),
               lambda: intersection_witness((zero,zero),max_states=0)]
    for action in invalid:
        try:
            action()
        except ValueError:
            continue
        raise AssertionError('Invalid input was accepted')
    return dict(counts=count, sizes=sizes, cap_regressions=3, invalid_inputs=len(invalid))


def main():
    result = dict(status='PASS', seed=SEED, base_commit='2c6b4aac57634bf2b802c1bf4fae323862fd21e1',
                  scope='C046-C049: terminal LCM synchronization and regular-copy reduction',
                  small=check_small(), family=check_family(), copy=check_copy(),
                  source_blobs={name: git_blob(ROOT/'experiments'/name)
                                for name in ('border_lab.py', 'topfree_bridge.py',
                                             'terminal_realization.py', 'terminal_copy.py')},
                  limitations=['Written proofs, not Lean-checked or independently refereed.',
                               'Finite comparisons do not prove the all-input reductions.',
                               'No unrestricted decision or polynomial-space upper bound.'])
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results/terminal-copy.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
