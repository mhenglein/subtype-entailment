"""E032: exact small intersections, binary synchronization, and counting words.

Finite evidence is separate from the written quantified statements.
No timeout or exploration cap is interpreted as an empty language.
"""
import hashlib
import itertools
import json
import random
from pathlib import Path

from border_lab import words, witness, border_witness
from word_sync import BinaryDFA, compile_sync, encode_blocks, decode_blocks, solve_sync
from counter_intersection import counting_dfas, counting_word
from terminal_realization import realize
from denial_bridge import build, reduced, Canonical

ROOT = Path(__file__).resolve().parents[1]


def direct_product(Ms):
    """Independent finite reachability, without witness reconstruction."""
    frontier = {tuple(m.start for m in Ms)}
    seen = set()
    while frontier:
        current = frontier.pop()
        if current in seen:
            continue
        seen.add(current)
        if all(q in m.final for q, m in zip(current, Ms)):
            return True
        for a in (0, 1):
            nxt = tuple(m.delta[q][a] for m, q in zip(Ms, current))
            if all(q >= 0 for q in nxt) and nxt not in seen:
                frontier.add(nxt)
    return False


def check():
    counts = dict(binary_words=0, block_tuples=0, product_decisions=0,
                  two_state_complete_pairs=0, direct_intersection_words=0,
                  canonical_models=0, summary_comparisons=0,
                  counter_bit_flips=0, counter_small_words=0,
                  grammar_factor_fixtures=0, capped_queries=0)
    U = BinaryDFA(((0, 0),), frozenset({0}))
    universal = compile_sync((U, U))
    assert len(universal.instance.delta) == 11 and len(universal.instance.flags) == 6
    # Includes invalid phases, missing separators, extra stages, empty blocks.
    for w in words('01', 14):
        expected = universal.predicts(w)
        assert witness(universal.instance, w) == border_witness(universal.instance, w) == expected
        counts['binary_words'] += 1
    for r, depth in ((2, 4), (3, 2), (4, 1)):
        F = compile_sync([U]*r)
        for blocks in itertools.product(tuple(words('01', depth)), repeat=r):
            w = encode_blocks(blocks)
            assert decode_blocks(w) == blocks
            expected = len(set(blocks)) == 1
            assert witness(F.instance, w) == border_witness(F.instance, w) == expected
            counts['block_tuples'] += 1
    mismatch = encode_blocks(('01', '10'))
    assert not witness(universal.instance, mismatch)
    assert witness(universal.instance, encode_blocks(('01', '01')))

    # Every pair of total 2-state DFAs, start 0: 16 tables * 4 final sets each.
    automata = []
    for tr in itertools.product(range(2), repeat=4):
        for mask in range(4):
            automata.append(BinaryDFA((tr[:2], tr[2:]),
                                     frozenset(q for q in range(2) if mask >> q & 1)))
    possible = impossible = 0
    short = tuple(words('01', 3))  # Four product states: shortest word <=3.
    for M, N in itertools.product(automata, repeat=2):
        expected_words = [u for u in short if M.accepts(u) and N.accepts(u)]
        counts['direct_intersection_words'] += len(short)
        answer = solve_sync((M, N), max_states=None)
        counts['product_decisions'] += 1
        counts['two_state_complete_pairs'] += 1
        assert (answer['status'] == 'YES') == bool(expected_words)
        if expected_words:
            possible += 1
            assert answer['common_word'] == expected_words[0]
        else:
            impossible += 1
            assert answer['status'] == 'NO'

    rng = random.Random(2026090548)
    generated_rows = []
    candidates = tuple(words('01', 3))
    for trial in range(120):
        r = rng.randrange(2, 5)
        Ms = []
        for _ in range(r):
            n = rng.randrange(1, 5)
            Ms.append(BinaryDFA(tuple(tuple(rng.randrange(-1, n) for _ in range(2))
                                      for _ in range(n)),
                                frozenset(q for q in range(n) if rng.random() < .45),
                                rng.randrange(n)))
        F = compile_sync(Ms)
        for _ in range(20):
            blocks = tuple(rng.choice(candidates) for _ in Ms)
            w = encode_blocks(blocks)
            expected = len(set(blocks)) == 1 and all(m.accepts(u) for m, u in zip(Ms, blocks))
            assert F.predicts(w) == witness(F.instance, w) == border_witness(F.instance, w) == expected
            counts['block_tuples'] += 1
        answer = solve_sync(Ms, max_states=None)
        assert (answer['status'] == 'YES') == direct_product(Ms)
        counts['product_decisions'] += 1
        generated_rows.append(dict(trial=trial, status=answer['status'],
                                   compiled_states=answer['compiled_states'],
                                   explored_states=answer['explored_states']))

    starts0 = BinaryDFA(((1, -1), (1, 1)), frozenset({1}))
    starts1 = BinaryDFA(((-1, 1), (1, 1)), frozenset({1}))
    no = solve_sync((starts0, starts1), max_states=None)
    assert no['status'] == 'NO'
    yes_nonempty = solve_sync((starts0, starts0), max_states=None)
    assert yes_nonempty['common_word'] == '0'
    cap = solve_sync((starts0, starts0), max_states=1)
    assert cap['status'] == 'UNKNOWN'
    counts['capped_queries'] += 1
    try:
        compile_sync([U])
        raise AssertionError('Missing arity guard')
    except ValueError:
        pass
    try:
        BinaryDFA(((2, 0),), frozenset({0}))
        raise AssertionError('Missing transition guard')
    except ValueError:
        pass

    # Semantic bridge and exact canonical regular countermodels.
    for Ms in ((U, U), (starts0, starts1), (starts0, starts0), counting_dfas(1)):
        F = compile_sync(Ms)
        R = realize(F.instance)
        status, B = build(R.variables, R.constraints, R.alpha, R.beta, max_classes=10000)
        assert status == 'SAT'
        red, _ = reduced(B, R.alpha, R.beta, max_classes=10000)
        assert red is not None
        data = tuple(words('01', 2))
        for blocks in itertools.product(data, repeat=len(Ms)):
            w = encode_blocks(blocks)
            expected = F.predicts(w)
            assert witness(B.instance, w) == witness(red, w) == expected
            counts['summary_comparisons'] += 1
        fixture_blocks = [tuple('' for _ in Ms), tuple('0' for _ in Ms),
                          tuple('01' for _ in Ms), tuple('10' for _ in Ms),
                          tuple('0' if i == 0 else '1' for i in range(len(Ms)))]
        for blocks in fixture_blocks:
            w = encode_blocks(blocks)
            errors = Canonical(R.variables, R.constraints, R.alpha, R.beta, w).errors()
            assert (not errors) == F.predicts(w), (blocks, errors)
            counts['canonical_models'] += 1

    counter_rows = []
    for width in range(1, 7):
        Ms = counting_dfas(width)
        c = counting_word(width)
        answer = solve_sync(Ms, max_states=None)
        counts['product_decisions'] += 1
        assert answer['status'] == 'YES' and answer['common_word'] == c
        expected_length = (width+1)*(2*width*(1 << width)+2)
        assert answer['shortest_length'] == expected_length
        for j in range(len(c)):
            flipped = c[:j] + ('1' if c[j] == '0' else '0') + c[j+1:]
            assert not all(m.accepts(flipped) for m in Ms)
            counts['counter_bit_flips'] += 1
        for shorter in (c[:-1], c[:width], c + c, c + '0'*width):
            assert not all(m.accepts(shorter) for m in Ms)
        w = answer['word']
        ell = 2*width
        factors = {w[j:j+ell] for j in range(len(w)-ell+1)}
        for value in range(1 << width):
            block = format(value, '0%db' % width)[::-1]
            assert encode_blocks((block,))[:-2] in factors
        if width <= 2:
            for candidate in words('01', len(c)):
                assert all(m.accepts(candidate) for m in Ms) == (candidate == c)
                counts['counter_small_words'] += 1
        counter_rows.append(dict(width=width, input_dfas=len(Ms),
                                  input_states=sum(len(m.delta) for m in Ms),
                                  compiled_states=answer['compiled_states'],
                                  compiled_flags=answer['compiled_flags'],
                                  common_word_length=len(c), witness_length=len(w),
                                  explored_product_states=answer['explored_states'],
                                  distinct_factors=len(factors), factor_length=ell,
                                  skeleton_body_lower_bound=(len(factors)+ell-1)//ell))

    for _ in range(300):
        parts = [rng.choice(('0', '1', '01', '10', '001', '110'))
                 for _ in range(rng.randrange(1, 6))]
        powers = [rng.randrange(0, 8) for _ in parts]
        text = ''.join(p*n for p, n in zip(parts, powers))
        body = sum(map(len, parts))
        for ell in range(1, min(12, len(text))+1):
            factors = {text[i:i+ell] for i in range(len(text)-ell+1)}
            assert len(factors) <= body*ell
            counts['grammar_factor_fixtures'] += 1

    def git_blob(path):
        raw = path.read_bytes()
        return hashlib.sha1(('blob %d\0' % len(raw)).encode()+raw).hexdigest()
    return dict(status='PASS', seed=2026090548, counts=counts,
                two_state_census=dict(YES=possible, NO=impossible),
                random_decisions={s:sum(r['status']==s for r in generated_rows)
                                  for s in ('YES','NO','UNKNOWN')},
                fixtures=dict(equal_counts_unequal_words=mismatch,
                              negative_product=no, positive_nonempty=yes_nonempty,
                              capped=cap),
                counting_family=counter_rows,
                dependency_blobs={p:git_blob(ROOT/'experiments'/p)
                                  for p in ('border_lab.py','terminal_realization.py','denial_bridge.py')},
                proof_status='Written arguments; not Lean-checked or independently reviewed',
                scope='Construction-specific exact decision, not unrestricted BorderAvoid')


if __name__ == '__main__':
    out = check()
    (ROOT/'results/word-synchronization.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))
