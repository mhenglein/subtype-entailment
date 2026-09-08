"""Reproduce the six-state NO certificate and regular-marking obstruction.

Written all-length proof: notes/2026-09-08-synchronized-tail-and-regular-marking-barrier.md.
The finite checks below are supporting evidence, not the quantified theorem.
Python standard library only. No subtype decision claim.
"""
import json
import random
from collections import Counter
from itertools import product
from pathlib import Path

DELTA = ((1, 2), (1, 2), (3, -1), (3, 4), (5, 2), (-1, -1))
FLAGS = frozenset({(0, 2), (0, 3), (1, 2)})
SEED = 2026090863


def run(word):
    states = [0]
    for letter in word:
        target = DELTA[states[-1]][int(letter)]
        if target < 0:
            return None
        states.append(target)
    return states


def violations(word):
    states = run(word)
    if states is None or states[-1] != 5:
        return []
    rho, n = word[::-1], len(word)
    return [(i, j) for i in range(n + 1) for j in range(i, n + 1)
            if (states[i], states[j]) in FLAGS and rho[:n-j] == rho[j-i:n-i]]


def symbolic_cut(word):
    states = run(word)
    if states is None or states[-1] != 5:
        raise ValueError('An accepted word is required')
    n = len(word) - len(word.lstrip('0'))
    m = len(word[:-2]) - len(word[:-2].rstrip('0'))
    j = len(word) - m - 2
    if n < m:
        return 0, len(word) - n - 2
    if n == m:
        return 0, j
    return n - m, j


def emit(word, marks):
    pieces = [letter + ('#' if mark else '') for letter, mark in zip(word, marks)]
    cuts = [0]
    for piece in pieces:
        cuts.append(cuts[-1] + len(piece))
    return ''.join(pieces), cuts


def annotated_violations(word, encoded, cuts):
    states, n = run(word), len(word)
    return [(i, j) for i in range(n) for j in range(i + 1, n)
            if (states[i], states[j]) in FLAGS
            and encoded[cuts[i]:].startswith(encoded[cuts[j]:])]


def greedy_decoration(word, delta):
    """Exact accepted annotation for a regular relation with final bit 1.

    All-1 stays in accepting state zero in the generated relations. This
    guarantees projection coverage. Suffix viability, not independent local
    choices, selects the lexicographically least accepting bit assignment.
    """
    count = len(delta)
    viable = [set() for _ in range(len(word) + 1)]
    viable[-1] = {0}
    for i in range(len(word) - 1, -1, -1):
        options = (1,) if i == len(word) - 1 else (0, 1)
        viable[i] = {q for q in range(count)
                     if any(delta[q][int(word[i])][b] in viable[i+1] for b in options)}
    assert 0 in viable[0]
    state, marks = 0, []
    for i, letter in enumerate(word):
        options = (1,) if i == len(word) - 1 else (0, 1)
        mark = next(b for b in options if delta[state][int(letter)][b] in viable[i+1])
        marks.append(mark)
        state = delta[state][int(letter)][mark]
    assert state == 0 and marks[-1] == 1
    return marks


def check():
    rng, counts = random.Random(SEED), Counter()
    for length in range(15):
        for bits in product('01', repeat=length):
            word = ''.join(bits)
            states = run(word)
            counts['raw_words_through_14'] += 1
            if states is None or states[-1] != 5:
                continue
            i, j = symbolic_cut(word)
            assert (states[i], states[j]) in FLAGS
            assert word[i:].startswith(word[j:])
            assert (i, j) in violations(word)
            counts['accepted_words_certified'] += 1
    for case in range(300):
        n, m = rng.randrange(12), rng.randrange(1, 12)
        middle = ''.join('0' * rng.randrange(1, 9) + '11' for _ in range(rng.randrange(1, 7)))
        word = '0' * n + '1' + middle + '0' * m + '10'
        assert symbolic_cut(word) in violations(word)
        counts['long_nonflat_certificates'] += 1
    for m in range(1, 65):
        word = '0' * (2*m) + '1' + '0' * m + '10'
        assert violations(word) == [(m, 2*m+1)]
        counts['unique_violation_words'] += 1
    edges = [(p, a) for p, row in enumerate(DELTA) for a, q in enumerate(row) if q >= 0 and q != 5]
    for mask in range(1 << len(edges)):
        marked = {(4, 0)} | {edge for index, edge in enumerate(edges) if mask >> index & 1}
        for H in (0, 1, 2, 4):
            m = H + 2
            word = '0' * (2*m) + '1' + '0' * m + '10'
            states = run(word)
            marks = [(states[i], int(a)) in marked for i, a in enumerate(word)]
            encoded, cuts = emit(word, marks)
            bad = annotated_violations(word, encoded, cuts)
            assert bad in ([], [(m, 2*m+1)])
            assert all(encoded[cuts[j]:].count('#') > H for _, j in bad)
            counts['memoryless_decoration_bound_checks'] += 1
    for case in range(100):
        M, H = rng.randrange(2, 5), case % 4
        delta = [[[rng.randrange(M) for _ in range(2)] for _ in range(2)] for _ in range(M)]
        for a in range(2):
            delta[0][a][1] = 0
        m = (1 << M) + M * (1 << M) * (H + 2)
        word = '0' * (2*m) + '1' + '0' * m + '10'
        encoded, cuts = emit(word, greedy_decoration(word, delta))
        # The independent family proof says this is the ONLY possible pair.
        # Do not claim a quadratic all-cut scan for these larger words.
        i, j = cuts[m], cuts[2*m+1]
        assert not encoded[i:].startswith(encoded[j:]) or encoded[j:].count('#') > H
        counts['regular_relation_greedy_checks'] += 1
    return {'status': 'PASS', 'seed': SEED, 'counts': dict(counts),
            'scope': 'Fixed six-state instance; finite checks support the written all-length theorem; no general subtype decision'}


if __name__ == '__main__':
    result = check()
    output = Path(__file__).resolve().parents[1] / 'results' / 'regular-marking-barrier.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))
