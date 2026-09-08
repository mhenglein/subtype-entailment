"""Reproduce the A017 four-state one-flag minimum-gap counterexample.

Finite checks support the implementation only. The all-r proof is in
notes/2026-09-08-oneflag-minimum-gap.md.
"""
import json
from pathlib import Path
from itertools import product

from border_lab import Instance, witness, border_witness, words

ROOT = Path(__file__).resolve().parents[1]

I = Instance(
    ((0, 2), (3, 0), (1, 1), (-1, -1)),
    frozenset({3}),
    frozenset({(0, 1)}),
)


def violations(word):
    c = I.run(word)
    if c is None or c[-1] not in I.final:
        return []
    n = len(word)
    out = []
    for i in range(n):
        for j in range(i + 1, n):
            if (c[i], c[j]) in I.flags and word[i:].startswith(word[j:]):
                last = not any((c[i+t], c[j+t]) in I.flags
                               for t in range(1, n-j+1))
                out.append((i, j, n-j, last))
    return out


def z(r):
    return '10' + '1' * (3*r + 2) + '0'


def check():
    counts = {
        'parameter_values': 0,
        'family_predicate_checks': 0,
        'enumerated_words': 0,
        'accepted_words': 0,
        'bad_accepted_words': 0,
        'witnesses': 0,
    }
    for r in range(201):
        zz = z(r); w = zz + zz; L = len(zz)
        c = I.run(w)
        assert c is not None and c[-1] == 3 and c[L] == 1
        vs = violations(w)
        assert (0, L, L, True) in vs
        assert (L+1, 2*L-1, 1, True) in vs
        assert min(v[2] for v in vs) == 1
        assert not witness(I, w) and not border_witness(I, w)
        counts['parameter_values'] += 1
        counts['family_predicate_checks'] += 2

    for w in words('01', 14):
        good = witness(I, w)
        assert good == border_witness(I, w)
        vs = violations(w)
        if I.admissible(w):
            counts['accepted_words'] += 1
            assert good == (not vs)
            if good: counts['witnesses'] += 1
            else: counts['bad_accepted_words'] += 1
        counts['enumerated_words'] += 1

    assert witness(I, '100') and witness(I, '110')
    result = {
        'status': 'PASS',
        'instance': {
            'delta': I.delta,
            'final': sorted(I.final),
            'flags': sorted(map(list, I.flags)),
        },
        'family': 'z_r = 10 1^(3r+2) 0; w_r = z_r z_r',
        'proved_properties': [
            'last-aligned violation length 3r+5 for every r>=0',
            'global minimum proper violation length 1 for every r>=0',
            'single forbidden ordered pair only',
        ],
        'counts': counts,
        'limits': [
            'The finite parameter range is not the unbounded proof',
            'Independent mathematical review pending',
            'Not Lean-checked',
            'Does not settle one-flag witness existence or Problem 1.7',
        ],
    }
    (ROOT / 'results').mkdir(exist_ok=True)
    (ROOT / 'results/oneflag-minimum-gap.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    check()
