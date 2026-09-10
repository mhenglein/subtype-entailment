"""Analytic five-state counterexample to live-source-simple normalization.

Language:
    11 (0* 101)* 0* 11
Flags: (0,1), (2,1).
Both flags are live on accepted runs.  A source-simple accepted word must be
1111, which violates (0,1).  The word 11011 is a witness and visits source 2
twice.  Hence pruning dead flags does not make source-simple normalization
true in general.
"""
import json
from pathlib import Path

from border_lab import Instance, witness, border_witness, words

ROOT = Path(__file__).resolve().parents[1]


def instance():
    # 0 -1-> 1 -1-> 2; 2 loops on 0 and exits on 1 to 3;
    # 3 -1-> final 4 or -0-> 1, making (2,1) genuinely live.
    return Instance(((-1,1),(-1,2),(2,3),(1,4),(-1,-1)),
                    frozenset({4}), frozenset({(0,1),(2,1)}))


def in_formula(w):
    # Parse 11 (0*101)* 0*11 exactly.
    if not w.startswith('11'):
        return False
    i = 2
    n = len(w)
    while True:
        j = i
        while j < n and w[j] == '0':
            j += 1
        if w[j:] == '11':
            return True
        if w[j:j+3] != '101':
            return False
        i = j + 3


def live_pair_on_word(I, pair, w):
    run = I.run(w)
    if run is None:
        return False
    p, q = pair
    return any(run[i] == p and run[j] == q
               for i in range(len(run)) for j in range(i, len(run)))


def source_simple(I, w):
    run = I.run(w)
    sources = {p for p, _ in I.flags}
    return all(run.count(p) <= 1 for p in sources)


def main():
    I = instance()
    assert live_pair_on_word(I, (0,1), '1111')
    assert live_pair_on_word(I, (2,1), '1110111')

    positive = '11011'
    assert I.admissible(positive)
    assert witness(I, positive) and border_witness(I, positive)
    assert not source_simple(I, positive)

    only_source_simple = '1111'
    assert I.admissible(only_source_simple) and source_simple(I, only_source_simple)
    assert not witness(I, only_source_simple)

    checked = accepted = witness_count = simple_accepted = 0
    for w in words('01', 14):
        direct = I.admissible(w)
        assert direct == in_formula(w), (w, direct)
        if direct:
            accepted += 1
            assert witness(I, w) == border_witness(I, w)
            if witness(I, w):
                witness_count += 1
            if source_simple(I, w):
                simple_accepted += 1
                assert w == only_source_simple
                assert not witness(I, w)
        checked += 1

    result = {
        'status': 'PASS',
        'states': 5,
        'language': '11 (0* 101)* 0* 11',
        'flags': [[0,1],[2,1]],
        'both_flags_live': True,
        'witness': positive,
        'witness_source_2_visits': I.run(positive).count(2),
        'only_source_simple_accepted_word': only_source_simple,
        'source_simple_word_is_witness': False,
        'bounded_formula_checks': checked,
        'bounded_accepted_words': accepted,
        'bounded_witnesses': witness_count,
        'bounded_source_simple_accepted_words': simple_accepted,
        'scope': ('All-length counterexample follows from the displayed exact language '
                  'decomposition and source-visit argument; bounded enumeration is regression only.'),
        'consequence': ('Even after exact dead-flag pruning, every witness may need a repeated '
                        'live flagged source. Q004 therefore requires a bound greater than one '
                        'visit per source or a different finite representation.'),
    }
    out = ROOT / 'results' / 'live-source-counterexample.json'
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
