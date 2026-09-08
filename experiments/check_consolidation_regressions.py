"""Regressions discovered during the September 8 open-PR consolidation."""
import json
from pathlib import Path

from border_lab import words, witness, border_witness
from check_oneflag_minimum_gap import I, violations
from run_profiles import join_runs

ROOT = Path(__file__).resolve().parents[1]


def check():
    # PR #12: validation must not consume a single-pass iterable.
    expected = '10110'
    assert join_runs([1, 2], '0') == expected
    assert join_runs((1, 2), '0') == expected
    assert join_runs(iter([1, 2]), '0') == expected

    # PR #14: the strengthened statement concerns the entire bad language,
    # not only the displayed square subfamily.
    accepted = bad = good = 0
    for w in words('01', 16):
        fw = witness(I, w)
        assert fw == border_witness(I, w)
        if not I.admissible(w):
            continue
        accepted += 1
        vs = violations(w)
        assert fw == (not vs)
        if vs:
            bad += 1
            assert min(v[2] for v in vs) == 1
        else:
            good += 1

    assert (accepted, bad, good) == (2564, 2502, 62)
    result = {
        'status': 'PASS',
        'join_runs_iterable_forms': 3,
        'oneflag_words_through_length_16': 131071,
        'oneflag_accepted_words': accepted,
        'oneflag_bad_accepted_words': bad,
        'oneflag_witnesses': good,
        'scope': 'Integration regressions; finite tests support but do not replace written all-length proofs',
    }
    path = ROOT / 'results' / 'consolidation-regressions.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    check()
