#!/usr/bin/env python3
"""Independent regression for the five-state all-length NO certificate.

The quantified proof is in notes/2026-09-08-five-state-no-certificate.md.
This script does not turn bounded testing into a theorem. It independently
implements the automaton run, suffix-agreement predicate, the three symbolic
certificate branches, and the special Necessary(L,D) identity used by the
all-budget obstruction.
"""

from itertools import product
import json
from pathlib import Path

DELTA = (
    (2, 1),
    (2, 1),
    (-1, 3),
    (4, 3),
    (-1, -1),
)
FINAL = frozenset({4})
FLAGS = frozenset({(0, 2), (0, 3), (1, 2)})


def run(word):
    q = 0
    states = [q]
    for ch in word:
        if ch not in "01":
            return None
        q = DELTA[q][ord(ch) - ord("0")]
        if q < 0:
            return None
        states.append(q)
    return tuple(states)


def accepted(word):
    states = run(word)
    return states is not None and states[-1] in FINAL


def violations(word):
    states = run(word)
    if states is None or states[-1] not in FINAL:
        return ()
    out = []
    n = len(word)
    for i in range(n + 1):
        for j in range(i, n + 1):
            if (states[i], states[j]) in FLAGS and word[i:].startswith(word[j:]):
                out.append((i, j, states[i], states[j]))
    return tuple(out)


def witness(word):
    return accepted(word) and not violations(word)


def necessary(word, L, D):
    if not accepted(word):
        return False
    n = len(word)
    for i, j, _p, _q in violations(word):
        suffix_length = n - j
        gap = j - i
        if suffix_length <= L or gap <= D:
            return False
    return True


def candidate(n, m):
    assert n >= 0 and m >= 1
    return "1" * n + "0" + "1" * m + "0"


def certificate(n, m):
    """Return (case, i, j, expected flagged pair) for an accepted candidate."""
    if n < m:
        # The target begins exactly n ones before the final zero.
        return "n<m", 0, m + 1, (0, 3)
    if n == m:
        # The target is the entry to the second 1-block.
        return "n=m", 0, n + 1, (0, 2)
    # Start in the first block exactly m ones before its zero.
    return "n>m", n - m, n + 1, (1, 2)


def check_certificate(n, m):
    word = candidate(n, m)
    states = run(word)
    case, i, j, pair = certificate(n, m)
    assert states is not None and states[-1] == 4
    assert (states[i], states[j]) == pair
    assert pair in FLAGS
    assert word[i:].startswith(word[j:])
    return case


def parse_candidate(word):
    zeroes = [i for i, ch in enumerate(word) if ch == "0"]
    if len(zeroes) != 2 or zeroes[-1] != len(word) - 1:
        return None
    n = zeroes[0]
    m = zeroes[1] - zeroes[0] - 1
    if m < 1 or word != candidate(n, m):
        return None
    return n, m


def main():
    branch_counts = {"n<m": 0, "n=m": 0, "n>m": 0}
    parameter_candidates = 0
    for n in range(33):
        for m in range(1, 33):
            word = candidate(n, m)
            assert accepted(word)
            case = check_certificate(n, m)
            branch_counts[case] += 1
            parameter_candidates += 1
            assert not witness(word)

    binary_words = 0
    accepted_words = 0
    parsed_accepted_words = 0
    certified_accepted_words = 0
    witnesses = 0
    for length in range(13):
        for bits in product("01", repeat=length):
            word = "".join(bits)
            binary_words += 1
            if not accepted(word):
                continue
            accepted_words += 1
            parsed = parse_candidate(word)
            assert parsed is not None
            parsed_accepted_words += 1
            n, m = parsed
            check_certificate(n, m)
            certified_accepted_words += 1
            if witness(word):
                witnesses += 1

    necessary_identity_checks = 0
    unique_violation_checks = 0
    for n in range(25):
        word = candidate(n, n + 1)
        actual = violations(word)
        assert len(actual) == 1
        i, j, p, q = actual[0]
        assert (i, j, p, q) == (0, n + 2, 0, 3)
        unique_violation_checks += 1
        for L in range(13):
            for D in range(13):
                got = necessary(word, L, D)
                expected = n + 1 > L and n + 2 > D
                assert got == expected
                necessary_identity_checks += 1

    result = {
        "status": "PASS",
        "proof_status": (
            "Written all-length three-case certificate; bounded regression is "
            "supporting evidence only; not Lean-checked or independently reviewed"
        ),
        "scope": (
            "The fixed five-state terminal instance from the C051/#9 obstruction. "
            "This is not a complete NO-certificate calculus for arbitrary instances."
        ),
        "parameter_grid": {
            "n": "0..32",
            "m": "1..32",
            "candidates": parameter_candidates,
            "branches": branch_counts,
        },
        "binary_census": {
            "max_length": 12,
            "words": binary_words,
            "accepted": accepted_words,
            "parsed_accepted": parsed_accepted_words,
            "certified_accepted": certified_accepted_words,
            "witnesses": witnesses,
        },
        "all_budget_regression": {
            "special_family_n": "0..24",
            "L": "0..12",
            "D": "0..12",
            "unique_violation_checks": unique_violation_checks,
            "necessary_identity_checks": necessary_identity_checks,
        },
    }

    out = Path(__file__).resolve().parents[1] / "results" / "five-state-no-certificate.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
