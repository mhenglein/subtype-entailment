#!/usr/bin/env python3
"""Independent regression for the regular-middle erasure NO rule.

The quantified proof is in notes/2026-09-08-regular-middle-erasure.md.
Finite checks below support that proof; they are not a substitute for it.
"""

from itertools import product
import json
from pathlib import Path

DELTA = (
    (1, 2),
    (1, 2),
    (3, -1),
    (3, 4),
    (5, 2),
    (-1, -1),
)
FINAL = frozenset({5})
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
        for j in range(i + 1, n):
            if (states[i], states[j]) in FLAGS and word[i:].startswith(word[j:]):
                out.append((i, j, states[i], states[j]))
    return tuple(out)


def parse_middle(middle):
    """Parse (0^+ 11)*, returning the tuple of positive zero-run lengths."""
    pos = 0
    runs = []
    while pos < len(middle):
        start = pos
        while pos < len(middle) and middle[pos] == "0":
            pos += 1
        r = pos - start
        if r < 1 or middle[pos:pos + 2] != "11":
            return None
        runs.append(r)
        pos += 2
    return tuple(runs)


def parse_candidate(word):
    """Return (n,m,middle,runs,j) for accepted 0^n1 M 0^m10 words."""
    if not accepted(word) or not word.endswith("10"):
        return None

    n = 0
    while n < len(word) and word[n] == "0":
        n += 1
    if n >= len(word) or word[n] != "1":
        return None

    pos = len(word) - 3
    m = 0
    while pos >= 0 and word[pos] == "0":
        m += 1
        pos -= 1
    if m < 1:
        return None

    j = len(word) - m - 2
    middle = word[n + 1:j]
    runs = parse_middle(middle)
    if runs is None:
        return None
    return n, m, middle, runs, j


def certificate(word):
    parsed = parse_candidate(word)
    if parsed is None:
        raise ValueError("word is not an accepted benchmark candidate")
    n, m, _middle, _runs, j = parsed
    N = len(word)
    if n < m:
        return "n<m", 0, N - n - 2, (0, 3)
    if n == m:
        return "n=m", 0, j, (0, 2)
    return "n>m", n - m, j, (1, 2)


def check_certificate(word):
    states = run(word)
    case, i, j, pair = certificate(word)
    assert states is not None and states[-1] == 5
    assert (states[i], states[j]) == pair
    assert pair in FLAGS
    assert word[i:].startswith(word[j:])
    return case


def erase_middle(word):
    n, m, _middle, _runs, _j = parse_candidate(word)
    return "0" * n + "1" + "0" * m + "10"


def middle_word(runs):
    return "".join("0" * r + "11" for r in runs)


def main():
    binary_words = 0
    accepted_words = 0
    parsed_accepted_words = 0
    certified_accepted_words = 0
    witnesses = 0

    for length in range(15):
        for bits in product("01", repeat=length):
            word = "".join(bits)
            binary_words += 1
            if not accepted(word):
                continue
            accepted_words += 1
            parsed = parse_candidate(word)
            assert parsed is not None
            parsed_accepted_words += 1
            check_certificate(word)
            certified_accepted_words += 1
            if not violations(word):
                witnesses += 1

    branches = {"n<m": 0, "n=m": 0, "n>m": 0}
    structured_candidates = 0
    nonempty_middle = 0
    erasure_checks = 0
    max_word_length = 0

    middle_runs = [()]
    for blocks in range(1, 4):
        middle_runs.extend(product(range(1, 4), repeat=blocks))

    for n in range(13):
        for m in range(1, 13):
            for runs in middle_runs:
                middle = middle_word(runs)
                word = "0" * n + "1" + middle + "0" * m + "10"
                assert accepted(word)
                parsed = parse_candidate(word)
                assert parsed is not None
                assert parsed[0] == n and parsed[1] == m and parsed[2] == middle
                case = check_certificate(word)
                branches[case] += 1
                structured_candidates += 1
                max_word_length = max(max_word_length, len(word))

                erased = erase_middle(word)
                assert accepted(erased)
                erased_case = check_certificate(erased)
                assert erased_case == case
                assert not violations(word) == False
                assert not violations(erased) == False
                erasure_checks += 1

                if runs:
                    nonempty_middle += 1
                    assert middle.startswith("0")
                    # The middle is a loop from state 2 back to state 2.
                    q = 2
                    for ch in middle:
                        q = DELTA[q][ord(ch) - ord("0")]
                        assert q >= 0
                    assert q == 2

    result = {
        "status": "PASS",
        "proof_status": (
            "Written all-length candidate-changing erasure proof; finite regression "
            "is supporting evidence only; not Lean-checked or independently reviewed"
        ),
        "scope": (
            "The six-state nonflat regular-decoration-barrier instance. The reusable "
            "comparison-isolated middle rule is proposed but not complete for arbitrary inputs."
        ),
        "binary_census": {
            "max_length": 14,
            "words": binary_words,
            "accepted": accepted_words,
            "parsed_accepted": parsed_accepted_words,
            "certified_accepted": certified_accepted_words,
            "witnesses": witnesses,
        },
        "structured_erasure": {
            "n": "0..12",
            "m": "1..12",
            "middle_blocks": "0..3",
            "middle_zero_run_lengths": "1..3",
            "candidates": structured_candidates,
            "nonempty_middle": nonempty_middle,
            "erasure_checks": erasure_checks,
            "branches": branches,
            "max_word_length": max_word_length,
        },
    }

    out = Path(__file__).resolve().parents[1] / "results" / "regular-middle-erasure.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
