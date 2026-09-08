#!/usr/bin/env python3
"""Independent finite regression for Theorem 4's insertion geometry.

The quantified theorem is in notes/2026-09-08-presburger-selector-lifting.md.
This checker ignores automaton flags and tests the underlying literal equality
claim exhaustively on small binary words and finite sample middle languages.
"""

from itertools import combinations, product
import json
from pathlib import Path


def insert_words(base, anchors, values):
    chosen = dict(zip(anchors, values))
    out = []
    for x in range(len(base) + 1):
        if x in chosen:
            out.append(chosen[x])
        if x < len(base):
            out.append(base[x])
    return "".join(out)


def mapped_cut(x, anchors, values):
    # Convention used by the proof: a reduced cut at an insertion anchor maps
    # to the cut AFTER that state-return word.
    return x + sum(len(v) for a, v in zip(anchors, values) if a <= x)


def agrees(word, i, j):
    return 0 <= i < j < len(word) and word[i:].startswith(word[j:])


def exposure(base, i, j, anchor):
    return max(0, i + (len(base) - j) - anchor)


def compatible(language, depth, prefix):
    assert len(prefix) == depth
    return all((middle + prefix)[:depth] == prefix for middle in language)


def locally_certified(base, i, j, anchors, languages):
    # Theorem 4 only handles erased anchors at/before the target cut.
    if any(a > j for a in anchors):
        return False
    for anchor, language in zip(anchors, languages):
        if i < anchor <= j:
            d = exposure(base, i, j, anchor)
            prefix = base[anchor:anchor + d]
            if len(prefix) != d or not compatible(language, d, prefix):
                return False
    return True


def main():
    language_options = (
        ("",),
        ("0",),
        ("1",),
        ("", "0"),
        ("", "00"),
        ("0", "00"),
        ("", "1"),
    )

    base_words = 0
    base_violations = 0
    local_certificates = 0
    multi_anchor_certificates = 0
    insertion_assignments = 0

    for length in range(2, 6):
        for bits in product("01", repeat=length):
            base = "".join(bits)
            base_words += 1
            for i in range(length):
                for j in range(i + 1, length):
                    if not agrees(base, i, j):
                        continue
                    base_violations += 1
                    for count in range(1, min(2, length) + 1):
                        for anchors in combinations(range(length), count):
                            if any(a > j for a in anchors):
                                continue
                            for languages in product(language_options, repeat=count):
                                if not locally_certified(base, i, j, anchors, languages):
                                    continue
                                local_certificates += 1
                                if count > 1:
                                    multi_anchor_certificates += 1
                                for values in product(*languages):
                                    insertion_assignments += 1
                                    word = insert_words(base, anchors, values)
                                    ii = mapped_cut(i, anchors, values)
                                    jj = mapped_cut(j, anchors, values)
                                    assert agrees(word, ii, jj)

    # Sharp negative control: exposure one requires a leading zero, but the
    # inserted language forces a one.  The original equality is destroyed.
    base = "000"
    i, j = 0, 1
    anchors = (1,)
    languages = (("1",),)
    assert agrees(base, i, j)
    assert exposure(base, i, j, 1) == 1
    assert not locally_certified(base, i, j, anchors, languages)
    broken = insert_words(base, anchors, ("1",))
    assert broken == "0100"
    assert not agrees(broken, mapped_cut(i, anchors, ("1",)), mapped_cut(j, anchors, ("1",)))

    # Composition control: the rightmost insertion sits exactly at the target
    # and has zero exposure; the earlier one needs only the forced zero prefix.
    base = "0000"
    i, j = 0, 2
    anchors = (1, 2)
    languages = (("", "0", "00"), ("", "1", "11"))
    assert locally_certified(base, i, j, anchors, languages)
    composition_assignments = 0
    for values in product(*languages):
        word = insert_words(base, anchors, values)
        assert agrees(word, mapped_cut(i, anchors, values), mapped_cut(j, anchors, values))
        composition_assignments += 1

    result = {
        "status": "PASS",
        "proof_status": (
            "Finite exhaustive/sampled literal-equality regression for the written "
            "right-to-left multi-insertion theorem; not a substitute for its all-length proof"
        ),
        "exhaustive_small": {
            "base_word_max_length": 5,
            "base_words": base_words,
            "base_violations": base_violations,
            "language_options_per_anchor": len(language_options),
            "maximum_anchors": 2,
            "local_certificates": local_certificates,
            "multi_anchor_certificates": multi_anchor_certificates,
            "insertion_assignments": insertion_assignments,
        },
        "negative_control": {
            "base": "000",
            "anchor": 1,
            "exposure": 1,
            "forced_middle": "1",
            "expanded": broken,
            "agreement_destroyed": True,
        },
        "composition_control": {
            "base": "0000",
            "anchors": [1, 2],
            "assignments": composition_assignments,
        },
        "scope": (
            "Literal comparison preservation only. Flag-state preservation additionally "
            "uses the regular return-state hypothesis in the written theorem."
        ),
    }
    out = Path(__file__).resolve().parents[1] / "results" / "multi-insertion-lift.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
