"""Check occurrence-context refinements of the C009 truncation rule.

This file keeps an independent witness predicate.  The implementation in
``border_lab.py`` is used only as a second oracle for the bounded regression.
All searches are finite; a passing run is evidence for the stated limits, not
an all-length theorem.
"""

import itertools
import json
import random
from pathlib import Path

from border_lab import Instance, border_witness as reference_witness


def run(instance, word):
    """Independent DFA run, returning state positions or None."""
    states = [instance.start]
    for letter in word:
        q = instance.delta[states[-1]][instance.alphabet.index(letter)]
        if q < 0:
            return None
        states.append(q)
    return tuple(states)


def direct_witness(instance, word):
    """Independent copy of Definition 8.1's forward formulation."""
    states = run(instance, word)
    if states is None:
        return False
    if states[-1] not in instance.final:
        return False
    if any(q in instance.bad for q in states):
        return False
    n = len(word)
    for i in range(n + 1):
        for j in range(i, n + 1):
            if word[i:].startswith(word[j:]) and (states[i], states[j]) in instance.flags:
                return False
    return True


def longest_repeated_suffix(word):
    """Longest suffix with an occurrence ending before the word's end."""
    for length in range(len(word) - 1, 0, -1):
        suffix = word[-length:]
        if suffix in word[:-1]:
            return length
    return 0


def source_states(instance, word, end, length, mode):
    """Return states allowed as flag sources for one transferred suffix.

    The strict position bound excludes the diagonal occurrence.  Diagonal
    flags are already absent because the original word is a witness.
    """
    states = run(instance, word)
    short = word[:end]
    start = end - length
    if mode == "all":
        return set(range(len(instance.delta)))
    if mode == "visited":
        return set(states[: end + 1])
    if mode == "prefix":
        return set(states[:start])
    if mode == "occurrence":
        suffix = short[start:end]
        return {
            states[index]
            for index in range(start)
            if short[index : index + length] == suffix
        }
    raise ValueError(mode)


def context_cut(instance, word, end, mode):
    """Check C009 or one of its source-context restrictions.

    Modes are ``all`` (C009), ``visited``, ``prefix``, and ``occurrence``.
    The latter two omit diagonal sources, which are inherited directly from
    the original witness.
    """
    if not 0 <= end < len(word) or not direct_witness(instance, word):
        return False
    states = run(instance, word)
    short = word[:end]
    repeated = longest_repeated_suffix(short)
    if repeated and short[-repeated:] != word[-repeated:]:
        return False
    if states[end] not in instance.final:
        return False
    for length in range(repeated + 1):
        new_target = states[end - length]
        old_target = states[len(word) - length]
        sources = source_states(instance, word, end, length, mode)
        if any(
            (source, new_target) in instance.flags
            and (source, old_target) not in instance.flags
            for source in sources
        ):
            return False
    return True


def generated_instances(seed, count):
    rng = random.Random(seed)
    for case in range(count):
        states = rng.randrange(2, 6)
        density = (0.0, 0.04, 0.12, 0.25)[case % 4]
        yield Instance(
            tuple(
                tuple(
                    -1 if rng.random() < 0.06 else rng.randrange(states)
                    for _ in range(2)
                )
                for _ in range(states)
            ),
            frozenset(q for q in range(states) if rng.random() < 0.4),
            frozenset(
                (q, r)
                for q in range(states)
                for r in range(states)
                if rng.random() < density
            ),
            frozenset(q for q in range(states) if rng.random() < 0.04),
        )


def all_two_state_instances():
    """Enumerate every binary two-state partial DFA instance."""
    values = range(-1, 2)
    transitions = itertools.product(values, repeat=4)
    subsets = [
        frozenset(q for q in range(2) if mask >> q & 1)
        for mask in range(4)
    ]
    flagsets = [
        frozenset(
            (q, r)
            for q in range(2)
            for r in range(2)
            if mask >> (2 * q + r) & 1
        )
        for mask in range(16)
    ]
    for flat in transitions:
        delta = (flat[:2], flat[2:])
        for final in subsets:
            for bad in subsets:
                for flags in flagsets:
                    yield Instance(delta, final, flags, bad)


def all_words(max_length):
    for length in range(max_length + 1):
        for letters in itertools.product("01", repeat=length):
            yield "".join(letters)


def describe(instance, word, end):
    states = run(instance, word)
    short = word[:end]
    repeated = longest_repeated_suffix(short)
    rows = []
    for length in range(repeated + 1):
        start = end - length
        suffix = short[start:end]
        occurrences = [
            index
            for index in range(start)
            if short[index : index + length] == suffix
        ]
        rows.append(
            {
                "length": length,
                "suffix": suffix,
                "new_target": states[start],
                "old_target": states[len(word) - length],
                "earlier_positions": occurrences,
                "earlier_states": sorted({states[index] for index in occurrences}),
                "all_state_failures": sorted(
                    source
                    for source in range(len(instance.delta))
                    if (source, states[start]) in instance.flags
                    and (source, states[len(word) - length]) not in instance.flags
                ),
            }
        )
    return {
        "delta": [list(row) for row in instance.delta],
        "final": sorted(instance.final),
        "bad": sorted(instance.bad),
        "flags": [list(pair) for pair in sorted(instance.flags)],
        "word": word,
        "end": end,
        "short_word": short,
        "state_trace": list(states),
        "lrs_short": repeated,
        "short_is_witness": direct_witness(instance, short),
        "c009_all_state": context_cut(instance, word, end, "all"),
        "visited_context": context_cut(instance, word, end, "visited"),
        "prefix_context": context_cut(instance, word, end, "prefix"),
        "exact_occurrence_context": context_cut(instance, word, end, "occurrence"),
        "suffix_rows": rows,
    }


def find_minimal_strict(mode, require_nonempty_prefix, require_repeated_suffix):
    """Find the first strict example in the complete two-state enumeration."""
    for length in range(1, 7):
        candidate_words = [
            "".join(letters)
            for letters in itertools.product("01", repeat=length)
        ]
        for instance in all_two_state_instances():
            for word in candidate_words:
                for end in range(length):
                    if require_nonempty_prefix and end == 0:
                        continue
                    if require_repeated_suffix and longest_repeated_suffix(word[:end]) == 0:
                        continue
                    if context_cut(instance, word, end, mode) and not context_cut(
                        instance, word, end, "all"
                    ):
                        return describe(instance, word, end)
    return None


def run_checks():
    modes = ("all", "visited", "prefix", "occurrence")
    counts = {
        "exhaustive_instances": 0,
        "exhaustive_words": 0,
        "exhaustive_applicable_cuts": {mode: 0 for mode in modes},
        "random_instances": 0,
        "random_words": 0,
        "random_applicable_cuts": {mode: 0 for mode in modes},
        "reference_witness_comparisons": 0,
        "implication_checks": {mode: 0 for mode in modes[1:]},
        "failures": [],
    }

    # Complete two-state regression through length six.  We compare the
    # independent witness predicate with the repository implementation and
    # verify that every proposed cut really produces a witness.
    bounded_words = list(all_words(6))
    for instance in all_two_state_instances():
        counts["exhaustive_instances"] += 1
        for word in bounded_words:
            counts["exhaustive_words"] += 1
            ours = direct_witness(instance, word)
            reference = reference_witness(instance, word)
            counts["reference_witness_comparisons"] += 1
            if ours != reference:
                counts["failures"].append(["witness_oracle", word])
                return counts
            if not ours:
                continue
            for end in range(len(word)):
                for mode in modes:
                    if context_cut(instance, word, end, mode):
                        counts["exhaustive_applicable_cuts"][mode] += 1
                        if mode != "all":
                            counts["implication_checks"][mode] += 1
                            if not direct_witness(instance, word[:end]):
                                counts["failures"].append([mode, word, end])
                                return counts

    # Independent random regression on larger state sets and longer words.
    for instance in generated_instances(20260904, 120):
        counts["random_instances"] += 1
        for word in all_words(8):
            counts["random_words"] += 1
            if not direct_witness(instance, word):
                continue
            for end in range(len(word)):
                for mode in modes:
                    if context_cut(instance, word, end, mode):
                        counts["random_applicable_cuts"][mode] += 1
                        if mode != "all":
                            counts["implication_checks"][mode] += 1
                            if not direct_witness(instance, word[:end]):
                                counts["failures"].append([mode, word, end])
                                return counts

    # These are the first examples in the complete two-state enumeration
    # with a nonempty, genuinely repeated retained suffix.
    strict_examples = {
        "visited_vs_c009": find_minimal_strict("visited", True, True),
        "occurrence_vs_c009": find_minimal_strict("occurrence", True, True),
        "empty_prefix_vs_c009": find_minimal_strict("visited", False, False),
    }
    return {"counts": counts, "strict_examples": strict_examples}


if __name__ == "__main__":
    result = run_checks()
    output = Path(__file__).resolve().parents[1] / "results" / "context-cuts.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if result.get("counts", result).get("failures"):
        raise SystemExit(1)
