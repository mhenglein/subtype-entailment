"""Standalone check of the three-state minimal-witness loop example.

The forward and reversed witness predicates are implemented locally.  This
script does not import the repository's BorderAvoid checker, so it can audit
the example independently.
"""

import itertools
import json
from dataclasses import dataclass


@dataclass(frozen=True)
class Instance:
    delta: tuple
    final: frozenset
    flags: frozenset
    bad: frozenset
    start: int = 0
    alphabet: str = "01"


def run(instance, word):
    states = [instance.start]
    for letter in word:
        target = instance.delta[states[-1]][instance.alphabet.index(letter)]
        if target < 0:
            return None
        states.append(target)
    return tuple(states)


def admissible(instance, word):
    states = run(instance, word)
    return (
        states is not None
        and states[-1] in instance.final
        and not any(state in instance.bad for state in states)
    )


def forward_witness(instance, word):
    states = run(instance, word)
    if not admissible(instance, word):
        return False
    length = len(word)
    return all(
        not (
            word[i:].startswith(word[j:])
            and (states[i], states[j]) in instance.flags
        )
        for i in range(length + 1)
        for j in range(i, length + 1)
    )


def reverse_witness(instance, word):
    """The border formulation, including empty and full borders."""
    states = run(instance, word)
    if not admissible(instance, word):
        return False
    reversed_word = word[::-1]
    reversed_states = states[::-1]
    for prefix_length in range(len(reversed_word) + 1):
        for border_length in range(prefix_length + 1):
            if (
                reversed_word[:border_length]
                == reversed_word[prefix_length - border_length : prefix_length]
                and (reversed_states[prefix_length], reversed_states[border_length])
                in instance.flags
            ):
                return False
    return True


def all_words(max_length):
    for length in range(max_length + 1):
        for letters in itertools.product("01", repeat=length):
            yield "".join(letters)


def main():
    instance = Instance(
        delta=((1, 0), (2, -1), (-1, 2)),
        final=frozenset({2}),
        flags=frozenset({(0, 1)}),
        bad=frozenset(),
    )
    word = "001"
    deleted = "00"
    trace = run(instance, word)
    deleted_trace = run(instance, deleted)

    assert trace == (0, 1, 2, 2)
    assert trace[2] == trace[3]
    assert forward_witness(instance, word)
    assert reverse_witness(instance, word)

    shorter_words = list(all_words(2))
    shorter_forward = {
        candidate: forward_witness(instance, candidate)
        for candidate in shorter_words
    }
    shorter_reverse = {
        candidate: reverse_witness(instance, candidate)
        for candidate in shorter_words
    }
    assert not any(shorter_forward.values())
    assert shorter_forward == shorter_reverse

    assert deleted_trace == (0, 1, 2)
    assert not forward_witness(instance, deleted)
    assert not reverse_witness(instance, deleted)

    # The deletion creates this exact flagged proper-border pair.
    assert deleted[0:].startswith(deleted[1:])
    assert (deleted_trace[0], deleted_trace[1]) in instance.flags

    result = {
        "instance": {
            "delta": [list(row) for row in instance.delta],
            "final": sorted(instance.final),
            "bad": sorted(instance.bad),
            "flags": [list(pair) for pair in sorted(instance.flags)],
        },
        "word": word,
        "word_trace": list(trace),
        "word_forward_witness": True,
        "word_reverse_witness": True,
        "shorter_words_checked": len(shorter_words),
        "shorter_words_forward_witnesses": [
            candidate for candidate, value in shorter_forward.items() if value
        ],
        "shorter_words_reverse_matches_forward": True,
        "deleted_word": deleted,
        "deleted_trace": list(deleted_trace),
        "deleted_forward_witness": False,
        "deleted_reverse_witness": False,
        "deleted_flagged_pair": [0, 1],
        "checks_passed": True,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
