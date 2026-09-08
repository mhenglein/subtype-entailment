"""Terminal witnesses with synchronized modular run lengths.

For periods p[0], ..., p[r-1], the witness language is exactly
    (1**N + '0')**r,  N a positive multiple of lcm(p).
See notes/2026-09-05-modular-synchronization.md for the all-length proof.
This module is a family generator and certificate checker, not a general solver.
Python 3.9+, standard library only.
"""
from dataclasses import dataclass
from math import lcm
from typing import FrozenSet, Iterable, Tuple

from border_lab import Instance


@dataclass(frozen=True)
class ModularFamily:
    periods: Tuple[int, ...]
    instance: Instance
    entries: Tuple[int, ...]
    cycles: Tuple[Tuple[int, ...], ...]

    @property
    def common_period(self) -> int:
        return lcm(*self.periods)

    @property
    def exact_budget(self) -> int:
        return (len(self.periods) - 1) * (self.common_period + 1)

    @property
    def shortest_length(self) -> int:
        return len(self.periods) * (self.common_period + 1)


def make_family(periods: Iterable[int]) -> ModularFamily:
    """Use one entry and one unary cycle per block, plus a terminal final.

    On alphabet '01', entry_i --1--> cycle_i[0]; the cycle advances on 1.
    Only its last phase can read 0, exiting to the next entry or final.
    Thus block i has a positive multiple of periods[i] ones.
    """
    ps = tuple(periods)
    if len(ps) < 2 or any(type(p) is not int or p <= 0 for p in ps):
        raise ValueError('At least two positive integer periods are required')
    delta = []
    entries, cycles = [], []
    for p in ps:
        entry = len(delta)
        cycle = tuple(range(entry + 1, entry + p + 1))
        entries.append(entry)
        cycles.append(cycle)
        delta.append((-1, cycle[0]))
        for j in range(p):
            on_zero = entry + p + 1 if j == p - 1 else -1
            delta.append((on_zero, cycle[(j + 1) % p]))
    delta.append((-1, -1))
    flags = set()
    for i in range(len(ps) - 1):
        flags.update((entries[i], q) for q in cycles[-1])
        flags.update((q, entries[-1]) for q in cycles[i])
    instance = Instance(tuple(delta), frozenset({len(delta) - 1}), frozenset(flags))
    return ModularFamily(ps, instance, tuple(entries), tuple(cycles))


def word_from_counts(counts: Iterable[int]) -> str:
    ns = tuple(counts)
    if not ns or any(type(n) is not int or n <= 0 for n in ns):
        raise ValueError('Positive integer block lengths are required')
    return ''.join('1' * n + '0' for n in ns)


def predicted_witness(family: ModularFamily, word: str) -> bool:
    """Independent arithmetic language specification; no automaton calls."""
    parts = word.split('0')
    if parts[-1] != '' or len(parts) != len(family.periods) + 1:
        return False
    blocks = parts[:-1]
    if any(not part or any(a != '1' for a in part) for part in blocks):
        return False
    ns = tuple(map(len, blocks))
    return len(set(ns)) == 1 and all(n % p == 0 for n, p in zip(ns, family.periods))


def agreement_profile(instance: Instance, word: str) -> FrozenSet[Tuple[int, int]]:
    """Full forward suffix-agreement profile, with diagonal/empty suffix."""
    c = instance.run(word)
    if c is None or c[-1] not in instance.final:
        raise ValueError('A defined accepted word is required')
    return frozenset((c[i], c[j]) for j in range(len(c)) for i in range(j + 1)
                     if word.startswith(word[j:], i))


def reverse_profile(instance: Instance, word: str) -> FrozenSet[Tuple[int, int]]:
    """Separate reversed-border calculation of the same full profile."""
    c = instance.run(word)
    if c is None or c[-1] not in instance.final:
        raise ValueError('A defined accepted word is required')
    rho, states = word[::-1], c[::-1]
    result = set()
    for end in range(len(rho) + 1):
        for border in range(end + 1):
            if rho[:border] == rho[end - border:end]:
                result.add((states[end], states[border]))
    return frozenset(result)


def delete_intervals(instance: Instance, word: str,
                     intervals: Iterable[Tuple[int, int]]) -> str:
    """Delete disjoint equal-state loops; validate the concrete edit certificate."""
    c = instance.run(word)
    if c is None or c[-1] not in instance.final:
        raise ValueError('A defined accepted word is required')
    parts, previous = [], 0
    for a, b in intervals:
        if not 0 <= previous <= a < b <= len(word) or c[a] != c[b]:
            raise ValueError('Intervals must be ordered disjoint state loops')
        parts.append(word[previous:a])
        previous = b
    result = ''.join(parts) + word[previous:]
    if not instance.admissible(result):
        raise AssertionError('Loop deletion did not preserve the accepted run')
    return result


def uniform_shrink_intervals(blocks: int, old: int, new: int) -> Tuple[Tuple[int, int], ...]:
    """For periods=(1,...,1), shrink every unary block in one operation."""
    if type(blocks) is not int or blocks < 2 or not 1 <= new < old:
        raise ValueError('Require at least two blocks and 1 <= new < old')
    return tuple((i * (old + 1) + 1, i * (old + 1) + 1 + old - new)
                 for i in range(blocks))
