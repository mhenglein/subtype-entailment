"""Exact copy-language constructions for terminal BorderAvoid (C046-C049).

All constructions are polynomial in their explicitly supplied transition tables.
No procedure here decides unrestricted BorderAvoid. See the accompanying note.
"""
from dataclasses import dataclass
from math import gcd
from typing import Iterable, Tuple
from border_lab import Instance


@dataclass(frozen=True)
class DFA:
    """An ordinary partial binary DFA; accepting states need not be terminal."""
    delta: Tuple[Tuple[int, int], ...]
    final: frozenset
    start: int = 0

    def __post_init__(self):
        k = len(self.delta)
        if not k or not isinstance(self.start, int) or not 0 <= self.start < k:
            raise ValueError('DFA must have a valid start and a nonempty state set')
        if any(len(row) != 2 or any(not isinstance(q, int) or q < -1 or q >= k
                                   for q in row) for row in self.delta):
            raise ValueError('Invalid binary DFA transition table')
        if any(not isinstance(q, int) or not 0 <= q < k for q in self.final):
            raise ValueError('Invalid final state')

    def accepts(self, word: str) -> bool:
        q = self.start
        for a in word:
            if a not in '01':
                raise ValueError('Input is not binary')
            q = self.delta[q][int(a)]
            if q < 0:
                return False
        return q in self.final


def lcm(values: Iterable[int]) -> int:
    out = 1
    for n in values:
        out = out // gcd(out, n) * n
    return out


def lcm_instance(periods: Iterable[int]) -> Instance:
    """Witnesses are exactly (1**a + '0')**r for positive common multiples a.

    k = 1 + r + sum(periods). The construction is already binary and flat.
    """
    periods = tuple(periods)
    if len(periods) < 2 or any(not isinstance(p, int) or isinstance(p, bool)
                               or p < 1 for p in periods):
        raise ValueError('At least two positive integer periods are required')
    delta, entries, interiors = [], [], []
    for p in periods:
        e = len(delta)
        entries.append(e)
        interiors.append(tuple(range(e + 1, e + p + 1)))
        delta.append([-1, e + 1])
        for j in range(p):
            delta.append([-1, e + 1 + (j + 1) % p])
    f = len(delta)
    delta.append([-1, -1])
    for i, states in enumerate(interiors):
        delta[states[-1]][0] = entries[i + 1] if i + 1 < len(periods) else f
    flags = set()
    for e, states in zip(entries[:-1], interiors[:-1]):
        flags.update((e, q) for q in interiors[-1])
        flags.update((p, entries[-1]) for p in states)
    return Instance(tuple(map(tuple, delta)), frozenset({f}), frozenset(flags))


def copy_instance(automata: Iterable[DFA]) -> Instance:
    """Ternary witnesses: (u+'#')**r with u in every supplied DFA language.

    A boundary state records the preceding data letter, or a fresh block-entry
    marker. Flags compare unequal markers between each earlier block and the
    last block. The longest common suffix proves equality of the whole blocks.
    """
    automata = tuple(automata)
    if len(automata) < 2 or any(not isinstance(m, DFA) for m in automata):
        raise ValueError('At least two DFA objects are required')
    delta, entries, copies, markers = [], [], [], []
    for m in automata:
        entry = len(delta)
        entries.append(entry)
        delta.append([-1, -1, -1])
        copy = {}
        marks = {entry: -1}
        for q in range(len(m.delta)):
            for a in range(2):
                state = len(delta)
                copy[q, a] = state
                marks[state] = a
                delta.append([-1, -1, -1])
        copies.append(copy)
        markers.append(marks)
    f = len(delta)
    delta.append([-1, -1, -1])
    for i, m in enumerate(automata):
        nxt = entries[i + 1] if i + 1 < len(automata) else f
        positions = [(entries[i], m.start)]
        positions += [(state, q) for (q, _), state in copies[i].items()]
        for state, q in positions:
            for a in range(2):
                t = m.delta[q][a]
                if t >= 0:
                    delta[state][a] = copies[i][t, a]
            if q in m.final:
                delta[state][2] = nxt
    flags = frozenset((p, q) for marks in markers[:-1]
                      for p, a in marks.items() for q, b in markers[-1].items()
                      if a != b)
    return Instance(tuple(map(tuple, delta)), frozenset({f}), flags,
                    alphabet='01#')


CODE = {'0': '00', '1': '01', '#': '10'}


def encode_word(word: str) -> str:
    try:
        return ''.join(CODE[a] for a in word)
    except KeyError as exc:
        raise ValueError('Word is not over 01#') from exc


def binary_encode(instance: Instance) -> Instance:
    """Fixed-length encoding; original flags apply only at code boundaries.

    Preserves witness existence and exact encoded witness language, not the
    numerical word budget. Uses at most three times the original state count.
    """
    if instance.alphabet != '01#' or any(len(row) != 3 for row in instance.delta):
        raise ValueError('Expected a ternary 01# instance')
    k = len(instance.delta)
    if not k or any(any(not isinstance(t, int) or t < -1 or t >= k for t in row)
                    for row in instance.delta):
        raise ValueError('Invalid transition table')
    valid = lambda q: isinstance(q, int) and 0 <= q < k
    if not valid(instance.start) or any(not valid(q) for q in instance.final | instance.bad):
        raise ValueError('Invalid state annotation')
    if any(len(pair) != 2 or any(not valid(q) for q in pair) for pair in instance.flags):
        raise ValueError('Invalid flag relation')
    delta = [[-1, -1] for _ in range(k)]
    for q, row in enumerate(instance.delta):
        for first in range(2):
            children = (row[0], row[1]) if first == 0 else (row[2], -1)
            if any(t >= 0 for t in children):
                mid = len(delta)
                delta[q][first] = mid
                delta.append(list(children))
    return Instance(tuple(map(tuple, delta)), instance.final, instance.flags,
                    instance.bad, instance.start)


def agreement_profile(instance: Instance, word: str) -> frozenset:
    """Full profile, including diagonals and empty suffixes."""
    states = instance.run(word)
    if states is None:
        raise ValueError('Word has no defined run')
    return frozenset((states[i], states[j])
                     for j in range(len(word) + 1) for i in range(j + 1)
                     if word.startswith(word[j:], i))


def intersection_witness(automata: Iterable[DFA], max_states: int = 200000) -> dict:
    """Exact product search for the *supplied intersection*, not general input.

    YES includes a common word; NO requires graph exhaustion. A cap is UNKNOWN.
    Via copy_instance/binary_encode this decides the constructed copy subclass.
    """
    from collections import deque
    automata = tuple(automata)
    if len(automata) < 2 or any(not isinstance(m, DFA) for m in automata):
        raise ValueError('At least two DFA objects are required')
    if not isinstance(max_states, int) or max_states < 1:
        raise ValueError('max_states must be positive')
    start = tuple(m.start for m in automata)
    parents = {start: None}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        if all(q in m.final for m, q in zip(automata, state)):
            letters = []
            node = state
            while parents[node] is not None:
                node, a = parents[node]
                letters.append(a)
            return {'status': 'YES', 'word': ''.join(reversed(letters)),
                    'states': len(parents)}
        for a in range(2):
            target = tuple(m.delta[q][a] for m, q in zip(automata, state))
            if -1 in target or target in parents:
                continue
            if len(parents) >= max_states:
                return {'status': 'UNKNOWN', 'reason': 'state cap',
                        'states': len(parents)}
            parents[target] = (state, str(a))
            queue.append(target)
    return {'status': 'NO', 'states': len(parents)}
