"""Whole-word synchronization by binary terminal suffix flags.

Input: a supplied tuple of binary DFAs. Output: a binary terminal BorderAvoid
instance with witnesses exactly (encode(u) + '00')**r for u accepted by every
input DFA. This is a construction-specific exact decider, not an unrestricted
BorderAvoid solver. See notes/2026-09-05-word-synchronization.md.
"""
from collections import deque
from dataclasses import dataclass
from math import prod
from typing import Optional, Tuple, FrozenSet

from border_lab import Instance, witness, border_witness


@dataclass(frozen=True)
class BinaryDFA:
    delta: Tuple[Tuple[int, int], ...]
    final: FrozenSet[int]
    start: int = 0

    def __post_init__(self):
        n = len(self.delta)
        if not n or type(self.start) is not int or not 0 <= self.start < n:
            raise ValueError('A DFA needs at least one state and a valid start')
        if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < n
                                   for q in row) for row in self.delta):
            raise ValueError('Invalid binary transition table; -1 means undefined')
        if any(type(q) is not int or not 0 <= q < n for q in self.final):
            raise ValueError('Invalid final state')

    def accepts(self, word: str) -> bool:
        q = self.start
        for a in word:
            if a not in '01':
                raise ValueError('Data words must be binary')
            q = self.delta[q][int(a)]
            if q < 0:
                return False
        return q in self.final


def encode_data(word: str) -> str:
    if any(a not in '01' for a in word):
        raise ValueError('Data words must be binary')
    return ''.join('1' + a for a in word)


def encode_blocks(blocks) -> str:
    return ''.join(encode_data(word) + '00' for word in blocks)


def decode_blocks(word: str) -> Optional[Tuple[str, ...]]:
    """Parse aligned two-bit tokens: 10 -> 0, 11 -> 1, 00 -> separator."""
    if len(word) % 2 or any(a not in '01' for a in word):
        return None
    result, current = [], []
    closed = False
    for i in range(0, len(word), 2):
        token = word[i:i+2]
        if token == '00':
            result.append(''.join(current))
            current = []
            closed = True
        elif token[0] == '1':
            current.append(token[1])
            closed = False
        else:
            return None
    return tuple(result) if closed else None


@dataclass(frozen=True)
class Synchronization:
    automata: Tuple[BinaryDFA, ...]
    instance: Instance
    # Boundary labels: (stage, DFA state, previous-data-bit-or-START).
    boundary_labels: Tuple[Tuple[int, int, int, str], ...]

    def predicts(self, word: str) -> bool:
        blocks = decode_blocks(word)
        return (blocks is not None and len(blocks) == len(self.automata)
                and len(set(blocks)) == 1
                and all(M.accepts(u) for M, u in zip(self.automata, blocks)))


def compile_sync(automata) -> Synchronization:
    """Compile r>=2 DFAs using 3*sum(n_i)+2*r+1 states and no Bad states.

    Flags occur only between code boundaries, from an earlier stage into the
    final stage, and forbid unequal predecessor tags. Helper states are not
    flagged. In particular the binary expansion introduces no phase flags.
    """
    ms = tuple(automata)
    if len(ms) < 2 or not all(isinstance(m, BinaryDFA) for m in ms):
        raise ValueError('Supply at least two validated BinaryDFA objects')
    delta, labels = [], []
    entries, tagged, data_helpers, separators = [], [], [], []

    def node():
        q = len(delta)
        delta.append([-1, -1])
        return q

    for i, M in enumerate(ms):
        e = node()
        entries.append(e)
        labels.append((e, i, M.start, 'START'))
        tags = {}
        for q in range(len(M.delta)):
            for a in '01':
                t = node()
                tags[q, a] = t
                labels.append((t, i, q, a))
        tagged.append(tags)
        data_helpers.append([node() for _ in M.delta])
        separators.append(node())
    f = node()

    for i, M in enumerate(ms):
        next_stage = entries[i+1] if i+1 < len(ms) else f
        delta[separators[i]][0] = next_stage
        for b, stage, q, _ in labels:
            if stage == i:
                delta[b][1] = data_helpers[i][q]
                if q in M.final:
                    delta[b][0] = separators[i]
        for q, row in enumerate(M.delta):
            for a, target in enumerate(row):
                if target >= 0:
                    delta[data_helpers[i][q]][a] = tagged[i][target, str(a)]

    last = [(b, tag) for b, i, _, tag in labels if i == len(ms)-1]
    flags = frozenset((b, target) for b, i, _, tag in labels if i < len(ms)-1
                      for target, other in last if tag != other)
    instance = Instance(tuple(tuple(row) for row in delta), frozenset({f}),
                        flags, start=entries[0])
    assert len(delta) == 3*sum(len(m.delta) for m in ms) + 2*len(ms) + 1
    return Synchronization(ms, instance, tuple(labels))


def solve_sync(automata, max_states: Optional[int] = 200000):
    """Exact common-word product search; a state cap is UNKNOWN, not NO.

    A supplied decomposition is mandatory. Passing an arbitrary Instance here
    is rejected rather than assuming it has this construction's structure.
    The product is explored on demand. Positive outputs pass both existing
    BorderAvoid predicates. The returned word is shortest within this class.
    """
    construction = compile_sync(automata)
    ms, I = construction.automata, construction.instance
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError('max_states must be a positive integer or None')
    start = tuple(m.start for m in ms)
    parent = {start: None}
    pending = deque([start])
    common = dict(product_state_bound=prod(len(m.delta) for m in ms),
                  compiled_states=len(I.delta), compiled_flags=len(I.flags))
    while pending:
        state = pending.popleft()
        if all(q in m.final for q, m in zip(state, ms)):
            rev = []
            cursor = state
            while parent[cursor] is not None:
                cursor, a = parent[cursor]
                rev.append(a)
            u = ''.join(reversed(rev))
            w = encode_blocks([u] * len(ms))
            assert all(m.accepts(u) for m in ms)
            assert construction.predicts(w) and witness(I, w) and border_witness(I, w)
            assert len(w) <= 2*len(ms)*common['product_state_bound']
            return dict(common, status='YES', common_word=u, word=w,
                        explored_states=len(parent), shortest_length=len(w))
        for a in (0, 1):
            nxt = tuple(m.delta[q][a] for m, q in zip(ms, state))
            if -1 in nxt or nxt in parent:
                continue
            if max_states is not None and len(parent) >= max_states:
                return dict(common, status='UNKNOWN', reason='Product-state cap',
                            explored_states=len(parent))
            parent[nxt] = (state, str(a))
            pending.append(nxt)
    return dict(common, status='NO', reason='Entire reachable product graph exhausted',
                explored_states=len(parent))
