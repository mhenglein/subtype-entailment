"""Exact arbitrary-flag decisions for a supplied finite delimited-block schema.

Each stage reads a binary data word accepted by its DFA, followed by a shared
logical delimiter outside the data alphabet. The binary compiler encodes data 0/1 as 10/11 and delimiters
as 00. Only logical boundary states carry flags or Bad annotations. This is
NOT a decomposition or decision procedure for arbitrary BorderAvoid inputs.

The decider reads all blocks backwards in synchronous padded convolution.
It records equal tails and encountered flagged tail pairs, then evaluates the
finite whole-block equality guards. Resource caps always return UNKNOWN.
"""
from collections import deque
from dataclasses import dataclass
from itertools import product
from math import prod
from typing import FrozenSet, Optional, Tuple

from border_lab import Instance, witness, border_witness
from word_sync import BinaryDFA, encode_blocks

Node = Tuple[int, int]


@dataclass(frozen=True)
class BlockSystem:
    automata: Tuple[BinaryDFA, ...]
    flags: FrozenSet[Tuple[Node, Node]] = frozenset()
    bad: FrozenSet[Node] = frozenset()

    def __post_init__(self):
        if not self.automata or not all(isinstance(m, BinaryDFA) for m in self.automata):
            raise ValueError('Supply a nonempty tuple of BinaryDFA stage descriptions')
        valid = {(i, q) for i, m in enumerate(self.automata) for q in range(len(m.delta))}
        valid.add(self.final)
        if not set(self.bad) <= valid:
            raise ValueError('Bad annotation is outside the stage states or terminal')
        if any(len(p) != 2 or p[0] not in valid or p[1] not in valid for p in self.flags):
            raise ValueError('Flag endpoint is outside the stage states or terminal')

    @property
    def final(self):
        return (len(self.automata), 0)

    def safe(self, i, q):
        x = (i, q)
        return x not in self.bad and (x, x) not in self.flags and (x, self.final) not in self.flags

    def compile(self):
        """Return the binary terminal Instance and logical-boundary ID map."""
        delta = []
        boundary, helper, separators = {}, {}, []
        def new():
            q = len(delta)
            delta.append([-1, -1])
            return q
        for i, m in enumerate(self.automata):
            for q in range(len(m.delta)):
                boundary[i, q] = new()
            for q in range(len(m.delta)):
                helper[i, q] = new()
            separators.append(new())
        final = new()
        boundary[self.final] = final
        for i, m in enumerate(self.automata):
            for q, row in enumerate(m.delta):
                b, h = boundary[i, q], helper[i, q]
                delta[b][1] = h
                if q in m.final:
                    delta[b][0] = separators[i]
                for a, target in enumerate(row):
                    if target >= 0:
                        delta[h][a] = boundary[i, target]
            delta[separators[i]][0] = (boundary[i+1, self.automata[i+1].start]
                                       if i+1 < len(self.automata) else final)
        inst = Instance(tuple(map(tuple, delta)), frozenset({final}),
                        frozenset((boundary[p], boundary[q]) for p, q in self.flags),
                        frozenset(boundary[p] for p in self.bad),
                        boundary[0, self.automata[0].start])
        assert len(delta) == 2*sum(len(m.delta) for m in self.automata)+len(self.automata)+1
        return inst, boundary


def stage_run(m, word):
    states = [m.start]
    for a in word:
        if a not in '01':
            return None
        nxt = m.delta[states[-1]][int(a)]
        if nxt < 0:
            return None
        states.append(nxt)
    return tuple(states)


def block_witness(system, blocks):
    """Independent all-cuts formula, not the convolution implementation."""
    ms = system.automata
    r = len(ms)
    if len(blocks) != r or system.final in system.bad or (system.final, system.final) in system.flags:
        return False
    runs = [stage_run(m, u) for m, u in zip(ms, blocks)]
    if any(c is None or c[-1] not in m.final for m, c in zip(ms, runs)):
        return False
    if any(not system.safe(i, q) for i, c in enumerate(runs) for q in c):
        return False
    for i in range(r):
        for j in range(i+1, r):
            guard = all(blocks[i+h] == blocks[j+h] for h in range(1, r-j))
            if not guard:
                continue
            for t in range(min(len(blocks[i]), len(blocks[j]))+1):
                left = blocks[i][len(blocks[i])-t:]
                right = blocks[j][len(blocks[j])-t:]
                if left == right and ((i, runs[i][-t-1]), (j, runs[j][-t-1])) in system.flags:
                    return False
    return True


def solve_blocks(system, max_states: Optional[int] = 200000,
                 max_transitions: Optional[int] = 2000000):
    """Exact finite search when uncapped; no claimed shortest full witness.

    BFS minimizes convolution length, not sum of block lengths. Equal-tail
    masks only shrink and hit masks only grow. Those monotonicity facts give
    a witness bound without assuming the full finite state bound is tight.
    """
    if not isinstance(system, BlockSystem):
        raise ValueError('A supplied BlockSystem decomposition is required')
    for limit in (max_states, max_transitions):
        if limit is not None and (type(limit) is not int or limit < 1):
            raise ValueError('Caps must be positive integers or None')
    ms = system.automata
    r = len(ms)
    pairs = tuple((i, j) for i in range(r) for j in range(i+1, r))
    bit = {pair: 1 << h for h, pair in enumerate(pairs)}
    all_equal = (1 << len(pairs))-1
    coord_bound = prod(len(m.delta)+1 for m in ms)
    phase_bound = (2*len(pairs)+1)*coord_bound
    common = dict(stages=r, pair_bits=len(pairs), coordinate_bound=coord_bound,
                  finite_state_bound=coord_bound * (1 << (2*len(pairs))),
                  convolution_path_bound=phase_bound, binary_witness_bound=2*r*phase_bound)
    if system.final in system.bad or (system.final, system.final) in system.flags:
        return dict(common, status='NO', reason='Unsafe terminal', states=0, transitions=0)
    allowed = [{q for q in range(len(m.delta)) if system.safe(i, q)} for i, m in enumerate(ms)]
    if any(m.start not in allowed[i] for i, m in enumerate(ms)):
        return dict(common, status='NO', reason='A mandatory stage start is unsafe', states=0, transitions=0)
    initial_options = [sorted(set(m.final) & allowed[i]) for i, m in enumerate(ms)]
    if any(not x for x in initial_options):
        return dict(common, status='NO', reason='A stage has no safe accepting endpoint', states=0, transitions=0)
    predecessors = []
    for i, m in enumerate(ms):
        pred = {q: [] for q in allowed[i]}
        for p in sorted(allowed[i]):
            for a, q in enumerate(m.delta[p]):
                if q in allowed[i]:
                    pred[q].append((str(a), p))
        predecessors.append(pred)
    # If guard_ij is true, a hit_ij is forbidden. Each guard uses whole-block
    # equalities from later stages and may be empty (always true).
    guard_masks = {}
    for i, j in pairs:
        mask = 0
        for h in range(1, r-j):
            mask |= bit[i+h, j+h]
        guard_masks[i, j] = mask

    def observe(coords, equal, hits):
        for i, j in pairs:
            if coords[i] >= 0 and coords[j] >= 0 and equal & bit[i, j]:
                if ((i, coords[i]), (j, coords[j])) in system.flags:
                    hits |= bit[i, j]
        # Empty guards cannot be falsified by any future letters.
        if any(hits & bit[p] and guard_masks[p] == 0 for p in pairs):
            return None
        return (coords, equal, hits)

    def endpoint_ok(equal, hits):
        return all(not hits & bit[p] or equal & guard_masks[p] != guard_masks[p] for p in pairs)

    parent, pending = {}, deque()
    transitions = 0
    for coordinates in product(*initial_options):
        initial = observe(tuple(coordinates), all_equal, 0)
        if initial is None:
            continue
        if initial not in parent:
            if max_states is not None and len(parent) >= max_states:
                return dict(common, status='UNKNOWN', reason='Initial-state cap',
                            states=len(parent), transitions=transitions)
            parent[initial] = None
            pending.append(initial)
    while pending:
        state = pending.popleft()
        coords, equal, hits = state
        if all(q < 0 for q in coords):
            if not endpoint_ok(equal, hits):
                continue
            columns, cur = [], state
            while parent[cur] is not None:
                cur, column = parent[cur]
                columns.append(column)
            columns.reverse()
            blocks = tuple(''.join(col[i] for col in columns if col[i] != '_')[::-1] for i in range(r))
            w = encode_blocks(blocks)
            compiled, _ = system.compile()
            assert block_witness(system, blocks) and witness(compiled, w) and border_witness(compiled, w)
            assert len(w) <= common['binary_witness_bound']
            return dict(common, status='YES', blocks=blocks, word=w,
                        states=len(parent), transitions=transitions,
                        convolution_columns=len(columns))
        options = []
        for i, q in enumerate(coords):
            if q < 0:
                options.append([('_', -1)])
            else:
                choices = list(predecessors[i][q])
                if q == ms[i].start:
                    choices.append(('_', -1))
                options.append(choices)
        for choice in product(*options):
            transitions += 1
            if max_transitions is not None and transitions > max_transitions:
                return dict(common, status='UNKNOWN', reason='Transition cap',
                            states=len(parent), transitions=transitions)
            column = tuple(a for a, _ in choice)
            nxt_coords = tuple(q for _, q in choice)
            nxt_equal = equal
            for i, j in pairs:
                if column[i] != column[j]:
                    nxt_equal &= ~bit[i, j]
            nxt = observe(nxt_coords, nxt_equal, hits)
            if nxt is None or nxt in parent:
                continue
            if max_states is not None and len(parent) >= max_states:
                return dict(common, status='UNKNOWN', reason='State cap',
                            states=len(parent), transitions=transitions)
            parent[nxt] = (state, column)
            pending.append(nxt)
    return dict(common, status='NO', reason='Entire finite convolution graph exhausted',
                states=len(parent), transitions=transitions)
