#!/usr/bin/env python3
"""Independent arithmetic/fixture check for Subtail's quantitative compiler bound.

Reviewed source revision: 064fc7306b679bf607b91e7d8de259823f200c62
This is a small, manually transcribed check of the used Lean constructors and
membership conditions. It is NOT execution of Lean or of the repository's full
enumerator/compiler. No enormous enumeration or product graph is materialized.

Source files: lean/Subtail/{Basic,RankQuery,RankQueryCompiler,
RankQueryEnumeration,RankQueryCoverage}.lean at the revision above.
"""
from dataclasses import dataclass
from math import prod
import json

REVISION = '064fc7306b679bf607b91e7d8de259823f200c62'
K = 5
# Undefined transitions are None. Bits are 0 and 1.
DELTA = ((None, None), (0, None), (None, 1), (2, None), (None, 3))
INITIAL, FINALS = 4, frozenset({0})
BAD, FLAGS = frozenset(), frozenset()

@dataclass(frozen=True)
class Colour:
    state: int
    mask: tuple[bool, ...]
    next_bit: int | None
    root: bool
    is_end: bool

@dataclass(frozen=True)
class Piece:
    kind: str
    source: int
    target: int
    lc: int
    rc: int
    label: str

V, A, OBS_SIZE = 1, 5, 2
S = A * OBS_SIZE
T = max(2, 1 + V + A + S)
block = 3 * A + 2 * S
limits = {
    'groups': 2 + V + 2 * A + 2 * S,
    'core': V + A * block * 2,
    'perAtom': 2 * block,
}
limits['seamEntries'] = block * limits['groups']
limits['scalar'] = limits['core'] + limits['groups'] + 2 * block + A + S + 1

forward = Piece('forward', 0, 1, 0, 0, 'F')
wrap = Piece('wrap', 1, 0, 0, 0, 'K0')
paths = tuple((forward, wrap) * 35 for _ in range(A))
groups, core_vars = 2, 0
locations = (('fresh', 0),)
states, next_bits, first_bit = (3, 4), (1, None), 0
seams = ()
old_end = Colour(2, (False,) * K, None, False, True)

# Observer: two controls, initial=final={0}, all colours allowed,
# and every label has all four control transitions. Both controls are usable.
def allows(q: int, col: Colour) -> bool:
    return 0 <= q < OBS_SIZE

def move(q: int, source: Colour, label: str, target: Colour) -> tuple[int, ...]:
    assert allows(q, source) and label in ('F', 'S', 'K0', 'K1')
    return (0, 1)

# All clauses have empty tests, equalities and disequalities.
# The following are exactly the Bounded checks for this fixture.
assert 0 < groups <= limits['groups']
assert 0 <= core_vars <= limits['core']
assert len(locations) == V
assert all(kind == 'fresh' and 0 <= x < groups for kind, x in locations)
assert len(states) == len(next_bits) == groups
assert all(0 <= q < K for q in states)
assert len(paths) == A
for path in paths:
    assert len(path) <= limits['perAtom']
    assert all(all(0 <= x < limits['scalar'] for x in (p.source, p.target, p.lc, p.rc)) for p in path)
assert len(seams) <= limits['seamEntries']

# validDiagram and atomValid, specialized to the only two piece kinds used.
assert next_bits[-1] is None and all(b in (0, 1) for b in next_bits[:-1])
assert old_end.is_end and not old_end.root and old_end.next_bit is None
assert DELTA[states[0]][first_bit] == old_end.state
assert states[0] not in BAD and (states[0], states[0]) not in FLAGS
for path in paths:
    assert path and ('fresh', path[0].source) == locations[0]
    assert ('fresh', path[-1].target) == locations[0]
    assert path[0].lc == path[-1].rc == 0
    for left, right in zip(path, path[1:]):
        assert left.target == right.source and left.rc == right.lc
    for p in path:
        assert 0 <= p.lc < OBS_SIZE and 0 <= p.rc < OBS_SIZE
        if p.kind == 'forward':
            assert p.source <= p.target < groups
            assert p.source != p.target
            assert p.target - p.source == 1  # no internal seams
        elif p.kind == 'wrap':
            assert p.source == groups - 1 and p.target == 0 and p.label == 'K0'
        else:
            raise AssertionError('Unexpected piece kind')

# Emission count: positive forward pieces contribute once per crossed interval.
# Wrap pieces contribute a unary test, not a path atom.
active = [[] for _ in range(groups - 1)]
wrap_tests = 0
for path in paths:
    for p in path:
        if p.kind == 'forward':
            for g in range(p.source, p.target):
                active[g].append((OBS_SIZE, p.lc, p.rc))
        else:
            wrap_tests += 1
assert len(active[0]) == 175 and wrap_tests == 175
interval_sizes = [K * 3 * 2 * prod(size for size, _, _ in items) for items in active]
out_vars = 2 + groups + core_vars
out_atoms = 2 + len(interval_sizes)
out_sum_sizes = 2 + 2 + sum(interval_sizes)
out_weight = max(2, 1 + out_vars + out_atoms + out_sum_sizes)
old_bound = 64 * K * T ** (2 * T + 2)
assert T == 17
assert out_weight == 12 + 6 * K * 2 ** 175
assert out_weight > old_bound
# A simple exact proof of the strict comparison, without logarithms.
assert 17 ** 2 < 2 ** 9
assert 64 * 17 ** 36 < 2 ** 168 < 6 * 2 ** 175

# A genuine safe base/extension model, not merely a valid but unsatisfiable clause.
B, B_labels = (0, 1), (0, 1, 2)
C, C_labels = (0, 1, 0, 1), (0, 1, 2, 3, 4)

def safe_reference(word: tuple[int, ...], labels: tuple[int, ...]) -> bool:
    return (bool(word) and len(labels) == len(word) + 1 and labels[0] in FINALS
            and all(q not in BAD for q in labels)
            and all(DELTA[labels[i + 1]][bit] == labels[i] for i, bit in enumerate(word))
            and not FLAGS)

def failure(word: tuple[int, ...], i: int) -> int:
    if i == 0:
        return 0
    return max(j for j in range(i) if j == 0 or word[:j] == word[i-j:i])

def advance(word: tuple[int, ...], i: int, bit: int) -> int:
    extended = word[:i] + (bit,)
    return max(j for j in range(len(word) + 1) if j == 0 or word[:j] == extended[-j:])

def colour(word: tuple[int, ...], labels: tuple[int, ...], i: int) -> Colour:
    return Colour(labels[i], (False,) * K, word[i] if i < len(word) else None,
                  i == 0, i == len(word))

assert all(DELTA[f] == (None, None) for f in FINALS)
assert safe_reference(B, B_labels) and safe_reference(C, C_labels)
assert C[:len(B)] == B and C_labels[:len(B_labels)] == B_labels
assert [j for j in range(len(B) + 1, len(C) + 1) if C[j-len(B):j] == B] == [len(C)]
assert colour(B, B_labels, 2) == old_end
# Base assignment END=2, INITIAL=0, z_0=1, z_1=2.
assert failure(B, 2) == 0 and advance(B, 0, first_bit) == 1
assert not colour(B, B_labels, 1).is_end
assert advance(B, 1, 1) == 2
# One positive shared generator step, (3,1,0,0^175) -> (4,END,1,0^175).
assert DELTA[4][1] == 3
fresh_left, fresh_right = colour(C, C_labels, 3), colour(C, C_labels, 4)
assert fresh_left == Colour(3, (False,) * K, 1, False, False)
assert fresh_right == Colour(4, (False,) * K, None, False, True)
assert all(allows(lc, fresh_left) and allows(rc, fresh_right)
           and rc in move(lc, fresh_left, 'S', fresh_right)
           for _, lc, rc in active[0])
# Each of the 175 wrap predicates holds on the same two fresh colours.
assert advance(C, 4, first_bit) == 3
assert 0 in move(0, fresh_right, 'K0', fresh_left)
# The actual original word is reverse(C)=1010 and is an original witness.
q = INITIAL
for bit in reversed(C):
    q = DELTA[q][bit]
    assert q is not None and q not in BAD
assert q in FINALS

print(json.dumps({
    'revision': REVISION,
    'verification': 'independent source-transcribed fixture; no Lean build or full enumeration',
    'input_weight': T,
    'limits': limits,
    'pieces_per_atom': len(paths[0]),
    'active_coordinates': len(active[0]),
    'output_variables': out_vars,
    'output_atoms': out_atoms,
    'interval_size': interval_sizes[0],
    'output_weight': out_weight,
    'proposed_U': old_bound,
    'output_greater_than_proposed_U': out_weight > old_bound,
    'safe_base': '01',
    'safe_first_return_extension': '0101',
    'all_assertions_passed': True,
}, indent=2))
