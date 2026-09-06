"""Exact recurrent-target residual benchmark; not an unrestricted solver.

Five states and two flags exhibit infinitely many mutually non-subsuming
left-context languages, even though every suffix has the same complete
transition action, endpoint, visited states and agreement profile. A tiny
parametric family retains the information the finite summary loses.
"""
from dataclasses import replace
from typing import FrozenSet, Iterable, Optional, Tuple
from border_lab import Instance, witness, border_witness

Pair = Tuple[int, int]
TABLE = ((-1, 1), (2, 1), (2, 3), (4, 3), (-1, -1))
EQUALITY_FLAGS = frozenset({(0, 3), (1, 2)})
DIAGONALS = frozenset((q, q) for q in range(5))
EMPTY_SUFFIX = frozenset((q, 4) for q in range(5))
BOUNDARY = DIAGONALS | EMPTY_SUFFIX
PROPER = frozenset({(1, 3), (2, 3), (0, 2), (1, 2), (0, 3)})
REPRESENTATIVES = ('1010', '10110', '11010')


def instance(flags: Iterable[Pair] = EQUALITY_FLAGS,
             bad: Iterable[int] = ()) -> Instance:
    flags, bad = frozenset(flags), frozenset(bad)
    if any(len(pair) != 2 or any(type(q) is not int or not 0 <= q < 5
                               for q in pair) for pair in flags):
        raise ValueError('Flag endpoints must be states 0,...,4')
    if any(type(q) is not int or not 0 <= q < 5 for q in bad):
        raise ValueError('Bad states must be states 0,...,4')
    return Instance(TABLE, frozenset({4}), flags, bad, 0)


def parse_candidate(word: str) -> Optional[Tuple[int, int, int]]:
    """Candidate words are 1^m 0^z 1^n 0 with m,z,n >= 1."""
    if not word or any(a not in '01' for a in word):
        return None
    i = 0
    while i < len(word) and word[i] == '1':
        i += 1
    m = i
    while i < len(word) and word[i] == '0':
        i += 1
    z = i-m
    start = i
    while i < len(word) and word[i] == '1':
        i += 1
    n = i-start
    return (m, z, n) if min(m, z, n) > 0 and word[i:] == '0' else None


def encode(m: int, z: int, n: int) -> str:
    if any(type(x) is not int or x < 1 for x in (m, z, n)):
        raise ValueError('All three counts must be positive integers')
    return '1'*m + '0'*z + '1'*n + '0'


def symbolic_profile(m: int, z: int, n: int) -> FrozenSet[Pair]:
    """All-length profile formula. Counts may be arbitrarily large integers."""
    if any(type(x) is not int or x < 1 for x in (m, z, n)):
        raise ValueError('All three counts must be positive integers')
    comparison = (0, 2) if m == n else ((1, 2) if m > n else (0, 3))
    return BOUNDARY | {(1, 3), comparison} | ({(2, 3)} if z > 1 else set())


def direct_profile(I: Instance, word: str) -> FrozenSet[Pair]:
    """Forward definition, including diagonal and empty-suffix agreements."""
    states = I.run(word)
    if states is None:
        raise ValueError('Word has an undefined run')
    return frozenset((states[i], states[j]) for i in range(len(word)+1)
                     for j in range(i, len(word)+1)
                     if word[i:].startswith(word[j:]))


def transition_action(I: Instance, word: str) -> Tuple[int, ...]:
    """Partial transition transformation induced on EVERY state."""
    return tuple(-1 if (run := replace(I, start=q).run(word)) is None else run[-1]
                 for q in range(len(I.delta)))


def reference_summary(n: int):
    if type(n) is not int or n < 1:
        raise ValueError('Reference exponent must be a positive integer')
    I = replace(instance(), start=2)
    word = '1'*n + '0'
    run = I.run(word)
    return (2, run[-1], frozenset(run), transition_action(I, word),
            direct_profile(I, word))


def residual_membership(prefix: str, n: int) -> bool:
    """Exact symbolic language R_n = {1^n 0^z : z >= 1}."""
    if type(n) is not int or n < 1:
        raise ValueError('Reference exponent must be positive')
    return prefix.startswith('1'*n) and len(prefix) > n and set(prefix[n:]) == {'0'}


def decide_kernel(I: Instance):
    """Complete for TABLE/start 0/final 4, with ANY flags and Bad states.

    Unsupported inputs get UNKNOWN. The three-word basis is justified by the
    exact profile formula; a failure to find a short word is not otherwise NO.
    """
    if I.delta != TABLE or I.start != 0 or I.final != frozenset({4}) or I.alphabet != '01':
        return {'status': 'UNKNOWN', 'reason': 'Outside the proved five-state kernel'}
    instance(I.flags, I.bad)  # Validate the remaining annotations.
    if I.bad or I.flags & BOUNDARY:
        return {'status': 'NO', 'reason': 'Every accepted path visits all five states; boundary exclusion'}
    for word in REPRESENTATIVES:
        if witness(I, word):
            assert border_witness(I, word)
            return {'status': 'YES', 'word': word,
                    'reason': 'Complete three-profile existence basis'}
    return {'status': 'NO', 'reason': 'Every order type is forbidden in the exact profile formula'}


def symbolic_exists(flags: Iterable[Pair], bad: Iterable[int] = ()) -> bool:
    """Closed-form existence rule independently used by the regression."""
    flags, bad = set(flags), set(bad)
    return not bad and not flags.intersection(BOUNDARY) and (1, 3) not in flags \
        and not {(0, 2), (1, 2), (0, 3)} <= flags


# A binary copy-language fixture with a recurrent final-stage entry. The
# unflagged helper 11 makes 01 a neutral return at state 5; 00 terminates.
COPY_TABLE = ((4,3), (4,3), (4,3), (1,2), (5,-1), (11,8),
              (9,8), (9,8), (6,7), (10,-1), (-1,-1), (10,5))
COPY_FLAGS = frozenset({(0,6), (0,7), (1,5), (1,7), (2,5), (2,6)})


def copy_instance() -> Instance:
    return Instance(COPY_TABLE, frozenset({10}), COPY_FLAGS)


def encode_data(data: str) -> str:
    if any(a not in '01' for a in data):
        raise ValueError('Data must be binary')
    return ''.join('1'+a for a in data)


def copy_candidate(left: str, right: str, returns: int = 0) -> str:
    if type(returns) is not int or returns < 0:
        raise ValueError('Return count must be a nonnegative integer')
    return encode_data(left)+'00'+'01'*returns+encode_data(right)+'00'


def parse_copy_candidate(word: str) -> Optional[Tuple[str, int, str]]:
    """Independent token parser for E(u)00(01)^aE(v)00, u,v arbitrary."""
    if len(word) % 2 or any(a not in '01' for a in word):
        return None
    tokens = [word[i:i+2] for i in range(0, len(word), 2)]
    i, left, right = 0, [], []
    while i < len(tokens) and tokens[i][0] == '1':
        left.append(tokens[i][1]); i += 1
    if i == len(tokens) or tokens[i] != '00':
        return None
    i += 1
    returns = 0
    while i < len(tokens) and tokens[i] == '01':
        returns += 1; i += 1
    while i < len(tokens) and tokens[i][0] == '1':
        right.append(tokens[i][1]); i += 1
    if tokens[i:] != ['00']:
        return None
    return (''.join(left), returns, ''.join(right))


def copy_residual_membership(prefix: str, reference_data: str) -> bool:
    """Exact regular residual R_u = E(u)00(01)*, retaining the SAME u."""
    head = encode_data(reference_data)+'00'
    if not prefix.startswith(head):
        return False
    rest = prefix[len(head):]
    return len(rest) % 2 == 0 and rest == '01'*(len(rest)//2)
