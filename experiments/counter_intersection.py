"""Polynomial-size DFA lists whose intersection is one binary counting word.

Bits inside each fixed-width number are least-significant first. The common
word lists 0,1,...,2**width-1 in that order, without separators. This supplies
an explicit nonflat family for whole-word synchronization, not a general
intersection algorithm. See the C050 written proof.
"""
from word_sync import BinaryDFA


def _reachable_dfa(initial, transition, is_final):
    states = [initial]
    ids = {initial: 0}
    delta = []
    for state in states:
        row = []
        for a in (0, 1):
            nxt = transition(state, a)
            if nxt is None:
                row.append(-1)
                continue
            if nxt not in ids:
                ids[nxt] = len(states)
                states.append(nxt)
            row.append(ids[nxt])
        delta.append(tuple(row))
    return BinaryDFA(tuple(delta), frozenset(i for i, q in enumerate(states)
                                           if is_final(q)))


def counting_dfas(width: int):
    """Return width+1 DFAs of at most 6*width**2+3*width total states."""
    if type(width) is not int or width < 1:
        raise ValueError('Width must be a positive integer')

    def format_step(state, a):
        kind, phase, all_ones = state
        if kind == 'done':
            return None
        if kind == 'first':
            if a != 0:
                return None
            return ('scan', 0, True) if phase+1 == width else ('first', phase+1, False)
        now_all = all_ones and a == 1
        if phase+1 == width:
            return ('done', 0, False) if now_all else ('scan', 0, True)
        return ('scan', phase+1, now_all)

    out = [_reachable_dfa(('first', 0, False), format_step,
                           lambda s: s[0] == 'done')]
    for bit in range(width):
        def bit_step(state, a, bit=bit):
            phase, expected, carry = state
            if phase < bit:
                carry = carry and a == 1
            elif phase == bit:
                if expected != -1 and a != expected:
                    return None
                expected = a ^ int(carry)
            if phase+1 == width:
                return (0, expected, True)
            return (phase+1, expected, carry)
        checker = _reachable_dfa((0, -1, True), bit_step,
                                 lambda s: s[0] == 0 and s[1] != -1)
        assert len(checker.delta) <= 6*width
        out.append(checker)
    assert len(out[0].delta) <= 3*width
    assert sum(len(m.delta) for m in out) <= 6*width*width+3*width
    return tuple(out)


def counting_word(width: int) -> str:
    if type(width) is not int or width < 1:
        raise ValueError('Width must be a positive integer')
    return ''.join(format(i, '0%db' % width)[::-1] for i in range(1 << width))
