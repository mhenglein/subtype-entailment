"""Unbounded shared-block copying, exact length formulas and regular filtering.

This is a supplied-family solver, NOT a general BorderAvoid decider.  See
notes/2026-09-10-copy-cycles-and-length-series.md for all-length proofs.
No external dependencies. All positive expanded outputs pass both predicates.
"""
from collections import deque
from dataclasses import replace
from math import isqrt
from typing import Optional
from border_lab import Instance, witness, border_witness


UNARY_FLAGS = frozenset({(0, 4), (2, 4), (1, 3)})


def unary_instance(flags=UNARY_FLAGS):
    """Eleven-state positive-unary-block instance. Only these flags supported."""
    flags = frozenset(flags)
    if not flags <= UNARY_FLAGS:
        raise ValueError('Flags must be a subset of the three construction flags')
    return Instance(((-1, 6), (7, 6), (8, 6), (-1, 9), (10, 9),
                     (-1, -1), (-1, 1), (2, -1), (-1, 3), (-1, 4), (5, -1)),
                    frozenset({5}), flags)


def copy_instance():
    """Thirteen states; data 10/11, block end 00, stage switch 01."""
    table = ((-1, 8), (9, 8), (9, 8), (10, 8), (-1, 11),
             (12, 11), (12, 11), (-1, -1), (1, 2), (3, -1),
             (-1, 4), (5, 6), (7, -1))
    sources = {0: 'S', 1: '0', 2: '1', 3: 'S'}
    targets = {4: 'S', 5: '0', 6: '1'}
    flags = frozenset((p, q) for p, a in sources.items()
                      for q, b in targets.items() if a != b)
    return Instance(table, frozenset({7}), flags)


def encode_data(word):
    if not isinstance(word, str) or not word or any(a not in '01' for a in word):
        raise ValueError('A nonempty binary data word is required')
    return ''.join('1' + a for a in word)


def block(word):
    return encode_data(word) + '00'


def candidate(earlier, final):
    earlier = tuple(earlier)
    if not earlier:
        raise ValueError('At least one earlier block is required')
    return ''.join(block(u) for u in earlier) + '01' + block(final)


def parse_candidate(word, unary=False):
    """Independent fixed-token parser; None means outside candidate grammar."""
    if not isinstance(word, str) or len(word) % 2 or any(a not in '01' for a in word):
        return None
    prior, current, final, switched = [], [], None, False
    for offset in range(0, len(word), 2):
        token = word[offset:offset+2]
        if final is not None:
            return None
        if token in ('10', '11'):
            if unary and token != '11':
                return None
            current.append(token[1])
        elif token == '00':
            if not current:
                return None
            if switched:
                final = ''.join(current)
            else:
                prior.append(''.join(current))
            current = []
        else:  # 01 is the unique switch, at a boundary after an earlier block.
            if switched or current or not prior:
                return None
            switched = True
    if not switched or final is None or current:
        return None
    return tuple(prior), final


def predicts_unary(word, flags=UNARY_FLAGS):
    parsed = parse_candidate(word, unary=True)
    if parsed is None:
        return False
    earlier, final = parsed
    n = len(final)
    return ((0, 4) not in flags or len(earlier[0]) >= n) and \
        ((2, 4) not in flags or all(len(u) >= n for u in earlier[1:])) and \
        ((1, 3) not in flags or all(len(u) <= n for u in earlier))


def divisor_count(n):
    if type(n) is not int or n < 1:
        raise ValueError('n must be a positive integer')
    return sum(2 if d*d != n else 1 for d in range(1, isqrt(n)+1) if n % d == 0)


def equal_coefficient(length):
    """Exact number of unary equal-copy witnesses of the given bit length."""
    if type(length) is not int or length < 0:
        raise ValueError('length must be a nonnegative integer')
    if length < 10 or length % 2:
        return 0
    n = (length - 2)//2
    return divisor_count(n) - 2


def two_flag_coefficient(length):
    """Remove (0,4): first block may be shorter; later blocks equal the final."""
    if type(length) is not int or length < 0:
        raise ValueError('length must be a nonnegative integer')
    if length < 10 or length % 2:
        return 0
    k = (length - 2)//2 - 1
    return k - divisor_count(k)


def _regular(I):
    if not isinstance(I, Instance) or I.alphabet != '01' or I.flags:
        raise ValueError('Regular domains must be unflagged binary Instances')
    k = len(I.delta)
    if not k or not 0 <= I.start < k:
        raise ValueError('Invalid start/state set')
    if any(len(row) != 2 or any(type(q) is not int or q < -1 or q >= k for q in row)
           for row in I.delta):
        raise ValueError('Malformed transition table')
    if any(type(q) is not int or q < 0 or q >= k for q in I.final | I.bad):
        raise ValueError('Malformed annotations')


def accelerate_copy_cycle(domain: Instance, data_domain: Optional[Instance] = None,
                          max_states=100000, max_work=2000000,
                          max_output_length=50000):
    """Decide D intersect {B^m 01 B : B=E(u)00, u in L nonempty, m>=1}.

    Complete when uncapped. The returned witness is not claimed shortest.
    Action replacement preserves this family and regular restrictions, not
    arbitrary internal profiles or left contexts. L defaults to binary words.
    """
    _regular(domain)
    if data_domain is None:
        data_domain = Instance(((0, 0),), frozenset({0}))
    _regular(data_domain)
    for value in (max_states, max_work, max_output_length):
        if value is not None and (type(value) is not int or value < 1):
            raise ValueError('Caps must be positive integers or None')
    d, ell = len(domain.delta), len(data_domain.delta)
    meta = dict(domain_states=d, data_states=ell,
                action_bound=(d+1)**d,
                search_state_bound=2*ell*(d+1)**d,
                witness_length_bound=(d+1)*(4*ell*(d+1)**d+2)+2)
    if domain.start in domain.bad or data_domain.start in data_domain.bad:
        return dict(meta, status='NO', states=0, work=0, reason='Unsafe domain start')
    sink = d
    table = tuple(tuple(t if p not in domain.bad and t >= 0 and t not in domain.bad
                        else sink for t in row) for p, row in enumerate(domain.delta)) + ((sink, sink),)
    finals = domain.final - domain.bad
    def act(word):
        out = []
        for p in range(d+1):
            for a in word:
                p = table[p][int(a)]
            out.append(p)
        return tuple(out)
    tokens = (act('10'), act('11'))
    delimiter, switch = act('00'), act('01')
    initial = (data_domain.start, tuple(range(d+1)), False)
    parent, pending = {initial: None}, deque([initial])
    tested, work = set(), 0
    while pending:
        node = pending.popleft()
        state, action, nonempty = node
        if nonempty and state in data_domain.final:
            A = tuple(delimiter[q] for q in action)
            if A not in tested:
                tested.add(A)
                q, copies, seen = A[domain.start], 1, set()
                while q not in seen:
                    seen.add(q)
                    work += 1
                    if max_work is not None and work > max_work:
                        return dict(meta, status='UNKNOWN', reason='Work cap', states=len(parent), work=work)
                    if A[switch[q]] in finals:
                        letters, cursor = [], node
                        while parent[cursor] is not None:
                            cursor, a = parent[cursor]
                            letters.append(a)
                        u = ''.join(reversed(letters))
                        length = (copies+1)*(2*len(u)+2)+2
                        if max_output_length is not None and length > max_output_length:
                            return dict(meta, status='UNKNOWN', reason='Output expansion cap',
                                        data_word=u, earlier_copies=copies, length=length,
                                        states=len(parent), work=work)
                        w = block(u)*copies + '01' + block(u)
                        assert copies <= d and len(w) <= meta['witness_length_bound']
                        assert data_domain.admissible(u) and domain.admissible(w)
                        I = copy_instance()
                        assert witness(I, w) and border_witness(I, w)
                        return dict(meta, status='YES', word=w, data_word=u, earlier_copies=copies,
                                    states=len(parent), work=work)
                    q = A[q]
                    copies += 1
        for a, token in enumerate(tokens):
            work += 1
            if max_work is not None and work > max_work:
                return dict(meta, status='UNKNOWN', reason='Work cap', states=len(parent), work=work)
            target = data_domain.delta[state][a]
            if target < 0 or target in data_domain.bad:
                continue
            nxt = (target, tuple(token[q] for q in action), True)
            if nxt not in parent:
                if max_states is not None and len(parent) >= max_states:
                    return dict(meta, status='UNKNOWN', reason='State cap', states=len(parent), work=work)
                parent[nxt] = (node, str(a))
                pending.append(nxt)
    return dict(meta, status='NO', reason='Complete action-product and power-orbit exhaustion',
                states=len(parent), work=work)
