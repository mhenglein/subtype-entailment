"""Exact boundary-origin comparisons in B**m Y without expanding large m.

B is a nonempty safe loop at p; Y safely ends at a terminal final from p.
Only sources at the displayed B boundaries are covered. Other source positions
need separate checks. The existential formula additionally requires B to be a
first-return word; this concrete comparison routine does not.
"""
from dataclasses import replace
from typing import Dict, Optional
from border_lab import Instance


def run_from(I, p, w):
    if p in I.bad:
        return None
    out = [p]
    for a in w:
        if a not in I.alphabet:
            return None
        q = I.delta[out[-1]][I.alphabet.index(a)]
        if q < 0 or q in I.bad:
            return None
        out.append(q)
    return tuple(out)


def validate(I):
    k = len(I.delta)
    if not k or I.alphabet != '01' or not 0 <= I.start < k:
        raise ValueError('A nonempty binary Instance is required')
    if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < k for q in row) for row in I.delta):
        raise ValueError('Invalid partial transition table')
    if not (I.final | I.bad) <= set(range(k)):
        raise ValueError('Invalid state annotation')
    if any(len(pair) != 2 or not set(pair) <= set(range(k)) for pair in I.flags):
        raise ValueError('Invalid flag')
    if any(any(t >= 0 for t in I.delta[f]) for f in I.final):
        raise ValueError('Accepting states must be terminal')


def power_context(I, p, B, Y):
    validate(I)
    if type(p) is not int or not 0 <= p < len(I.delta) or not B:
        raise ValueError('Valid pivot and nonempty loop required')
    b = run_from(I, p, B)
    y = run_from(I, p, Y)
    if b is None or b[-1] != p or y is None or y[-1] not in I.final:
        raise ValueError('B must be a safe loop and Y safely terminal-accepted')
    return b, y


def split_power_suffix(B, Q):
    if not B:
        raise ValueError('Nonempty base required')
    ell = 0
    while Q.endswith(B):
        Q = Q[:-len(B)]
        ell += 1
    return Q, ell


def conjugacy_cut(B, Q, j):
    """Direct string oracle: B**j Q = D B**j; return D or None."""
    if not B or type(j) is not int or j < 0:
        raise ValueError('Invalid power')
    X = B*j
    word = X+Q
    if not X:
        return Q
    return word[:-len(X)] if word.endswith(X) else None


def conjugacy_summary(B, Q, j):
    """Closed all-j formula, compared with conjugacy_cut in the regression."""
    A, ell = split_power_suffix(B, Q)
    if j <= ell:
        return B*j+A+B*(ell-j)
    if j == ell+1:
        return B*ell+(B+A)[:-len(B)] if (B+A).endswith(B) else None
    return Q if B+A == A+B else None


def captured_borders(I, p, Y):
    """All nonempty borders via the independently formulated unique capture."""
    c = run_from(I, p, Y)
    if c is None or c[-1] not in I.final:
        raise ValueError('A safe accepted tail is required')
    out = {}
    for r in range(len(I.delta)):
        if r in I.bad:
            continue
        q = r
        end = 0 if q in I.final else None
        if end is None:
            for i, a in enumerate(Y, 1):
                q = I.delta[q][int(a)]
                if q < 0 or q in I.bad:
                    break
                if q in I.final:
                    end = i
                    break
        if end and Y.endswith(Y[:end]) and c[len(Y)-end] == r:
            out[r] = (Y[:end], Y[:-end])
    return out


def boundary_targets(I, p, B, Y, m: int):
    """Map each realized target state to one (remaining copies, local cut).

    Sources range over the m+1 displayed boundaries, including Y's start.
    Runtime depends on the explicit B,Y,k, not on the magnitude of m.
    The result covers diagonals, empty suffixes, and overlap.
    """
    if type(m) is not int or m < 0:
        raise ValueError('m must be a nonnegative integer')
    _, cy = power_context(I, p, B, Y)
    b = len(B)
    out = {}
    # Accepted prefixes of the pure periodic word, one per target state.
    # If none is seen before a repeated block-boundary state, none occurs later.
    for t in range(len(I.delta)):
        if t in I.bad:
            continue
        q, seen, length = t, set(), 0
        accepted = q in I.final
        dead = False
        blocks = 0
        while not accepted and not dead and blocks < m and q not in seen:
            seen.add(q)
            for a in B:
                q = I.delta[q][int(a)]
                length += 1
                if q < 0 or q in I.bad:
                    dead = True
                    break
                if q in I.final:
                    accepted = True
                    break
            blocks += 1
        if accepted:
            j = (length+b-1)//b
            s = B*j+Y
            v = (B*((length+b-1)//b))[:length]
            cut = len(s)-length
            c = run_from(I, p, s)
            if (not length or s.endswith(v)) and c[cut] == t:
                out[t] = (j, cut, 'periodic')
    # All other captures end past the periodic prefix and leave a nonempty
    # border P of Y. Capture enumeration includes the whole tail as a border.
    for _, (P, Q) in captured_borders(I, p, Y).items():
        A, ell = split_power_suffix(B, Q)
        for j in range(min(m, ell)+1):
            t = cy[len(Q)-j*b]
            old = out.get(t)
            if old is None or j < old[0]:
                out[t] = (j, len(Q), 'border')
        if m > ell and (B+A).endswith(B):
            D = (B+A)[:-b]
            trace = run_from(I, p, D)
            if trace is None:
                raise AssertionError('Conjugacy prefix must be a defined safe path')
            t = trace[-1]
            j = ell+1
            old = out.get(t)
            if old is None or j < old[0]:
                out[t] = (j, len(Q), 'exceptional')
        # Any j>ell+1 implies commutation and has the same cut state as j=0.
    return out


def direct_boundary_targets(I, p, B, Y, m):
    power_context(I, p, B, Y)
    w = B*m+Y
    c = run_from(I, p, w)
    return {c[j] for i in range(0, m*len(B)+1, len(B))
            for j in range(i, len(w)+1) if w[i:].startswith(w[j:])}


def boundary_safe(I, p, B, Y, m):
    actual = boundary_targets(I, p, B, Y, m)
    return all((p, t) not in I.flags for t in actual)
