"""Exact regular slices for the empty and full BorderAvoid obligations.

The remaining proper-border conditions are still required. The optional
regularity certificate proves they cannot be flagged on an accepting run;
failure to obtain that certificate says nothing about witness existence.
"""

from collections import deque
from dataclasses import dataclass
from typing import Optional

from border_lab import Instance


@dataclass(frozen=True)
class BoundarySlice:
    final: int
    relaxed: Instance
    relevant: frozenset
    active_flags: frozenset
    shortest: Optional[str]


def _reachable(instance, starts, allowed, reverse=False):
    edges = {q: set() for q in allowed}
    for q in allowed:
        for r in instance.delta[q]:
            if r in allowed:
                source, target = (r, q) if reverse else (q, r)
                edges[source].add(target)
    found = set(starts) & allowed
    pending = deque(found)
    while pending:
        for r in edges[pending.popleft()]:
            if r not in found:
                found.add(r)
                pending.append(r)
    return frozenset(found)


def _shortest_path(instance, target, allowed):
    if instance.start not in allowed or target not in allowed:
        return None
    parent = {instance.start: None}
    pending = deque([instance.start])
    while pending:
        q = pending.popleft()
        if q == target:
            letters = []
            while parent[q] is not None:
                q, letter = parent[q]
                letters.append(letter)
            return "".join(reversed(letters))
        for letter, r in zip(instance.alphabet, instance.delta[q]):
            if r in allowed and r not in parent:
                parent[r] = (q, letter)
                pending.append(r)
    return None


def final_slices(instance):
    """Compile N''(0,0) as a union of regular single-final-state languages."""
    states = set(range(len(instance.delta)))
    slices = []
    diagonal = {q for q in states if (q, q) in instance.flags}
    for final in sorted(instance.final):
        forbidden = instance.bad | diagonal | {
            q for q in states if (q, final) in instance.flags
        }
        allowed = states - forbidden
        relaxed = Instance(instance.delta, frozenset({final}), frozenset(),
                           frozenset(forbidden), instance.start, instance.alphabet)
        from_start = _reachable(instance, {instance.start}, allowed)
        to_final = _reachable(instance, {final}, allowed, reverse=True)
        relevant = from_start & to_final
        # Only an ordered pair on some accepting run can carry a flag.
        active = frozenset(
            (q, r) for q in relevant
            for r in _reachable(instance, {q}, relevant)
            if (q, r) in instance.flags
        )
        slices.append(BoundarySlice(
            final, relaxed, relevant, active,
            _shortest_path(instance, final, allowed)))
    return tuple(slices)


def boundary_accepts(slices, word):
    return any(part.relaxed.admissible(word) for part in slices)


def two_state_decision(instance, slices=None):
    """Decide witness existence for at most two states, over any finite alphabet.

    A nonempty boundary slice has a simple accepting path of length at most
    one. Such a word has no proper nonempty suffix agreement.
    """
    if len(instance.delta) > 2:
        raise ValueError("two_state_decision requires at most two states")
    if slices is None:
        slices = final_slices(instance)
    candidates = [part.shortest for part in slices if part.shortest is not None]
    if not candidates:
        return {"status": "NO"}
    return {"status": "YES", "word": min(candidates, key=lambda w: (len(w), w))}


def regularity_certificate(instance, slices=None):
    """Certify that all flag obligations are regular boundary conditions.

    If no flag can occur in forward order on an accepting boundary-safe run,
    the full witness language equals the union of these regular slices.
    The returned shortest word is then globally shortest; NO is exact.
    Otherwise the result is UNKNOWN, without an emptiness claim.
    """
    if slices is None:
        slices = final_slices(instance)
    if any(part.active_flags for part in slices):
        return {"status": "UNKNOWN", "reason": "proper flags may occur"}
    candidates = [part.shortest for part in slices if part.shortest is not None]
    if not candidates:
        return {"status": "NO", "reason": "all regular boundary slices are empty"}
    return {"status": "YES", "word": min(candidates, key=lambda w: (len(w), w)),
            "reason": "no active ordered flag in any boundary slice"}
