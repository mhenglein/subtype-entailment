"""C029 candidate via bounded safe cycles and a reverse periodic monitor.

This independent executable preserves the earlier C029 implementation.
A cap returns UNKNOWN. NO_INFINITE_EXTENSION excludes only that branch.
Ordinary proof and explicit formalization obligations are in the dated note.
"""
from collections import deque
from itertools import product

from border_lab import witness, border_witness
from safe_extensions import absorption_holds, safe_states, zero_region, shortest_paths


def phase_equal(period, left, right):
    """Equality of infinite rotations, tested over one full supplied period.

    The period need not be primitive. Testing only left == right is unsound.
    """
    d = len(period)
    return all(period[(left+t) % d] == period[(right+t) % d] for t in range(d))


def initial_monitor(I, target, period):
    d = len(period)
    buckets = [frozenset() for _ in range(d)]
    buckets[0] = frozenset({target})
    return target, 0, True, tuple(buckets)


def prepend_step(I, period, node, predecessor, letter):
    """Exact reverse edge; None rejects undefined/unsafe/conflicting cuts."""
    current, phase, matching, buckets = node
    if predecessor not in safe_states(I):
        return None
    if I.delta[predecessor][I.alphabet.index(letter)] != current:
        return None
    if not matching:
        return predecessor, 0, False, ()
    d = len(period)
    phase = (phase-1) % d
    if letter != period[phase]:
        return predecessor, 0, False, ()
    if any((predecessor, later) in I.flags
           for other_phase, group in enumerate(buckets)
           if phase_equal(period, phase, other_phase)
           for later in group):
        return None
    new = list(buckets)
    new[phase] = new[phase] | {predecessor}
    return predecessor, phase, True, tuple(new)


def monitor_word(I, prefix, period):
    """Run the reverse monitor on one supplied safe prefix, for testing."""
    if not period:
        raise ValueError("Nonempty period required")
    states = I.run(prefix)
    if states is None or any(q not in safe_states(I) for q in states):
        return False
    node = initial_monitor(I, states[-1], period)
    for j in range(len(prefix)-1, -1, -1):
        node = prepend_step(I, period, node, states[j], prefix[j])
        if node is None:
            return False
    return True


def periodic_prefix_search(I, target, period, max_states=None):
    """All-length finite graph search for a prefix, no word-length cutoff.

    Caller must ensure the endpoint is safe and its incoming column empty.
    This checks eventual infinite-suffix conflicts, not finite witnesshood.
    """
    if not period:
        raise ValueError("Nonempty period required")
    safe = safe_states(I)
    if I.start not in safe or target not in safe:
        return dict(status="NO_PREFIX", states=0)
    first = initial_monitor(I, target, period)
    parents = {first: None}
    pending = deque([first])
    while pending:
        node = pending.popleft()
        if node[0] == I.start:
            letters = []
            while parents[node] is not None:
                node, letter = parents[node]
                letters.append(letter)
            return dict(status="YES", prefix="".join(letters), states=len(parents))
        for predecessor in sorted(safe):
            for letter in I.alphabet:
                nxt = prepend_step(I, period, node, predecessor, letter)
                if nxt is None or nxt in parents:
                    continue
                if max_states is not None and len(parents) >= max_states:
                    return dict(status="UNKNOWN", states=len(parents), reason="monitor state cap")
                parents[nxt] = node, letter
                pending.append(nxt)
    return dict(status="NO_PREFIX", states=len(parents))


def safe_cycle(I, target, cycle):
    if not cycle or target not in safe_states(I):
        return False
    q = target
    for letter in cycle:
        q = I.delta[q][I.alphabet.index(letter)]
        if q not in safe_states(I):
            return False
    return q == target


def extract_witness(I, prefix, cycle):
    """A finite uniform suffix-equality horizon; no active-ray implementation.

    Every old suffix pair is jointly periodic after at most len(prefix)
    comparison positions. One more full cycle determines infinite equality.
    len(prefix)+1 cycle copies supply that entire horizon at every old target.
    """
    word = prefix + cycle * (len(prefix)+1)
    if not witness(I, word) or not border_witness(I, word):
        raise AssertionError(("finite extraction failed", I, prefix, cycle, word))
    return word


def infinite_cycle_decision(I, max_states=None):
    """Exact cycle-only C029 decision under the ordinary proof, absent a cap."""
    if not absorption_holds(I):
        return dict(status="UNKNOWN", reason="absorption hypothesis fails")
    safe = safe_states(I)
    paths = shortest_paths(I, I.start, safe)
    targets = sorted(set(paths) & safe & zero_region(I))
    total = cycles = 0
    unknown = False
    for length in range(1, len(I.delta)+1):
        for letters in product(I.alphabet, repeat=length):
            cycle = "".join(letters)
            for target in targets:
                if not safe_cycle(I, target, cycle):
                    continue
                cycles += 1
                answer = periodic_prefix_search(I, target, cycle, max_states)
                total += answer["states"]
                if answer["status"] == "UNKNOWN":
                    unknown = True
                if answer["status"] == "YES":
                    prefix = answer["prefix"]
                    word = extract_witness(I, prefix, cycle)
                    return dict(status="YES", word=word, prefix=prefix, cycle=cycle,
                                target=target, states=total, cycles=cycles,
                                method="bounded cycle and reverse periodic monitor")
    return dict(status="UNKNOWN" if unknown else "NO_INFINITE_EXTENSION",
                states=total, cycles=cycles,
                scope="does not exclude terminal witnesses")
