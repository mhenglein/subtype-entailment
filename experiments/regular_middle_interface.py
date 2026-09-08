"""Finite interface analysis for proof-directed regular-middle erasure.

This module does not decide BorderAvoid.  It checks two regular properties used
by the candidate-changing erasure rule:

* all accepted middle words induce one required boundary action in the original
  DFA; and
* all nonempty accepted middle words share a computable maximal literal prefix.

Both checks are exact finite graph computations for deterministic partial DFAs.
"""

from collections import deque


def _validate(delta, start, final):
    states = range(len(delta))
    if start not in states:
        raise ValueError("bad start state")
    final = frozenset(final)
    if not final.issubset(states):
        raise ValueError("bad final state")
    width = None
    for row in delta:
        if width is None:
            width = len(row)
        elif len(row) != width:
            raise ValueError("nonrectangular transition table")
        for q in row:
            if q < -1 or q >= len(delta):
                raise ValueError("bad transition target")
    return final, width or 0


def coreachable(delta, final):
    final, width = _validate(delta, 0, final)
    pred = [[] for _ in delta]
    for p, row in enumerate(delta):
        for a in range(width):
            q = row[a]
            if q >= 0:
                pred[q].append(p)
    seen = set(final)
    todo = list(final)
    for q in todo:
        for p in pred[q]:
            if p not in seen:
                seen.add(p)
                todo.append(p)
    return frozenset(seen)


def common_nonempty_prefix(delta, start, final, alphabet="01"):
    """Maximal common prefix of all nonempty accepted words.

    Returns None when the language has no nonempty word.  Epsilon acceptance is
    ignored: the prefix describes only the nonempty branch, matching an erasure
    proof that handles empty/nonempty middles separately.
    """
    final, width = _validate(delta, start, final)
    if len(alphabet) != width:
        raise ValueError("alphabet width mismatch")
    live = coreachable(delta, final)

    first = []
    for a, ch in enumerate(alphabet):
        q = delta[start][a]
        if q >= 0 and q in live:
            first.append((ch, q))
    if not first:
        return None
    if len(first) != 1:
        return ""

    prefix = first[0][0]
    q = first[0][1]
    while True:
        # Once the current prefix itself is accepted, longer accepted words no
        # longer force another common symbol.
        if q in final:
            return prefix
        choices = []
        for a, ch in enumerate(alphabet):
            r = delta[q][a]
            if r >= 0 and r in live:
                choices.append((ch, r))
        if len(choices) != 1:
            return prefix
        ch, q = choices[0]
        prefix += ch


def boundary_action_counterexample(
    middle_delta,
    middle_start,
    middle_final,
    original_delta,
    boundary_state,
    alphabet="01",
):
    """Return an accepted middle whose original action does not return boundary.

    Returns None exactly when every accepted middle word maps boundary_state back
    to boundary_state.  The returned word may be epsilon when epsilon itself is
    a counterexample (which can only happen if the requested boundary comparison
    is malformed; the original state is unchanged on epsilon).
    """
    middle_final, width = _validate(middle_delta, middle_start, middle_final)
    if len(alphabet) != width:
        raise ValueError("alphabet width mismatch")
    if boundary_state < 0 or boundary_state >= len(original_delta):
        raise ValueError("bad original boundary state")
    if any(len(row) != width for row in original_delta):
        raise ValueError("original alphabet width mismatch")

    first = (middle_start, boundary_state)
    parent = {first: None}
    todo = deque([first])
    while todo:
        m, q = state = todo.popleft()
        if m in middle_final and q != boundary_state:
            letters = []
            while parent[state] is not None:
                state, ch = parent[state]
                letters.append(ch)
            return "".join(reversed(letters))
        for a, ch in enumerate(alphabet):
            nm = middle_delta[m][a]
            nq = original_delta[q][a]
            if nm < 0:
                continue
            # A middle accepted by its own DFA but undefined in the original is
            # also a failed boundary-action certificate.
            if nq < 0:
                return _reconstruct(parent, state) + ch
            nxt = (nm, nq)
            if nxt not in parent:
                parent[nxt] = (state, ch)
                todo.append(nxt)
    return None


def _reconstruct(parent, state):
    letters = []
    while parent[state] is not None:
        state, ch = parent[state]
        letters.append(ch)
    return "".join(reversed(letters))


def interface_summary(
    middle_delta,
    middle_start,
    middle_final,
    original_delta,
    boundary_state,
    alphabet="01",
):
    """Return the exact finite interface facts needed by an erasure proof."""
    counterexample = boundary_action_counterexample(
        middle_delta,
        middle_start,
        middle_final,
        original_delta,
        boundary_state,
        alphabet,
    )
    return {
        "boundary_state": boundary_state,
        "all_words_return_boundary": counterexample is None,
        "boundary_counterexample": counterexample,
        "common_nonempty_prefix": common_nonempty_prefix(
            middle_delta, middle_start, middle_final, alphabet
        ),
        "epsilon_in_middle": middle_start in frozenset(middle_final),
    }
