"""Finite interface analysis for proof-directed regular-middle erasure.

This module does not decide BorderAvoid. It checks regular properties used by
candidate-changing erasure rules and can discover return languages of productive
SCCs directly from the original deterministic partial DFA.
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

    Returns None when the language has no nonempty word. Epsilon acceptance is
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
    to boundary_state. Undefined original transitions are represented by a dead
    product component so any returned counterexample is a complete accepted word.
    """
    middle_final, width = _validate(middle_delta, middle_start, middle_final)
    if len(alphabet) != width:
        raise ValueError("alphabet width mismatch")
    if boundary_state < 0 or boundary_state >= len(original_delta):
        raise ValueError("bad original boundary state")
    for row in original_delta:
        if len(row) != width:
            raise ValueError("original alphabet width mismatch")
        for q in row:
            if q < -1 or q >= len(original_delta):
                raise ValueError("bad original transition target")

    first = (middle_start, boundary_state)
    parent = {first: None}
    todo = deque([first])
    while todo:
        m, q = state = todo.popleft()
        if m in middle_final and q != boundary_state:
            return _reconstruct(parent, state)
        for a, ch in enumerate(alphabet):
            nm = middle_delta[m][a]
            if nm < 0:
                continue
            nq = -1 if q < 0 else original_delta[q][a]
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
    """Return exact finite interface facts needed by an erasure proof."""
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


def strongly_connected_components(delta):
    """Return SCCs of the defined transition graph as sorted tuples."""
    _validate(delta, 0, set())
    n = len(delta)
    graph = [sorted({q for q in row if q >= 0}) for row in delta]
    rev = [[] for _ in delta]
    for p, qs in enumerate(graph):
        for q in qs:
            rev[q].append(p)

    seen = set()
    order = []
    for root in range(n):
        if root in seen:
            continue
        stack = [(root, 0)]
        seen.add(root)
        while stack:
            q, i = stack[-1]
            if i < len(graph[q]):
                r = graph[q][i]
                stack[-1] = (q, i + 1)
                if r not in seen:
                    seen.add(r)
                    stack.append((r, 0))
            else:
                order.append(q)
                stack.pop()

    seen.clear()
    out = []
    for root in reversed(order):
        if root in seen:
            continue
        comp = []
        todo = [root]
        seen.add(root)
        for q in todo:
            comp.append(q)
            for r in rev[q]:
                if r not in seen:
                    seen.add(r)
                    todo.append(r)
        out.append(tuple(sorted(comp)))
    return tuple(sorted(out))


def restricted_return_dfa(original_delta, component, boundary_state):
    """DFA for words that stay inside component and return boundary_state.

    The returned tuple is (delta,start,final,index_to_original). Epsilon is
    accepted. The language can be nonflat even though this representation is
    finite, because it is exactly the SCC's return language at the boundary.
    """
    _validate(original_delta, 0, set())
    component = tuple(sorted(set(component)))
    if boundary_state not in component:
        raise ValueError("boundary is not in component")
    index = {q: i for i, q in enumerate(component)}
    rows = []
    for q in component:
        row = []
        for r in original_delta[q]:
            row.append(index[r] if r in index else -1)
        rows.append(tuple(row))
    start = index[boundary_state]
    return tuple(rows), start, frozenset({start}), component


def scc_return_interfaces(original_delta, alphabet="01"):
    """Discover cyclic SCC return languages and their forced prefixes.

    Each row is a finite candidate interface. This does not prove that erasing
    the SCC is semantically sound; a separate comparison selector must show that
    its chosen forbidden comparison does not depend on the erased interior.
    """
    _validate(original_delta, 0, set())
    rows = []
    for component in strongly_connected_components(original_delta):
        cyclic = len(component) > 1 or any(
            original_delta[q][a] == q
            for q in component
            for a in range(len(original_delta[q]))
        )
        if not cyclic:
            continue
        for boundary in component:
            md, start, final, mapping = restricted_return_dfa(
                original_delta, component, boundary
            )
            prefix = common_nonempty_prefix(md, start, final, alphabet)
            if prefix is None:
                continue
            rows.append({
                "component": mapping,
                "boundary_state": boundary,
                "common_nonempty_prefix": prefix,
                "epsilon_in_middle": True,
            })
    return tuple(rows)
