#!/usr/bin/env python3
"""Independent finite-graph falsification for issue #71.

Graph comparisons are exact for the unfoldings, including cyclic graphs.
The finite corpus is NOT a completeness bound on valuations or inputs.
Missing witnesses in a bounded corpus are reported as UNKNOWN.
No existing Subtail implementation is imported.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import platform
import random
import sys

BASE = "19b06d4fed9da635d9b911f0e908d04e4fc4b099"
SEED = 2026092071
# Node: (label, left, right); B and T ignore the final fields.
Node = tuple[str, int, int]
Graph = tuple[Node, ...]
Clause = tuple  # ('le', x, y), ('bot', x), ('top', x), ('prod', x, l, r)
B: Node = ("B", 0, 0)
T: Node = ("T", 0, 0)


def separation(g: Graph, a: int, h: Graph, b: int) -> tuple[int, ...] | None:
    """Shortest finite failure of literal coinductive labelled-tree order."""
    queue = deque([(a, b, ())])
    seen: set[tuple[int, int]] = set()
    while queue:
        x, y, word = queue.popleft()
        if (x, y) in seen:
            continue
        seen.add((x, y))
        lx, ly = g[x][0], h[y][0]
        if lx == "B" or ly == "T":
            continue
        if lx != "P" or ly != "P":
            return word
        queue.append((g[x][1], h[y][1], word + (0,)))
        queue.append((g[x][2], h[y][2], word + (1,)))
    return None


def below(g: Graph, a: int, h: Graph, b: int) -> bool:
    return separation(g, a, h, b) is None


def equal(g: Graph, a: int, h: Graph, b: int) -> bool:
    return below(g, a, h, b) and below(h, b, g, a)


def projection(g: Graph, negative: bool = False) -> Graph:
    """P(t), or P(dual(t))=Q(t), as a top-free finite graph."""
    omega = len(g)
    out: list[Node] = []
    for label, l, r in g:
        if label == "P":
            out.append(("P", l, r))
        elif (label == "T") != negative:
            out.append(("P", omega, omega))
        else:
            out.append(B)
    out.append(("P", omega, omega))
    return tuple(out)


def dual_graph(g: Graph) -> Graph:
    return tuple(("T" if label == "B" else "B" if label == "T" else "P", l, r)
                 for label, l, r in g)


def dual_clause(c: Clause) -> Clause:
    if c[0] == "le":
        return ("le", c[2], c[1])
    if c[0] == "bot":
        return ("top", c[1])
    if c[0] == "top":
        return ("bot", c[1])
    return c


def holds(g: Graph, roots: tuple[int, ...], c: Clause, projected: bool = False) -> bool:
    kind, x, *args = c
    a = roots[x]
    if kind == "le":
        return below(g, a, g, roots[args[0]])
    if kind == "bot":
        return equal(g, a, (B,), 0)
    if kind == "top":
        value: Graph = (("P", 0, 0),) if projected else (T,)
        return equal(g, a, value, 0)
    if kind == "prod":
        p = len(g)
        value = g + (("P", roots[args[0]], roots[args[1]]),)
        return equal(value, a, value, p)
    raise ValueError(f"Unknown clause: {c!r}")


def models(g: Graph, roots: tuple[int, ...], cs: tuple[Clause, ...], projected: bool = False) -> bool:
    return all(holds(g, roots, c, projected) for c in cs)


def total_label(g: Graph, root: int, word: tuple[int, ...]) -> str:
    q = root
    for a in word:
        if g[q][0] != "P":
            return g[q][0]
        q = g[q][1 + a]
    return g[q][0]


@dataclass
class TopNFA:
    """Exact least top-language construction, independently checked below.

    There is one state per variable and one accepting universal-suffix state.
    Epsilon and product edges implement inclusion/push; pop rules are saturated.
    """
    n: int
    eps: list[set[int]]
    edges: list[list[set[int]]]
    rounds: int

    def closure(self, states: set[int] | frozenset[int]) -> frozenset[int]:
        return frozenset(q for s in states for q in self.eps[s])

    def step(self, states: frozenset[int], a: int) -> frozenset[int]:
        return self.closure({q for s in states for q in self.edges[a][s]})

    def accepts(self, root: int, word: tuple[int, ...]) -> bool:
        states = self.closure({root})
        for a in word:
            states = self.step(states, a)
        return self.n in states


def top_nfa(n: int, cs: tuple[Clause, ...]) -> TopNFA:
    eps = [{i} for i in range(n + 1)]
    edges = [[set() for _ in range(n + 1)] for _ in range(2)]
    prods: list[tuple[int, int, int]] = []
    for c in cs:
        if c[0] == "top":
            eps[c[1]].add(n)
        elif c[0] == "le":
            eps[c[2]].add(c[1])
        elif c[0] == "prod":
            x, l, r = c[1:]
            edges[0][x].add(l)
            edges[1][x].add(r)
            prods.append((x, l, r))
    edges[0][n].add(n)
    edges[1][n].add(n)
    rounds = 0
    while True:
        rounds += 1
        old = tuple(frozenset(row) for row in eps)
        for k in range(n + 1):
            for p in range(n + 1):
                if k in eps[p]:
                    eps[p].update(eps[k])
        for x, l, r in prods:
            for a, target in ((0, l), (1, r)):
                reached = {q for p in eps[x] for v in edges[a][p] for q in eps[v]}
                eps[target].update(reached)
        if old == tuple(frozenset(row) for row in eps):
            break
    return TopNFA(n, eps, edges, rounds)


def lift(g: Graph, roots: tuple[int, ...], cs: tuple[Clause, ...]) -> tuple[Graph, tuple[int, ...]]:
    """Build the labelled lift of the supplied positive projected valuation."""
    nfa = top_nfa(len(roots), cs)
    pairs: list[tuple[int, frozenset[int]]] = []
    lookup: dict[tuple[int, frozenset[int]], int] = {}
    out: list[Node] = []

    def intern(pair: tuple[int, frozenset[int]]) -> int:
        if pair not in lookup:
            lookup[pair] = len(pairs)
            pairs.append(pair)
            out.append(B)
        return lookup[pair]

    new_roots = tuple(intern((q, nfa.closure({x}))) for x, q in enumerate(roots))
    i = 0
    while i < len(pairs):
        q, states = pairs[i]
        if nfa.n in states:
            assert g[q][0] == "P", "forced top outside positive projection"
            out[i] = T
        elif g[q][0] == "B":
            out[i] = B
        else:
            assert g[q][0] == "P", "positive model must be top-free"
            l = intern((g[q][1], nfa.step(states, 0)))
            r = intern((g[q][2], nfa.step(states, 1)))
            out[i] = ("P", l, r)
        i += 1
    return tuple(out), new_roots


def all_graphs(n: int, top: bool) -> list[Graph]:
    options = [B] + ([T] if top else []) + [("P", l, r) for l in range(n) for r in range(n)]
    return list(product(options, repeat=n))


def all_words(depth: int) -> list[tuple[int, ...]]:
    return [w for d in range(depth + 1) for w in product((0, 1), repeat=d)]


def finite_trees(depth: int) -> list:
    if depth == 0:
        return ["B", "T"]
    smaller = finite_trees(depth - 1)
    return ["B", "T"] + [(l, r) for l in smaller for r in smaller]


def graph_of_tree(t) -> Graph:
    nodes: list[Node] = []
    def visit(s) -> int:
        q = len(nodes)
        nodes.append(B)
        if s == "B":
            nodes[q] = B
        elif s == "T":
            nodes[q] = T
        else:
            l, r = visit(s[0]), visit(s[1])
            nodes[q] = ("P", l, r)
        return q
    visit(t)
    return tuple(nodes)


def literal_finite_below(s, t) -> bool:
    if s == "B" or t == "T":
        return True
    if s == "T" or t == "B":
        return False
    return literal_finite_below(s[0], t[0]) and literal_finite_below(s[1], t[1])


def bounded_derivation(n: int, cs: tuple[Clause, ...], cap: int) -> set[tuple[int, tuple[int, ...]]]:
    """Literal finite closure with a stack cap; missing facts remain UNKNOWN."""
    facts = {(c[1], w) for c in cs if c[0] == "top" for w in all_words(cap)}
    changed = True
    while changed:
        changed = False
        new = set(facts)
        for x, w in facts:
            for c in cs:
                if c[0] == "le" and x == c[1]:
                    new.add((c[2], w))
                elif c[0] == "prod":
                    p, l, r = c[1:]
                    if len(w) < cap:
                        if x == l:
                            new.add((p, (0,) + w))
                        if x == r:
                            new.add((p, (1,) + w))
                    if x == p and w:
                        new.add((l if w[0] == 0 else r, w[1:]))
        if new != facts:
            facts = new
            changed = True
    return facts


def run() -> dict:
    counts: Counter = Counter()
    trees = finite_trees(2)
    gs = [graph_of_tree(t) for t in trees]
    for s, g in zip(trees, gs):
        for t, h in zip(trees, gs):
            actual = literal_finite_below(s, t)
            assert actual == below(g, 0, h, 0)
            p, q = projection(g), projection(g, True)
            r, v = projection(h), projection(h, True)
            assert actual == (below(p, 0, r, 0) and below(v, 0, q, 0))
            counts["finite_tree_order_pairs"] += 1

    cyclic = all_graphs(2, True)
    for g in cyclic:
        for h in cyclic:
            for a in range(2):
                for b in range(2):
                    actual = below(g, a, h, b)
                    assert actual == (below(projection(g), a, projection(h), b)
                                      and below(projection(h, True), b, projection(g, True), a))
                    assert actual == below(dual_graph(h), b, dual_graph(g), a)
                    counts["cyclic_graph_order_pairs"] += 1

    n = 2
    roots = (0, 1)
    clauses = ([("le", x, y) for x in range(n) for y in range(n)]
               + [(k, x) for k in ("bot", "top") for x in range(n)]
               + [("prod", x, l, r) for x in range(n) for l in range(n) for r in range(n)])
    systems = [tuple(c) for size in range(3) for c in combinations(clauses, size)]
    rng = random.Random(SEED)
    systems += [tuple(rng.sample(clauses, rng.randint(3, 8))) for _ in range(250)]
    # Important longer recurrent/shared-variable fixtures, expressed with exact naming.
    systems += [
        (("prod", 0, 0, 0), ("le", 0, 1)),
        (("prod", 0, 1, 1), ("top", 1)),
        (("top", 0), ("bot", 0)),
        (("prod", 0, 0, 1), ("bot", 1)),
        (("prod", 0, 1, 0), ("top", 1)),
        (("prod", 0, 1, 1), ("prod", 1, 0, 0)),
    ]
    pos_graphs = all_graphs(2, False)
    projected_truth = [[holds(g, roots, c, True) for c in clauses] for g in pos_graphs]
    source_truth = [[holds(g, roots, c) for c in clauses] for g in cyclic]
    idx = {c: i for i, c in enumerate(clauses)}
    max_lift_nodes = 0
    max_rounds = 0
    missed_derivations = 0
    for cs in systems:
        dc = tuple(dual_clause(c) for c in cs)
        assert tuple(dual_clause(c) for c in dc) == cs
        pmodels = [g for g, row in zip(pos_graphs, projected_truth) if all(row[idx[c]] for c in cs)]
        qmodels = [g for g, row in zip(pos_graphs, projected_truth) if all(row[idx[c]] for c in dc)]
        if not pmodels or not qmodels:
            counts["systems_without_two_bounded_projection_witnesses_UNKNOWN"] += 1
        else:
            counts["systems_with_two_projection_witnesses"] += 1
            for positive, original, is_dual in ((pmodels, cs, False), (qmodels, dc, True)):
                for g in positive:
                    h, hr = lift(g, roots, original)
                    assert models(h, hr, original), (cs, g, h, hr, is_dual)
                    projected_h = projection(h)
                    for x in roots:
                        assert equal(projected_h, hr[x], g, x)
                    max_lift_nodes = max(max_lift_nodes, len(h))
                    source_h = dual_graph(h) if is_dual else h
                    assert models(source_h, hr, cs)
                    for a in roots:
                        for b in roots:
                            w = separation(g, a, g, b)
                            if w is not None:
                                left, right = (b, a) if is_dual else (a, b)
                                assert not below(source_h, hr[left], source_h, hr[right])
                                # Same separating address in the relevant projection.
                                ph = projection(source_h, is_dual)
                                assert total_label(ph, hr[a], w) == "P"
                                assert total_label(ph, hr[b], w) == "B"
                                counts["same_word_countermodels"] += 1
                    counts["projected_models_lifted"] += 1
        for g, row in zip(cyclic, source_truth):
            if all(row[idx[c]] for c in cs):
                assert models(projection(g), roots, cs, True)
                assert models(projection(g, True), roots, dc, True)
                counts["source_model_projection_checks"] += 1
        nfa = top_nfa(n, cs)
        max_rounds = max(max_rounds, nfa.rounds)
        direct = bounded_derivation(n, cs, 6)
        for x in range(n):
            for w in all_words(3):
                recognized = nfa.accepts(x, w)
                derived = (x, w) in direct
                if derived:
                    assert recognized, (cs, x, w)
                if recognized and not derived:
                    missed_derivations += 1
                counts["bounded_derivation_membership_comparisons"] += 1
                if recognized:
                    for v in all_words(2):
                        assert nfa.accepts(x, w + v), (cs, x, w, v)
                        counts["right_ideal_checks"] += 1
        counts["systems_checked"] += 1

    # Larger exact cyclic/shared-variable fixtures exercise nontrivial top cones.
    targeted = [
        (
            (("P", 1, 2), ("P", 0, 2), T),
            (("prod", 0, 1, 2), ("prod", 1, 0, 2), ("top", 2)),
        ),
        (
            (("P", 1, 3), ("P", 2, 3), T, B),
            (("prod", 0, 1, 3), ("prod", 1, 2, 3), ("top", 2), ("bot", 3)),
        ),
        (
            (("P", 2, 3), ("P", 3, 2), T, T),
            (("prod", 0, 2, 3), ("prod", 1, 3, 2), ("le", 0, 1), ("top", 2)),
        ),
    ]
    for source, cs in targeted:
        rs = tuple(range(len(source)))
        assert models(source, rs, cs)
        nfa = top_nfa(len(rs), cs)
        max_rounds = max(max_rounds, nfa.rounds)
        for negative in (False, True):
            dc = tuple(dual_clause(c) for c in cs) if negative else cs
            g = projection(source, negative)
            h, hr = lift(g, rs, dc)
            assert models(h, hr, dc)
            assert models(dual_graph(h) if negative else h, hr, cs)
            for x in rs:
                assert equal(projection(h), hr[x], g, x)
            max_lift_nodes = max(max_lift_nodes, len(h))
            counts["larger_targeted_lifts"] += 1
        for x in rs:
            for w in all_words(6):
                if nfa.accepts(x, w):
                    assert total_label(source, x, w) == "T"
                counts["larger_top_cone_membership_checks"] += 1

    # Literal source regression facts, with exact (not corpus-based) answers.
    bot, top, omega = (B,), (T,), (("P", 0, 0),)
    top_product = (T, ("P", 0, 0))
    assert not below(top, 0, top_product, 1)
    assert below(omega, 0, omega, 0)
    assert below((B, ("P", 0, 0)), 1, top, 0)
    assert not below(top, 0, bot, 0)
    ambient = (("P", 0, 0), T)
    assert models(ambient, roots, (("prod", 0, 0, 0), ("le", 0, 1)))
    assert not below(ambient, 1, ambient, 0)
    assert below(projection(ambient), 1, projection(ambient), 0)
    assert not below(projection(ambient, True), 0, projection(ambient, True), 1)

    # Positive and negative projections can EACH be satisfiable when their naive
    # independently selected valuations fail the covering condition.
    assert models((B, B), roots, (), True)
    assert total_label((B, B), 0, ()) == "B"
    counts["literal_boundary_fixtures"] = 6
    return {
        "status": "PASS",
        "source_base": BASE,
        "seed": SEED,
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "counts": dict(sorted(counts.items())),
        "maximum_lift_graph_nodes": max_lift_nodes,
        "maximum_nfa_saturation_rounds": max_rounds,
        "nfa_positive_without_bounded_derivation_UNKNOWN": missed_derivations,
        "bounds": {"finite_tree_depth": 2, "enumerated_graph_nodes": 2, "targeted_graph_nodes_at_most": 4, "all_system_clause_count_at_most": 2,
                   "additional_seeded_systems": 250, "random_max_clauses": 8,
                   "direct_derivation_stack_cap": 6, "comparison_word_depth": 3,
                   "right_extension_depth": 2},
        "limits": [
            "All graph comparisons are exact for the given regular graph unfoldings.",
            "The input/model corpus is finite; it supplies no universal model bound.",
            "Absent bounded model witnesses and capped derivation misses remain UNKNOWN.",
            "No C081 implementation was executed; its use in the decision proof is imported.",
            "No independent mathematical reviewer or full repository suite was run by this script.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("results/explicit-top-dual-projection.json"))
    args = parser.parse_args()
    result = run()
    result["script_sha256"] = sha256(Path(__file__).read_bytes()).hexdigest()
    result["command"] = "python3 experiments/check_explicit_top_dual_projection.py --output results/explicit-top-dual-projection.json"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
