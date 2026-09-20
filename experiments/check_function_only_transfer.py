#!/usr/bin/env python3
"""Independent function-only semantic diagnostics for Subtail #74 / #72.

No Subtail imports. This checks finite trees and SUPPLIED regular graphs;
it is not a solver for entailment over unknown arbitrary-tree valuations.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import random
import sys
import time
from typing import Any

BASE = "19b06d4fed9da635d9b911f0e908d04e4fc4b099"
SEED = 2026092074
Tree = Any  # None for bottom, (left, right) for a finite function tree.
Fact = tuple[int, str]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


@lru_cache(maxsize=None)
def finite_leq(s: Tree, t: Tree) -> bool:
    if s is None:
        return True
    if t is None:
        return False
    return finite_leq(t[0], s[0]) and finite_leq(s[1], t[1])


@lru_cache(maxsize=None)
def nodes(t: Tree) -> frozenset[str]:
    if t is None:
        return frozenset()
    return frozenset({""} | {"0" + w for w in nodes(t[0])}
                     | {"1" + w for w in nodes(t[1])})


def finite_trees(depth: int) -> list[Tree]:
    out: list[Tree] = [None]
    for _ in range(depth):
        out = [None] + list(product(out, repeat=2))
    return out


def prefixes(w: str) -> list[str]:
    return [w[:i] for i in range(len(w))]


def guarded_bad(s: Tree, t: Tree) -> str | None:
    a, b = nodes(s), nodes(t)
    for w in sorted(a | b, key=lambda u: (len(u), u)):
        active = all(v in a and v in b for v in prefixes(w))
        bad = (w in b and w not in a) if w.count("0") % 2 else (w in a and w not in b)
        if active and bad:
            return w
    return None


def unguarded_signed(s: Tree, t: Tree) -> bool:
    a, b = nodes(s), nodes(t)
    return all((w not in b or w in a) if w.count("0") % 2
               else (w not in a or w in b) for w in a | b)


@dataclass(frozen=True)
class Graph:
    states: tuple[tuple[int, int] | None, ...]
    root: int = 0

    def __post_init__(self) -> None:
        require(0 <= self.root < len(self.states), "invalid graph root")
        for state in self.states:
            if state is not None:
                require(len(state) == 2 and all(0 <= c < len(self.states) for c in state),
                        "invalid graph children")


def tree_graph(t: Tree) -> Graph:
    table: list[tuple[int, int] | None] = []
    index: dict[Tree, int] = {}

    def add(v: Tree) -> int:
        if v not in index:
            children = None if v is None else (add(v[0]), add(v[1]))
            index[v] = len(table)
            table.append(children)
        return index[v]

    root = add(t)
    return Graph(tuple(table), root)


def graph_gfp(g: Graph, h: Graph) -> bool:
    """Descending relation elimination on the disjoint UNION of graph states.

    Both orientations are necessary: the domain dependency reverses the pair.
    No word enumeration, parity function, or guarded-path code is used here.
    """
    offset = len(g.states)
    states = g.states + tuple(None if s is None else (s[0] + offset, s[1] + offset)
                              for s in h.states)
    relation = set(product(range(len(states)), repeat=2))
    while True:
        new = {(i, j) for i, j in relation if states[i] is None or
               (states[j] is not None and
                (states[j][0], states[i][0]) in relation and
                (states[i][1], states[j][1]) in relation)}
        if new == relation:
            return (g.root, h.root + offset) in new
        relation = new


def graph_bad_path(g: Graph, h: Graph) -> str | None:
    """Ascending reachability on signed cross-graph pairs; exact finite search."""
    todo = deque([(g.root, h.root, 0, "")])
    seen: set[tuple[int, int, int]] = set()
    while todo:
        i, j, sign, word = todo.popleft()
        key = (i, j, sign)
        if key in seen:
            continue
        seen.add(key)
        a, b = g.states[i], h.states[j]
        low, high = (b, a) if sign else (a, b)
        if low is None:
            continue
        if high is None:
            return word
        todo.append((a[0], b[0], sign ^ 1, word + "0"))
        todo.append((a[1], b[1], sign, word + "1"))
    return None


def graph_word_bad(g: Graph, h: Graph, w: str) -> bool:
    i, j, sign = g.root, h.root, 0
    for letter in w:
        a, b = g.states[i], h.states[j]
        if a is None or b is None:
            return False
        bit = int(letter)
        i, j = a[bit], b[bit]
        sign ^= bit == 0
    a, b = g.states[i], h.states[j]
    return (b is not None and a is None) if sign else (a is not None and b is None)


def variable_closure(seed: set[Fact], constraints: list[tuple[int, int]]) -> set[Fact]:
    """EXACT all-word closure for VARIABLE-ONLY inequalities and finite seeds.

    No rule introduces a word absent from the seeds and their prefixes, so
    this finite saturation is exact. No constructor-constraint solver is claimed.
    """
    facts = set(seed)
    words = {""} | {w[:i] for _, w in seed for i in range(len(w) + 1)}
    while True:
        new = facts | {(x, w[:-1]) for x, w in facts if w}
        for x, y in constraints:
            if (x, "") in facts:
                new.add((y, ""))
            for w in words - {""}:
                low, high = (y, x) if w.count("0") % 2 else (x, y)
                if (low, w) in facts and (high, w[:-1]) in facts:
                    new.add((high, w))
        if new == facts:
            return new
        facts = new


def from_nodes(p: set[str], prefix: str = "") -> Tree:
    if prefix not in p:
        return None
    return (from_nodes(p, prefix + "0"), from_nodes(p, prefix + "1"))


def expr_eval(e: Any, rho: dict[str, Tree]) -> Tree:
    if e is None:
        return None
    if isinstance(e, str):
        return rho[e]
    return (expr_eval(e[0], rho), expr_eval(e[1], rho))


def atom(e: Any, w: str) -> bool | tuple[str, str]:
    if e is None:
        return False
    if isinstance(e, str):
        return e, w
    if not w:
        return True
    return atom(e[int(w[0])], w[1:])


def horn_holds(e: Any, f: Any, rho: dict[str, Tree]) -> bool:
    facts = {x: nodes(t) for x, t in rho.items()}

    def value(a: bool | tuple[str, str]) -> bool:
        return a if isinstance(a, bool) else a[1] in facts[a[0]]

    # Exact finite check: outside this union both possible mismatch facts are false.
    words = nodes(expr_eval(e, rho)) | nodes(expr_eval(f, rho)) | {""}
    for w in words:
        low, high = (f, e) if w.count("0") % 2 else (e, f)
        body = value(atom(low, w))
        if w:
            body = body and value(atom(high, w[:-1]))
        if body and not value(atom(high, w)):
            return False
    return True


def run() -> dict[str, Any]:
    started = time.perf_counter()
    B, A = (None, None), ((None, None), None)
    require(finite_leq(None, A) and not unguarded_signed(None, A), "inactive parity fixture")
    require(finite_leq(A, B) and not finite_leq(B, A), "arrow direction fixture")
    S1, S2 = {(1, ""), (1, "0")}, {(0, ""), (1, "")}
    C = [(0, 1)]
    require(variable_closure(S1, C) == S1 and variable_closure(S2, C) == S2, "individual closures")
    combined = variable_closure(S1 | S2, C)
    require(combined == S1 | S2 | {(0, "0")}, "nonadditive closure fixture")

    trees = finite_trees(3)
    finite_pairs = 0
    for s, t in product(trees, repeat=2):
        expected = finite_leq(s, t)
        g, h = tree_graph(s), tree_graph(t)
        witness = graph_bad_path(g, h)
        require(expected == (guarded_bad(s, t) is None), "finite active-path disagreement")
        require(expected == graph_gfp(g, h) == (witness is None), "finite graph disagreement")
        if witness is not None:
            require(graph_word_bad(g, h, witness), "bad graph certificate")
        finite_pairs += 1

    exprs = [None, "x", "y", ("x", "y"), ("y", "x"), ("x", "x"),
             (None, "x"), ("x", None), (("x", "x"), "y")]
    expression_cases = 0
    for x, y in product(finite_trees(2), repeat=2):
        rho = {"x": x, "y": y}
        for e, f in product(exprs, repeat=2):
            require(horn_holds(e, f, rho) == finite_leq(expr_eval(e, rho), expr_eval(f, rho)),
                    "expression Horn expansion disagreement")
            expression_cases += 1

    canonical_cases = 0
    witness_classes = {"empty": 0, "nonempty_even": 0, "odd": 0}
    for constraints in [[], [(0, 1)], [(1, 0)], [(0, 1), (1, 0)]]:
        for rho in product(trees, repeat=2):
            if not all(finite_leq(rho[x], rho[y]) for x, y in constraints):
                continue
            for x, y in [(0, 1), (1, 0)]:
                w = guarded_bad(rho[x], rho[y])
                if w is None:
                    continue
                low, high = (y, x) if w.count("0") % 2 else (x, y)
                seeds = {(x, v) for v in prefixes(w)} | {(y, v) for v in prefixes(w)} | {(low, w)}
                closure = variable_closure(seeds, constraints)
                require((high, w) not in closure, "canonical coverage failure")
                reconstructed = tuple(from_nodes({u for v, u in closure if v == z}) for z in range(2))
                require(all(finite_leq(reconstructed[a], reconstructed[b]) for a, b in constraints),
                        "canonical premise reconstruction failure")
                require(not finite_leq(reconstructed[x], reconstructed[y]), "canonical query reconstruction failure")
                require(graph_word_bad(tree_graph(reconstructed[x]), tree_graph(reconstructed[y]), w),
                        "canonical same-address reconstruction failure")
                canonical_cases += 1
                witness_classes["empty" if not w else "odd" if w.count("0") % 2 else "nonempty_even"] += 1

    graphs: list[Graph] = []
    for n in (1, 2):
        choices = [None] + list(product(range(n), repeat=2))
        graphs.extend(Graph(tuple(states)) for states in product(choices, repeat=n))
    graph_pairs = 0
    for g, h in product(graphs, repeat=2):
        witness = graph_bad_path(g, h)
        require(graph_gfp(g, h) == (witness is None), "exhaustive regular-graph disagreement")
        if witness is not None:
            require(graph_word_bad(g, h, witness), "regular certificate failure")
        graph_pairs += 1
    rng = random.Random(SEED)

    def random_graph() -> Graph:
        n = rng.randint(1, 6)
        choices = [None] + list(product(range(n), repeat=2))
        return Graph(tuple(rng.choice(choices) for _ in range(n)), rng.randrange(n))

    for _ in range(500):
        g, h = random_graph(), random_graph()
        w = graph_bad_path(g, h)
        require(graph_gfp(g, h) == (w is None), "random regular-graph disagreement")
        if w is not None:
            require(graph_word_bad(g, h, w), "random certificate failure")

    L = Graph(((0, 1), None))
    even = Graph(((1, 2), (0, 2), None))
    G = Graph(((1, 0), None))
    omega = Graph(((0, 0),))
    require(graph_gfp(L, even) and graph_gfp(even, L), "odd/even cycle equations")
    require(graph_gfp(L, G) and graph_gfp(omega, G) and not graph_gfp(G, omega), "greatest-spine fixtures")
    require(not graph_gfp(L, tree_graph(None)), "infinite nonbottom fixture")
    require(not any(finite_leq(t, (t, None)) and finite_leq((t, None), t) for t in trees),
            "unexpected bounded finite recursive solution")

    return {
        "status": "PASS", "input_revision": BASE, "session": "function-only-transfer-20260920",
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "environment": {"python": sys.version.split()[0], "platform": platform.platform(),
                        "workspace": "isolated standalone worktree; not a Subtail clone"},
        "command": "python3 experiments/check_function_only_transfer.py --output results/function-only-transfer.json",
        "random_seed": SEED,
        "counts": {"finite_trees_max_constructor_depth_3": len(trees), "finite_pair_comparisons": finite_pairs,
                   "finite_expression_Horn_cases": expression_cases,
                   "variable_only_canonical_countermodel_cases": canonical_cases,
                   "canonical_witness_classes": witness_classes,
                   "regular_graphs_on_one_or_two_labelled_states_root_zero": len(graphs),
                   "exhaustive_regular_graph_pairs": graph_pairs, "random_regular_graph_pairs_up_to_six_states": 500},
        "counterexample": {"B": "bottom -> bottom", "A": "B -> bottom",
                           "C": ["x <= y"], "S1": sorted(S1), "S2": sorted(S2),
                           "closure_union": sorted(combined), "new_fact": [0, "0"]},
        "named_checks": ["inactive odd-address parity refuted", "node-union closure refuted",
                         "odd and even contravariant cycles accepted coinductively",
                         "same-address canonical reconstruction", "finite model of (X->bottom)<=X",
                         "infinite greatest right-spine fixtures"],
        "limitations": ["Author-run independent ALGORITHMS, not independent mathematical review.",
                        "No Subtail, Lean, full-suite, integration or performance claim.",
                        "Finite expression truth checks are bounded evidence.",
                        "Variable-only finite-seed closure is exact; no general guarded-closure solver implemented.",
                        "Regular comparisons concern supplied graphs, not regular or arbitrary entailment.",
                        "Absence of finite recursive solutions in this census is not the all-depth proof."],
        "elapsed_seconds": round(time.perf_counter() - started, 6),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON receipt destination")
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
