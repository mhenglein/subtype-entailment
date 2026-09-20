#!/usr/bin/env python3
"""Independent finite evidence for the #70 bottom-marker reduction.

No Subtail implementation is imported. NFA universality is checked by subset
reachability; small NFAs also have an independent configuration-path oracle.
Literal finite-graph tree inclusion checks complete infinite unfoldings. Tests
are evidence, not a proof of universal quantification over arbitrary trees.
Run: python3 experiments/check_hr_topfree_transfer_70.py --output results/hr-topfree-transfer-70.json
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import random

BASE = "19b06d4fed9da635d9b911f0e908d04e4fc4b099"
SEED = 2026092070


@dataclass(frozen=True)
class NFA:
    n: int
    edges: tuple[tuple[int, int, int], ...]  # label -1 is epsilon

    def close(self, mask: int) -> int:
        while True:
            old = mask
            for i, a, j in self.edges:
                if a == -1 and mask & (1 << i):
                    mask |= 1 << j
            if mask == old:
                return mask

    def step(self, mask: int, a: int) -> int:
        mask = self.close(mask)
        out = 0
        for i, b, j in self.edges:
            if a == b and mask & (1 << i):
                out |= 1 << j
        return self.close(out)

    def missing(self) -> str | None:
        start = self.close(1)
        queue = deque([(start, "")])
        seen = {start}
        while queue:
            s, w = queue.popleft()
            if s == 0:
                return w
            for a in (0, 1):
                t = self.step(s, a)
                if t not in seen:
                    seen.add(t)
                    queue.append((t, w + str(a)))
        return None

    def accepts_literal(self, word: str, start: int = 0) -> bool:
        # Independent nondeterministic (state, position) graph; no subset code.
        queue = deque([(start, 0)])
        seen = set()
        while queue:
            i, pos = queue.popleft()
            if (i, pos) in seen:
                continue
            seen.add((i, pos))
            if pos == len(word):
                return True  # every state accepts
            for j, a, k in self.edges:
                if j == i:
                    if a == -1:
                        queue.append((k, pos))
                    elif str(a) == word[pos]:
                        queue.append((k, pos + 1))
        return False


class Trees:
    """A node is bottom (None) or product (two child indices)."""
    def __init__(self, nodes=None):
        # 0 bottom, 1 Omega, 2 K, 3 K's inner product.
        self.nodes = list(nodes) if nodes is not None else [None, (1, 1), (3, 0), (2, 2)]

    def pair(self, x: int, y: int) -> int:
        self.nodes.append((x, y))
        return len(self.nodes) - 1

    def marker(self, x: int, y: int) -> int:
        return self.pair(self.pair(x, y), 0)

    def separating(self, x: int, y: int) -> str | None:
        # Complete inclusion on finite graphs, not a finite-depth approximation.
        queue = deque([(x, y, "")])
        seen = set()
        while queue:
            x, y, w = queue.popleft()
            if (x, y) in seen:
                continue
            seen.add((x, y))
            left, right = self.nodes[x], self.nodes[y]
            if left is None:
                continue
            if right is None:
                return w
            for a in (0, 1):
                queue.append((left[a], right[a], w + str(a)))
        return None

    def le(self, x: int, y: int) -> bool:
        return self.separating(x, y) is None

    def member(self, x: int, word: str) -> bool:
        for a in word:
            node = self.nodes[x]
            if node is None:
                return False
            x = node[int(a)]
        return self.nodes[x] is not None


def code(word: str) -> str:
    return "".join("0" + a for a in word)


def canonical(a: NFA) -> tuple[Trees, list[int]]:
    g = Trees()
    subsets = sorted({a.close(s) for s in range(1 << a.n)})
    roots = {0: 1}
    for s in subsets:
        if s:
            roots[s] = len(g.nodes)
            g.nodes.extend([None, None])
    for s in subsets:
        if s:
            p = roots[s]
            g.nodes[p] = (p + 1, 0)
            g.nodes[p + 1] = (roots[a.step(s, 0)], roots[a.step(s, 1)])
    return g, [roots[a.close(1 << i)] for i in range(a.n)]


def constraints(g: Trees, a: NFA, xs: list[int], z: int, b: int) -> list[tuple[int, int]]:
    out = [(g.marker(b, b), b)]
    for i, label, j in a.edges:
        rhs = xs[j] if label == -1 else (
            g.marker(xs[j], z) if label == 0 else g.marker(z, xs[j]))
        out.append((xs[i], rhs))
    return out


def words(max_length: int):
    for length in range(max_length + 1):
        for letters in product("01", repeat=length):
            yield "".join(letters)


def one_case(a: NFA, literal: bool) -> dict:
    v = a.missing()
    if literal:
        # A shortest missing word reaches an empty subset on a simple path.
        brute = next((w for w in words((1 << a.n) - 1)
                      if not a.accepts_literal(w)), None)
        assert brute == v, (a, brute, v)
    g, xs = canonical(a)
    graph_nodes = len(g.nodes)
    cs = constraints(g, a, xs, 1, 2)
    assert all(g.le(x, y) for x, y in cs), a
    assert (g.separating(xs[0], 2) is None) == (v is None), a
    if v is not None:
        w = code(v) + "1"
        assert not a.accepts_literal(v)
        assert all(a.accepts_literal(v[:i]) for i in range(len(v)))
        assert g.member(xs[0], w) and not g.member(2, w), (a, v, w)
    # Satisfiability does not rely on nonuniversality or the canonical graph.
    h = Trees()
    assert all(h.le(x, y) for x, y in constraints(h, a, [0] * a.n, 0, 2))
    return {"universal": v is None, "premises": len(cs), "nodes": graph_nodes}


def finite_trees(height: int):
    ts = [frozenset()]
    for _ in range(height):
        ts = [frozenset()] + [frozenset({""} | {"0" + w for w in x} |
              {"1" + w for w in y}) for x in ts for y in ts]
    return ts


def in_k(w: str) -> bool:
    return all(w[i] == "0" for i in range(0, len(w), 2))


def arbitrary_value_tests() -> dict:
    # Exhaust ALL three-free-node graphs plus a designated bottom node.
    # x=1,z=2,b=3 may be cyclic, partially coded, or wholly outside the image.
    choices = [None] + list(product(range(4), repeat=2))
    checked = satisfying = 0
    a = NFA(1, ((0, 0, 0), (0, 1, 0)))
    for table in product(choices, repeat=3):
        g = Trees([None, *table])
        cs = constraints(g, a, [1], 2, 3)
        checked += 1
        if all(g.le(x, y) for x, y in cs):
            satisfying += 1
            assert g.le(1, 3), table
    # Literal finite address-set test uses neither graph inclusion nor NFA code.
    finite = finite_trees(4)
    finite_sat = 0
    for x in finite:
        def in_upper(w, letter):
            if w in ("", "0"):
                return True
            if len(w) < 2 or w[0] != "0":
                return False
            return w[1] != letter or w[2:] in x  # other child is Omega
        if all(in_upper(w, "0") and in_upper(w, "1") for w in x):
            finite_sat += 1
            assert all(in_k(w) for w in x)
    return {"status": "PASS", "arbitrary_graph_valuations": checked,
            "satisfying_graph_valuations": satisfying,
            "literal_finite_values": len(finite), "satisfying_finite_values": finite_sat}


def repair_tests() -> dict:
    g = Trees()
    assert g.le(g.marker(2, 2), 2) and g.le(2, g.marker(2, 2))
    assert not g.le(1, g.marker(1, 1))
    # Literal HR with no transitions: both alpha=Omega and beta=Omega.
    assert g.le(g.pair(1, 1), 1) and g.le(1, 1)
    # Reversed query fails on the universal automaton: alpha=bottom, beta=K.
    a = NFA(1, ((0, 0, 0), (0, 1, 0)))
    assert all(g.le(x, y) for x, y in constraints(g, a, [0], 1, 2))
    assert not g.le(2, 0)
    # A finite reference cannot satisfy the recursive lower premise.
    finite_b = g.pair(0, 0)
    assert not g.le(g.marker(finite_b, finite_b), finite_b)
    # Dropping that premise and using a finite reference also fails on YES.
    assert g.le(2, g.marker(2, 1)) and g.le(2, g.marker(1, 2))
    assert not g.le(2, finite_b)
    fixtures = []
    for name, edges in (("no_edges", ()), ("only_0_loop", ((0, 0, 0),)),
                        ("both_loops", ((0, 0, 0), (0, 1, 0)))):
        a = NFA(1, edges)
        h, xs = canonical(a)
        assert all(h.le(x, y) for x, y in constraints(h, a, xs, 1, 2))
        fixtures.append({"name": name, "missing_word": a.missing(),
                         "shortest_graph_separator": h.separating(xs[0], 2)})
    return {"marker_pilots": {"status": "PASS", "fixtures": fixtures},
            "identity_transfer": {"status": "FAIL", "reason": "RHS is greatest Omega"},
            "reversed_query_repair": {"status": "FAIL", "reason": "bottom state valuation"},
            "finite_reference_repair": {"status": "FAIL", "reason": "recursive bound or YES case fails"}}


def run() -> dict:
    counts = {"exhaustive_nfas": 0, "random_nfas": 0, "universal": 0,
              "nonuniversal": 0, "premise_checks": 0, "maximum_model_nodes": 0}
    def add(a, literal, category):
        r = one_case(a, literal)
        counts[category] += 1
        counts["universal" if r["universal"] else "nonuniversal"] += 1
        counts["premise_checks"] += r["premises"]
        counts["maximum_model_nodes"] = max(counts["maximum_model_nodes"], r["nodes"])
    for n in (1, 2):
        slots = tuple(product(range(n), (-1, 0, 1), range(n)))
        for mask in range(1 << len(slots)):
            add(NFA(n, tuple(e for i, e in enumerate(slots) if mask & (1 << i))),
                True, "exhaustive_nfas")
    rng = random.Random(SEED)
    for n in range(3, 7):
        for k in range(100):
            # Half have no epsilon transitions, avoiding trivial epsilon collapse.
            edges = tuple((i, a, j) for i, a, j in product(range(n), (-1, 0, 1), range(n))
                          if rng.random() < (0 if a == -1 and k % 2 else 0.20))
            add(NFA(n, edges), False, "random_nfas")
    return {"status": "PASS", "base_commit": BASE, "seed": SEED,
            "python": platform.python_version(), "platform": platform.system(),
            "machine": platform.machine(),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope": "finite experiment families; ordinary all-input proof is separate",
            "nfa_and_graph_checks": counts, "non_image_value_checks": arbitrary_value_tests(),
            "repair_checks": repair_tests(),
            "independent_mathematical_review": "UNKNOWN",
            "lean_and_full_repository_checks": "NOT RUN",
            "original_pdf_page_image_check": "NOT RUN"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()  # Assertion failures terminate with a nonzero exit status.
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
