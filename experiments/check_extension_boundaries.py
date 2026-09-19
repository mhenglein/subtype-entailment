#!/usr/bin/env python3
"""E053: literal boundary checks, not a general extension decision procedure."""
import argparse
from collections import deque
from functools import lru_cache
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BOTTOM = ("bottom",)
TOP = ("top",)


def product(left, right):
    return ("product", left, right)


@lru_cache(None)
def finite_trees(depth, with_top=True):
    leaves = (BOTTOM, TOP) if with_top else (BOTTOM,)
    if depth == 0:
        return leaves
    smaller = finite_trees(depth - 1, with_top)
    return leaves + tuple(product(x, y) for x in smaller for y in smaller)


def finite_below(left, right, contravariant=False):
    """The literal root-label order on finite trees, with the chosen variance."""
    if left == BOTTOM or right == TOP:
        return True
    if left == TOP or right == BOTTOM:
        return False
    if contravariant:
        domain = finite_below(right[1], left[1], True)
    else:
        domain = finite_below(left[1], right[1])
    return domain and finite_below(left[2], right[2], contravariant)


def addresses(tree):
    if tree[0] != "product":
        return frozenset()
    return frozenset([()] + [(0,) + w for w in addresses(tree[1])]
                     + [(1,) + w for w in addresses(tree[2])])


class Graphs:
    """Finite bottom/product graphs: node 0 is bottom, node 1 is Omega."""

    def __init__(self):
        self.nodes = [None, (1, 1)]
        self.intern = {(1, 1): 1}

    def pair(self, left, right):
        key = (left, right)
        if key not in self.intern:
            self.intern[key] = len(self.nodes)
            self.nodes.append(key)
        return self.intern[key]

    def substitute(self, tree):
        if tree == BOTTOM:
            return 0
        if tree == TOP:
            return 1
        return self.pair(self.substitute(tree[1]), self.substitute(tree[2]))


def graph_below(nodes, left, right):
    """Reject exactly when a reachable pair has product on left, bottom on right.

    A queued pair corresponds to one common address. If the left is bottom,
    no longer product address needs comparison. Otherwise both child pairs
    are required. The finite pair set makes visited-state closure exact even
    on cycles. This algorithm does not call the finite-tree order predicate.
    """
    assert all(node is None or (len(node) == 2 and all(
        isinstance(v, int) and 0 <= v < len(nodes) for v in node)) for node in nodes)
    pending = deque([(left, right)])
    seen = set()
    while pending:
        pair = pending.popleft()
        if pair in seen:
            continue
        seen.add(pair)
        a, b = (nodes[i] for i in pair)
        if a is None:
            continue
        if b is None:
            return False
        pending.extend(zip(a, b))
    return True


def render(tree):
    if len(tree) == 1:
        return tree[0]
    return f"({render(tree[1])} * {render(tree[2])})"


def run():
    trees = finite_trees(2)
    assert len(trees) == 38 and len(set(trees)) == 38
    graphs = Graphs()
    image = {tree: graphs.substitute(tree) for tree in trees}
    counts = {"both_true": 0, "both_false": 0,
              "source_true_image_false": 0, "source_false_image_true": 0}
    for left in trees:
        for right in trees:
            source = finite_below(left, right)
            target = graph_below(graphs.nodes, image[left], image[right])
            key = ("both_true" if source else "source_false_image_true") if target else (
                "source_true_image_false" if source else "both_false")
            counts[key] += 1
    assert sum(counts.values()) == 38**2
    assert counts["source_true_image_false"] == 0  # bounded preservation only
    assert counts["source_false_image_true"] > 0

    top_product = product(TOP, TOP)
    assert not finite_below(TOP, top_product)
    assert graph_below(graphs.nodes, image[TOP], image[top_product])
    nonbottom = product(BOTTOM, BOTTOM)
    assert finite_below(nonbottom, TOP)
    assert not finite_below(nonbottom, BOTTOM)
    # Finite graphs independently validate the zero-spine countermodel.
    spine_nodes = [None, (1, 0), (1, 0)]
    assert graph_below(spine_nodes, 2, 1)  # x * bottom <= x
    assert not graph_below(spine_nodes, 1, 0)  # x <= bottom fails
    finite_no_top = finite_trees(4, False)
    finite_models = sum(finite_below(product(x, BOTTOM), x) for x in finite_no_top)
    assert len(finite_no_top) == 677 and finite_models == 0
    # This finite census supplements, but does not prove, the all-depth argument.

    arrow_left = product(nonbottom, BOTTOM)
    arrow_right = nonbottom
    assert finite_below(arrow_left, arrow_right, contravariant=True)
    assert not addresses(arrow_left).issubset(addresses(arrow_right))
    assert not finite_below(arrow_right, arrow_left, contravariant=True)
    assert addresses(arrow_right).issubset(addresses(arrow_left))
    # An independent finite-domain cross-check of the graph order without top.
    small = finite_trees(3, False)
    small_images = {tree: graphs.substitute(tree) for tree in small}
    for left in small:
        for right in small:
            actual = graph_below(graphs.nodes, small_images[left], small_images[right])
            assert actual == addresses(left).issubset(addresses(right))

    return {
        "experiment": "E053",
        "status": "PASS",
        "meaning": "Exact literal counterexamples and bounded comparisons; no general extension theorem.",
        "base_mathematical_revision": "c946d86b9e65da2877e0df42c710abbdcb5a4037",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "top_to_omega": {
            "source_depth": 2, "trees": len(trees), "pairs": len(trees)**2,
            "counts": counts,
            "reflection_counterexample": {
                "left": render(TOP), "right": render(top_product),
                "source_below": False, "image_below": True,
            },
        },
        "top_to_bottom": {"left": render(nonbottom), "right": "top",
                          "source_below": True, "image_below": False},
        "zero_spine": {"graph": spine_nodes, "x": 1, "bottom": 0,
                       "x_times_bottom": 2, "premise": True, "query": False,
                       "finite_depth": 4, "finite_trees": len(finite_no_top),
                       "finite_models_in_census": finite_models},
        "contravariance": {"left": "((bottom -> bottom) -> bottom)",
                           "right": "(bottom -> bottom)", "below": True,
                           "branch_address_inclusion": False,
                           "reversed_below": False, "reversed_inclusion": True},
        "graph_order_independent_finite_check": {"trees": len(small), "pairs": len(small)**2,
                                                "predicate": "literal product-address inclusion"},
        "unproved_by_this_check": ["top-extension decidability", "arbitrary-size encoding preservation",
                                   "regular-countermodel theorem", "generic arity or multiple constructors"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the deterministic evidence JSON.")
    parser.add_argument("--check", type=Path, help="Compare with an existing evidence JSON.")
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    if args.check and json.loads(args.check.read_text()) != json.loads(text):
        raise SystemExit("FAIL: saved boundary evidence differs")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
