#!/usr/bin/env python3
"""Conservative naming of finite bottom/product expressions (A010/A018, #31).

Input uses a topologically ordered node table. Reusing a node is syntax sharing,
not recursive syntax: each reference must point to an earlier row. Normalization
expands occurrences, reserving one bottom proxy iff bottom occurs in a used root.
Original variable indices are unchanged. The query is NEVER a premise.

This executable has an ordinary correctness proof, not a Lean certification.
It does not decide entailment and does not inspect, unfold, or enumerate models.
Python 3.9+; standard library only. See the dated implementation note.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Optional, Protocol, Sequence, Tuple, TypeVar


@dataclass(frozen=True)
class Node:
    op: str
    var: Optional[int] = None
    left: Optional[int] = None
    right: Optional[int] = None


@dataclass(frozen=True)
class Input:
    variables: int
    nodes: Tuple[Node, ...]
    premises: Tuple[Tuple[int, int], ...]
    query: Tuple[int, int]

    @classmethod
    def from_dict(cls, raw: Mapping[str, Any]) -> Input:
        """Parse and validate the finite syntax encoding; reject malformed inputs."""
        if not isinstance(raw, dict):
            raise ValueError("input must be a JSON object")
        _keys(raw, {"variables", "nodes", "premises", "query"}, "input")
        n = _nat(raw["variables"], "variables")
        if not isinstance(raw["nodes"], list):
            raise ValueError("nodes must be a list")
        nodes = []
        for i, row in enumerate(raw["nodes"]):
            if not isinstance(row, dict):
                raise ValueError(f"node {i} must be an object")
            op = row.get("op")
            if op == "var":
                _keys(row, {"op", "var"}, f"node {i}")
                nodes.append(Node(op, var=_index(row["var"], n, f"node {i} variable")))
            elif op == "bottom":
                _keys(row, {"op"}, f"node {i}")
                nodes.append(Node(op))
            elif op == "product":
                _keys(row, {"op", "left", "right"}, f"node {i}")
                nodes.append(Node(op, left=_index(row["left"], i, f"node {i} left"),
                                  right=_index(row["right"], i, f"node {i} right")))
            else:
                raise ValueError(f"node {i}: unknown op {op!r}")
        if not isinstance(raw["premises"], list):
            raise ValueError("premises must be a list")
        premises = tuple(_pair(p, len(nodes), "premise") for p in raw["premises"])
        query = _pair(raw["query"], len(nodes), "query")
        return cls(n, tuple(nodes), premises, query)

    def to_dict(self) -> dict:
        rows = []
        for node in self.nodes:
            row = {"op": node.op}
            if node.op == "var":
                row["var"] = node.var
            elif node.op == "product":
                row.update(left=node.left, right=node.right)
            rows.append(row)
        return {"variables": self.variables, "nodes": rows,
                "premises": [list(p) for p in self.premises], "query": list(self.query)}


def _keys(row: Mapping, expected: set, where: str) -> None:
    if set(row) != expected:
        raise ValueError(f"{where}: expected keys {sorted(expected)}")


def _nat(value: Any, where: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{where} must be a nonnegative integer (not bool)")
    return value


def _index(value: Any, size: int, where: str) -> int:
    result = _nat(value, where)
    if result >= size:
        raise ValueError(f"{where}: index {result} outside [0, {size})")
    return result


def _pair(value: Any, size: int, where: str) -> Tuple[int, int]:
    if not isinstance(value, (list, tuple)) or len(value) != 2:
        raise ValueError(f"{where} must contain two node indices")
    return (_index(value[0], size, where), _index(value[1], size, where))


# The argument order is precisely TreeSemantics.Constraint:
# leq(source,target), upper(source,left,right), lower(left,right,target), denial(source).
Clause = Tuple[Any, ...]


@dataclass(frozen=True)
class Binding:
    index: int
    op: str
    left: Optional[int] = None
    right: Optional[int] = None
    source_node: Optional[int] = None
    forest_root: Optional[int] = None


@dataclass(frozen=True)
class Output:
    original_variables: int
    variables: int
    definitions: Tuple[Clause, ...]
    premises: Tuple[Clause, ...]
    query: Tuple[int, int]
    bindings: Tuple[Binding, ...]

    @property
    def constraints(self) -> Tuple[Clause, ...]:
        return self.definitions + self.premises

    @property
    def extra(self) -> int:
        return self.variables - self.original_variables

    def to_dict(self) -> dict:
        bindings = []
        for b in self.bindings:
            row = {"index": b.index, "op": b.op}
            if b.op == "product":
                row.update(left=b.left, right=b.right, source_node=b.source_node,
                           forest_root=b.forest_root)
            bindings.append(row)
        p = sum(b.op == "product" for b in self.bindings)
        bottom = int(any(b.op == "bottom" for b in self.bindings))
        return {"schema": "subtail-normalized-v1",
                "original_variables": self.original_variables, "variables": self.variables,
                "definitions": [list(c) for c in self.definitions],
                "premises": [list(c) for c in self.premises], "query": list(self.query),
                "bindings": bindings,
                "counts": {"product_occurrences": p, "bottom_proxy": bottom,
                           "fresh_variables": self.extra, "definitions": len(self.definitions),
                           "premises": len(self.premises), "constraints": len(self.constraints)}}


def normalize(problem: Input) -> Output:
    """Total on validated finite syntax, with no recursion or search cutoff.

    Pass 1 determines whether a *reachable* bottom is present. Pass 2 is an
    explicit postorder stack, expanded once per forest occurrence. Children are
    already named when a fresh parent is emitted. Repeated syntax occurrences
    deliberately receive separate product names. Unused input nodes emit nothing.
    """
    # Validation is independent of Python annotations, including direct callers.
    if not isinstance(problem, Input):
        raise ValueError("normalize expects Input")
    problem = Input.from_dict(problem.to_dict())
    roots = [r for pair in problem.premises for r in pair] + list(problem.query)
    todo, seen = list(roots), set()
    has_bottom = False
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        node = problem.nodes[i]
        if node.op == "bottom":
            has_bottom = True
        elif node.op == "product":
            todo.extend((node.left, node.right))

    bottom_index = problem.variables
    bindings = [Binding(bottom_index, "bottom")] if has_bottom else []
    definitions = [("denial", bottom_index)] if has_bottom else []
    next_index = problem.variables + int(has_bottom)
    root_names = []
    for forest_root, root in enumerate(roots):
        stack, names = [(root, False)], []
        while stack:
            i, expanded = stack.pop()
            node = problem.nodes[i]
            if node.op == "var":
                names.append(node.var)
            elif node.op == "bottom":
                names.append(bottom_index)
            elif not expanded:
                # LIFO: left subtree, right subtree, then their parent.
                stack.extend(((i, True), (node.right, False), (node.left, False)))
            else:
                right, left = names.pop(), names.pop()
                parent = next_index
                next_index += 1
                bindings.append(Binding(parent, "product", left, right, i, forest_root))
                definitions.extend((("upper", parent, left, right),
                                    ("lower", left, right, parent)))
                names.append(parent)
        if len(names) != 1:
            raise AssertionError("internal postorder stack invariant")
        root_names.append(names[0])
    premises = tuple(("leq", root_names[2*i], root_names[2*i+1])
                     for i in range(len(problem.premises)))
    return Output(problem.variables, next_index, tuple(definitions), premises,
                  (root_names[-2], root_names[-1]), tuple(bindings))


T = TypeVar("T")


class TreeAlgebra(Protocol[T]):
    """Only bottom and product are needed; no membership or equality oracle."""
    def bottom(self) -> T: ...
    def product(self, left: T, right: T) -> T: ...


def extend(output: Output, original: Sequence[T], algebra: TreeAlgebra[T]) -> Tuple[T, ...]:
    """Evaluate the acyclic binding list; retain original values literally.

    Intended for outputs of normalize. Works for any bottom/product algebra;
    model-preservation theorems specialize it to TreeSemantics.Tree.
    """
    if len(original) != output.original_variables:
        raise ValueError("original valuation has the wrong number of variables")
    values = list(original)
    for b in output.bindings:
        if b.index != len(values):
            raise ValueError("bindings are not contiguous fresh indices")
        if b.op == "bottom":
            values.append(algebra.bottom())
        elif b.op == "product":
            left = _index(b.left, len(values), "binding left")
            right = _index(b.right, len(values), "binding right")
            values.append(algebra.product(values[left], values[right]))
        else:
            raise ValueError("unknown binding operation")
    if len(values) != output.variables:
        raise ValueError("inconsistent output variable count")
    return tuple(values)


def restrict(output: Output, values: Sequence[T]) -> Tuple[T, ...]:
    if len(values) != output.variables:
        raise ValueError("normalized valuation has the wrong number of variables")
    return tuple(values[:output.original_variables])


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", default="-", help="JSON path; - means stdin")
    parser.add_argument("--output", type=Path, help="write JSON here, otherwise stdout")
    args = parser.parse_args(argv)
    try:
        text = sys.stdin.read() if args.input == "-" else Path(args.input).read_text()
        result = normalize(Input.from_dict(json.loads(text))).to_dict()
        rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered)
        else:
            sys.stdout.write(rendered)
    except (ValueError, TypeError, OSError) as exc:
        print(f"normalization error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
