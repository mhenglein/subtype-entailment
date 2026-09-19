#!/usr/bin/env python3
"""Independent semantic checks for the finite-expression normalizer (#31).

Tree values are finite graphs denoting regular, possibly infinite trees.
Inclusion is decided by exact product-graph reachability, NOT a depth cutoff.
The production normalizer does not import this model evaluator or any solver.
Bounded syntax/valuation sampling is evidence, never general entailment NO.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from functools import lru_cache
from itertools import product
import hashlib
import json
from pathlib import Path
import platform
import random
import subprocess
import sys

from expression_normalization import Input, normalize, extend, restrict

SEED = 2026091931
ROOT = Path(__file__).resolve().parents[1]


class Arena:
    """A finite coalgebra: None is bottom; (left,right) is a product node.

    A value is a state index. Cycles may denote infinite trees. Appending states
    never changes the meaning of existing states. Base cyclic states are filled
    before any cached semantic comparison is made.
    """
    def __init__(self):
        self.nodes = [None]
        self.intern = {}

    def bottom(self):
        return 0

    def product(self, left, right):
        pair = (left, right)
        if pair not in self.intern:
            self.intern[pair] = len(self.nodes)
            self.nodes.append(pair)
        return self.intern[pair]

    def graph(self, rows, root=0):
        start = len(self.nodes)
        self.nodes.extend(None if row is None else (start+row[0], start+row[1])
                          for row in rows)
        return start+root

    @lru_cache(maxsize=200000)
    def below(self, left, right):
        todo, seen = [(left, right)], set()
        while todo:
            a, b = todo.pop()
            if (a, b) in seen:
                continue
            seen.add((a, b))
            sa, sb = self.nodes[a], self.nodes[b]
            if sa is None:
                continue
            if sb is None:
                return False
            todo.extend(((sa[0], sb[0]), (sa[1], sb[1])))
        return True

    def equal(self, left, right):
        return self.below(left, right) and self.below(right, left)

    def has(self, root, word):
        for a in word:
            node = self.nodes[root]
            if node is None:
                return False
            root = node[a]
        return self.nodes[root] is not None

    def separator(self, left, right):
        """Shortest finite address witnessing a failed inclusion, or None."""
        todo, seen = deque([(left, right, ())]), set()
        while todo:
            a, b, word = todo.popleft()
            if (a, b) in seen:
                continue
            seen.add((a, b))
            sa, sb = self.nodes[a], self.nodes[b]
            if sa is None:
                continue
            if sb is None:
                return word
            for bit in (0, 1):
                todo.append((sa[bit], sb[bit], word+(bit,)))
        return None


def original_eval(problem, rho, arena):
    """Independent topological evaluation of INPUT syntax, not proxy bindings."""
    values = []
    for node in problem.nodes:
        if node.op == "bottom":
            values.append(arena.bottom())
        elif node.op == "var":
            values.append(rho[node.var])
        elif node.op == "product":
            values.append(arena.product(values[node.left], values[node.right]))
        else:
            raise AssertionError("invalid input in checker")
    return values


def original_models(problem, rho, arena):
    values = original_eval(problem, rho, arena)
    return all(arena.below(values[l], values[r]) for l, r in problem.premises)


def holds(clause, eta, arena):
    """Literal reading of the four TreeSemantics.Constraint constructors."""
    op, *v = clause
    if op == "leq":
        return arena.below(eta[v[0]], eta[v[1]])
    if op == "upper":
        return arena.below(eta[v[0]], arena.product(eta[v[1]], eta[v[2]]))
    if op == "lower":
        return arena.below(arena.product(eta[v[0]], eta[v[1]]), eta[v[2]])
    if op == "denial":
        return arena.below(eta[v[0]], arena.bottom())
    raise AssertionError("unknown normalized constructor")


def models(clauses, eta, arena):
    return all(holds(c, eta, arena) for c in clauses)


def from_terms(n, premises, query):
    """Encode small tuple expressions independently, deliberately sharing syntax."""
    rows, table = [], {}
    def enc(t):
        if t in table:
            return table[t]
        if t[0] == "v":
            row = {"op": "var", "var": t[1]}
        elif t[0] == "b":
            row = {"op": "bottom"}
        else:
            row = {"op": "product", "left": enc(t[1]), "right": enc(t[2])}
        i = len(rows)
        rows.append(row)
        table[t] = i
        return i
    ps = [[enc(l), enc(r)] for l, r in premises]
    qs = [enc(query[0]), enc(query[1])]
    return Input.from_dict(dict(variables=n, nodes=rows, premises=ps, query=qs))


def structural_check(problem, out, counts):
    roots = [r for pair in problem.premises for r in pair] + list(problem.query)
    todo, p, bot = list(roots), 0, False
    while todo:
        node = problem.nodes[todo.pop()]
        if node.op == "bottom":
            bot = True
        elif node.op == "product":
            p += 1
            todo.extend((node.left, node.right))
    assert out.extra == p+int(bot)
    assert len(out.bindings) == out.extra
    assert len(out.definitions) == 2*p+int(bot)
    assert len(out.premises) == len(problem.premises)
    assert len(out.constraints) == len(problem.premises)+2*p+int(bot)
    assert [b.index for b in out.bindings] == list(range(problem.variables, out.variables))
    assert [b.index for b in out.bindings if b.op == "bottom"] == (
        [problem.variables] if bot else [])
    reconstructed = []
    for binding in out.bindings:
        if binding.op == "bottom":
            reconstructed.append(("denial", binding.index))
        else:
            assert 0 <= binding.left < binding.index
            assert 0 <= binding.right < binding.index
            assert problem.nodes[binding.source_node].op == "product"
            reconstructed.extend((("upper", binding.index, binding.left, binding.right),
                                  ("lower", binding.left, binding.right, binding.index)))
    assert tuple(reconstructed) == out.definitions
    for clause in out.constraints:
        assert len(clause) == {"leq": 3, "upper": 4, "lower": 4, "denial": 2}[clause[0]]
        assert all(type(i) is int and 0 <= i < out.variables for i in clause[1:])
    for node, q in zip(problem.query, out.query):
        if problem.nodes[node].op == "var":
            assert q == problem.nodes[node].var
    assert out.to_dict() == normalize(Input.from_dict(problem.to_dict())).to_dict()
    counts["structural_systems"] += 1


def expected_extension(problem, out, rho, arena):
    vals = original_eval(problem, rho, arena)
    # Each allocated occurrence has independently evaluated original syntax.
    return tuple(rho) + tuple(arena.bottom() if b.op == "bottom" else vals[b.source_node]
                              for b in out.bindings)


def extension_check(problem, out, rho, arena, counts, words=False):
    eta = extend(out, rho, arena)
    assert restrict(out, eta) == tuple(rho)
    expected = expected_extension(problem, out, rho, arena)
    assert all(arena.equal(a, b) for a, b in zip(eta, expected))
    assert models(out.definitions, eta, arena)
    assert models(out.constraints, eta, arena) == original_models(problem, rho, arena)
    ev = original_eval(problem, rho, arena)
    for node, q in zip(problem.query, out.query):
        assert arena.equal(ev[node], eta[q])
    assert arena.below(ev[problem.query[0]], ev[problem.query[1]]) == arena.below(
        eta[out.query[0]], eta[out.query[1]])
    counts["original_valuation_extensions"] += 1
    if words:
        for length in range(5):
            for word in product((0, 1), repeat=length):
                original = (arena.has(ev[problem.query[0]], word)
                            and not arena.has(ev[problem.query[1]], word))
                normalized = (arena.has(eta[out.query[0]], word)
                              and not arena.has(eta[out.query[1]], word))
                assert original == normalized
                counts["fixed_address_comparisons"] += 1
    return eta


def arbitrary_valuation_check(problem, out, eta, arena, counts):
    rho = tuple(eta[:problem.variables])
    expected = expected_extension(problem, out, rho, arena)
    exact = all(arena.equal(a, b) for a, b in zip(eta, expected))
    d = models(out.definitions, eta, arena)
    assert d == exact  # Uniqueness of extension, not just equisatisfiability.
    assert models(out.constraints, eta, arena) == (exact and original_models(problem, rho, arena))
    if d:
        ev = original_eval(problem, rho, arena)
        for node, q in zip(problem.query, out.query):
            assert arena.equal(eta[q], ev[node])
        counts["definition_models_among_checked_valuations"] += 1
    counts["arbitrary_normalized_valuations"] += 1


def run():
    counts = Counter()
    arena = Arena()
    b = arena.bottom()
    unit = arena.product(b, b)
    left = arena.product(unit, b)
    right = arena.product(b, unit)
    both = arena.product(unit, unit)
    zero = arena.graph([(0, 1), None])
    omega = arena.graph([(0, 0)])
    values = (b, unit, left, right, both, zero, omega)
    small_values = (b, unit, zero, omega)
    assert arena.equal(arena.product(zero, b), zero)
    assert arena.equal(arena.product(omega, omega), omega)
    assert not arena.below(zero, unit)
    assert arena.separator(zero, unit) == (0,)
    assert arena.separator(unit, b) == ()
    assert arena.separator(zero, omega) is None

    # All shallow expression pairs and all zero/one-premise systems on them.
    for n in (0, 1):
        leaves = [("b",)] + [("v", i) for i in range(n)]
        terms = leaves + [("p", x, y) for x in leaves for y in leaves]
        pairs = list(product(terms, repeat=2))
        premise_sets = [()] + [(p,) for p in pairs]
        for premises in premise_sets:
            for query in pairs:
                counts["exhaustive_input_systems"] += 1
                inp = from_terms(n, premises, query)
                out = normalize(inp)
                structural_check(inp, out, counts)
                for rho in product(values, repeat=n):
                    extension_check(inp, out, rho, arena, counts)
                # All valuations in the stated four-value domain when at most
                # four output variables. This is a test scope, not a NO bound.
                if out.variables <= 4:
                    counts["exhaustive_normalized_systems"] += 1
                    for eta in product(small_values, repeat=out.variables):
                        counts["exhaustive_normalized_valuations"] += 1
                        arbitrary_valuation_check(inp, out, eta, arena, counts)

    rng = random.Random(SEED)
    for case in range(250):
        n = rng.randrange(4)
        rows = [{"op": "bottom"}] + [{"op": "var", "var": i} for i in range(n)]
        for _ in range(rng.randrange(1, 9)):
            rows.append({"op": "product", "left": rng.randrange(len(rows)),
                         "right": rng.randrange(len(rows))})
        premises = [[rng.randrange(len(rows)), rng.randrange(len(rows))]
                    for _ in range(rng.randrange(4))]
        query = [rng.randrange(len(rows)), rng.randrange(len(rows))]
        inp = Input.from_dict(dict(variables=n, nodes=rows, premises=premises, query=query))
        out = normalize(inp)
        structural_check(inp, out, counts)
        # Additional genuinely cyclic regular values, not just finite trees.
        size = rng.randrange(2, 7)
        graph = [None if rng.randrange(4) == 0 else
                 (rng.randrange(size), rng.randrange(size)) for _ in range(size)]
        random_tree = arena.graph(graph)
        pool = values+(random_tree,)
        for _ in range(5):
            rho = tuple(rng.choice(pool) for _ in range(n))
            eta = extension_check(inp, out, rho, arena, counts, words=True)
            arbitrary_valuation_check(inp, out, eta, arena, counts)
            if out.extra:
                counts["seeded_fresh_mutations"] += 1
                mutated = list(eta)
                mutated[rng.randrange(n, out.variables)] = rng.choice(pool)
                arbitrary_valuation_check(inp, out, tuple(mutated), arena, counts)
        counts["seeded_systems"] += 1

    # Regression groups from the released advisory, plus zero/deep/DAG inputs.
    v, bot = ("v", 0), ("b",)
    pp = ("p", bot, bot)
    nested = ("p", ("p", v, bot), ("p", v, bot))
    inp = from_terms(2, [(nested, ("v", 1))], (v, ("v", 1)))
    out = normalize(inp)
    assert (out.extra, len(out.constraints)) == (4, 8)
    extension_check(inp, out, (zero, omega), arena, counts, words=True)
    counts["adversarial_groups"] += 1

    # Missing LOWER definition falsely admits all-bottom on an inconsistent input.
    inp = from_terms(0, [(pp, bot)], (bot, bot))
    out = normalize(inp)
    eta = (b,)*out.variables
    assert not original_models(inp, (), arena)
    assert not models(out.constraints, eta, arena)
    assert models([c for c in out.constraints if c[0] != "lower"], eta, arena)
    counts["adversarial_groups"] += 1

    # Missing UPPER definition admits an oversized proxy and invalid old model.
    inp = from_terms(1, [(v, pp)], (v, bot))
    out = normalize(inp)
    eta = list(extend(out, (left,), arena))
    for binding in out.bindings:
        if binding.op == "product":
            eta[binding.index] = left
    assert not original_models(inp, (left,), arena)
    assert models([c for c in out.constraints if c[0] != "upper"], eta, arena)
    assert not models(out.constraints, eta, arena)
    counts["adversarial_groups"] += 1

    # Query-only old variable and no fresh-name collision: old index 1 is retained.
    inp = from_terms(2, [(bot, v)], (("v", 1), v))
    out = normalize(inp)
    eta = extension_check(inp, out, (b, unit), arena, counts, words=True)
    assert out.query == (1, 0) and out.bindings[0].index == 2
    assert models(out.constraints, eta, arena)
    assert not arena.below(eta[1], eta[0])
    counts["adversarial_groups"] += 1

    # Necessarily infinite recursive constraint, with exact regular model.
    inp = from_terms(1, [(("p", v, bot), v)], (v, bot))
    out = normalize(inp)
    eta = extension_check(inp, out, (zero,), arena, counts, words=True)
    assert models(out.constraints, eta, arena)
    assert arena.separator(eta[out.query[0]], eta[out.query[1]]) == ()
    assert all(arena.has(zero, (0,)*j) for j in range(101))
    counts["adversarial_groups"] += 1

    # Compound query definitions alone do not assume the query.
    inp = from_terms(0, [], (pp, bot))
    out = normalize(inp)
    eta = extension_check(inp, out, (), arena, counts, words=True)
    assert models(out.constraints, eta, arena)
    assert not arena.below(eta[out.query[0]], eta[out.query[1]])
    assert out.premises == ()
    counts["adversarial_groups"] += 1

    # No bottom, no product, repeated old variables, and unused declared variables.
    inp = from_terms(3, [(v, v)], (("v", 2), v))
    out = normalize(inp)
    assert out.extra == 0 and out.definitions == () and out.query == (2, 0)
    extension_check(inp, out, (b, zero, omega), arena, counts, words=True)
    counts["adversarial_groups"] += 1

    # Zero originals is supported for constant queries; repeated DAG nodes expand.
    inp = from_terms(0, [], (bot, bot))
    out = normalize(inp)
    assert (out.variables, out.query, out.extra) == (1, (0, 0), 1)
    inp = Input.from_dict(dict(variables=1, nodes=[{"op": "var", "var": 0},
        {"op": "product", "left": 0, "right": 0},
        {"op": "product", "left": 1, "right": 1}], premises=[], query=[2, 2]))
    out = normalize(inp)
    assert out.extra == 6 and len(out.definitions) == 12
    extension_check(inp, out, (zero,), arena, counts, words=True)
    counts["adversarial_groups"] += 1

    # Dead bottom row must not allocate a proxy; no recursion ceiling.
    inp = Input.from_dict(dict(variables=1, nodes=[{"op": "bottom"}, {"op": "var", "var": 0}],
                              premises=[], query=[1, 1]))
    assert normalize(inp).extra == 0
    depth = 10000
    rows = [{"op": "var", "var": 0}, {"op": "bottom"}]
    for _ in range(depth):
        rows.append({"op": "product", "left": len(rows)-1, "right": 0})
    inp = Input.from_dict(dict(variables=1, nodes=rows, premises=[], query=[len(rows)-1, 0]))
    out = normalize(inp)
    structural_check(inp, out, counts)
    assert out.extra == depth+1 and len(out.constraints) == 2*depth+1
    class SizeAlgebra:
        def bottom(self): return 0
        def product(self, left, right): return 1+left+right
    assert extend(out, (0,), SizeAlgebra())[out.query[0]] == depth
    counts["deep_product_depth"] = depth
    counts["adversarial_groups"] += 1

    good = dict(variables=1, nodes=[{"op": "var", "var": 0}], premises=[], query=[0, 0])
    invalid = [None, {}, dict(good, variables=-1), dict(good, variables=True),
               dict(good, query=[0]), dict(good, query=[0, 1]), dict(good, query=[False, 0]),
               dict(good, nodes=[{"op": "var", "var": 1}]),
               dict(good, nodes=[{"op": "product", "left": 0, "right": 0}]),
               dict(good, nodes=[{"op": "top"}]), dict(good, unexpected=1),
               dict(good, nodes=[{"op": "bottom", "var": 0}]),
               dict(good, premises=[[0, -1]]), dict(good, premises="invalid")]
    for raw in invalid:
        try:
            Input.from_dict(raw)
        except ValueError:
            counts["invalid_inputs_rejected"] += 1
        else:
            raise AssertionError(f"accepted malformed input: {raw!r}")
    # CLI tests use the actual executable, not a reimplementation.
    for sample in (good, from_terms(0, [], (pp, bot)).to_dict(),
                   from_terms(1, [(("p", v, bot), v)], (v, bot)).to_dict()):
        proc = subprocess.run([sys.executable, str(ROOT / "experiments/expression_normalization.py")],
                              input=json.dumps(sample), text=True, capture_output=True, check=True)
        assert json.loads(proc.stdout) == normalize(Input.from_dict(sample)).to_dict()
        counts["cli_roundtrips"] += 1
    proc = subprocess.run([sys.executable, str(ROOT / "experiments/expression_normalization.py")],
                          input=json.dumps(invalid[2]), text=True, capture_output=True)
    assert proc.returncode == 2 and not proc.stdout and "normalization error" in proc.stderr
    counts["cli_invalid_input_checks"] += 1

    return {"status": "PASS", "seed": SEED, "counts": dict(sorted(counts.items())),
            "scope": {"exact_tree_semantics": "finite graph coalgebras, including infinite trees; inclusion by complete product-graph reachability",
                      "exhaustive_syntax": "n=0,1; leaves bottom/variables and one product over leaves; every query and zero/one premise",
                      "original_value_domain": "seven named finite/infinite regular trees",
                      "normalized_value_domain": "all assignments of bottom,unit,zeroSpine,fullTree when output variables <=4",
                      "seeded": "250 finite DAG inputs; five original valuations and fresh-value mutations per input",
                      "fixed_addresses": "all binary words of length <=4 on named/seeded cases",
                      "not_claimed": "not an exhaustive arbitrary-tree theorem, unrestricted decision, or Lean proof"},
            "environment": {"python": platform.python_version(), "platform": platform.system(),
                            "machine": platform.machine()},
            "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in (
                "experiments/expression_normalization.py", "experiments/check_expression_normalization.py")}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
