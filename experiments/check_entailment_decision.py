#!/usr/bin/env python3
"""Independent native regressions for the expression-level entailment Boolean.

The Lean checker is invoked once per fixture.  A bounded process timeout is an
UNKNOWN result; it is never turned into a negative answer.  The expected
answers below come from elementary order laws, explicit finite-tree
countermodels, or the regular zero-spine model, rather than another copy of
the Boolean implementation.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import time
from typing import Optional


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
ENV_SH = Path("/home/marcus/.local/share/subtail/env.sh")
DEFAULT_TIMEOUT = 20.0
RESULT_MARKER = "SUBTAIL_CASE_RESULT:"


@dataclass(frozen=True)
class Expr:
    op: str
    args: tuple[object, ...] = ()


def V(i: int) -> Expr:
    return Expr("var", (i,))


BOT = Expr("bot")


def P(left: Expr, right: Expr) -> Expr:
    return Expr("prod", (left, right))


@dataclass(frozen=True)
class Fixture:
    name: str
    kind: str
    n: int
    expected: bool
    reason: str
    justification: str
    tags: tuple[str, ...]
    premises: tuple[tuple[Expr, Expr], ...] = ()
    left: Optional[Expr] = None
    right: Optional[Expr] = None
    constraints: tuple[tuple[str, tuple[int, ...]], ...] = ()
    a: Optional[int] = None
    b: Optional[int] = None


def frontend(
    name: str,
    n: int,
    premises: tuple[tuple[Expr, Expr], ...],
    left: Expr,
    right: Expr,
    expected: bool,
    reason: str,
    justification: str,
    *tags: str,
) -> Fixture:
    return Fixture(
        name=name,
        kind="frontend",
        n=n,
        expected=expected,
        reason=reason,
        justification=justification,
        tags=tuple(tags),
        premises=premises,
        left=left,
        right=right,
    )


def normalized(
    name: str,
    n: int,
    constraints: tuple[tuple[str, tuple[int, ...]], ...],
    a: int,
    b: int,
    expected: bool,
    reason: str,
    justification: str,
    *tags: str,
) -> Fixture:
    return Fixture(
        name=name,
        kind="normalized",
        n=n,
        expected=expected,
        reason=reason,
        justification=justification,
        tags=tuple(tags),
        constraints=constraints,
        a=a,
        b=b,
    )


def raw(
    name: str,
    n: int,
    constraints: tuple[tuple[str, tuple[int, ...]], ...],
    a: int,
    b: int,
    expected: bool,
    reason: str,
    justification: str,
    *tags: str,
) -> Fixture:
    return Fixture(
        name=name,
        kind="raw",
        n=n,
        expected=expected,
        reason=reason,
        justification=justification,
        tags=tuple(tags),
        constraints=constraints,
        a=a,
        b=b,
    )


LEQ = lambda a, b: ("leq", (a, b))
UPPER = lambda a, l, r: ("upper", (a, l, r))
LOWER = lambda l, r, a: ("lower", (l, r, a))
DENIAL = lambda a: ("denial", (a,))


def corpus() -> list[Fixture]:
    """A small, named corpus whose answers have independent justifications."""
    return [
        frontend(
            "empty-reflexive",
            1,
            (),
            V(0),
            V(0),
            True,
            "reflexivity",
            "Every tree is below itself; no premise is needed.",
            "guard",
        ),
        frontend(
            "empty-variable-cross",
            2,
            (),
            V(0),
            V(1),
            False,
            "root-bottom-countermodel",
            "Set v0 to the root-only tree product(bottom,bottom), v1 to bottom, and use the empty address.",
            "guard",
        ),
        frontend(
            "empty-bottom-left",
            1,
            (),
            BOT,
            V(0),
            True,
            "bottom-left",
            "Bottom has no product nodes, so bottom is below every tree.",
            "guard",
        ),
        frontend(
            "empty-variable-bottom",
            1,
            (),
            V(0),
            BOT,
            False,
            "root-bottom-countermodel",
            "Set v0 to the root-only tree product(bottom,bottom); it has the empty node and bottom does not.",
            "guard",
        ),
        frontend(
            "empty-product-left",
            1,
            (),
            P(V(0), BOT),
            V(0),
            False,
            "product-child-countermodel",
            "Set v0 to the root-only tree. product(v0,bottom) has the false-left child while v0 does not.",
        ),
        frontend(
            "premise-forward",
            2,
            ((V(0), V(1)),),
            V(0),
            V(1),
            True,
            "premise",
            "The queried inequality is exactly the listed premise.",
            "guard",
        ),
        frontend(
            "premise-reverse",
            2,
            ((V(0), V(1)),),
            V(1),
            V(0),
            False,
            "premise-reverse-countermodel",
            "Set v0 to bottom and v1 to the root-only tree. The premise holds, but v1 is not below v0 at the empty address.",
            "guard",
        ),
        frontend(
            "transitive-query-not-premise",
            3,
            ((V(0), V(1)), (V(1), V(2))),
            V(0),
            V(2),
            True,
            "transitivity",
            "Both listed premises compose by transitivity; the queried pair is not itself a premise.",
        ),
        frontend(
            "product-monotone",
            2,
            ((V(0), V(1)),),
            P(V(0), BOT),
            P(V(1), BOT),
            True,
            "product-monotonicity",
            "Product is covariant in both arguments, and bottom is below itself; apply product_mono to the premise.",
        ),
        frontend(
            "product-monotone-reverse",
            2,
            ((V(0), V(1)),),
            P(V(1), BOT),
            P(V(0), BOT),
            False,
            "product-reverse-countermodel",
            "Set v0 to bottom and v1 to the root-only tree. The premise holds, while the queried products differ at the left child.",
        ),
        frontend(
            "query-only-source",
            3,
            ((V(0), V(1)),),
            V(2),
            V(0),
            False,
            "query-only-variable-countermodel",
            "The query-only v2 is root-only, v0 is bottom, and v1 is root-only; the premise holds but the query fails at the empty address.",
        ),
        frontend(
            "query-only-target",
            3,
            ((V(0), V(1)),),
            V(0),
            V(2),
            False,
            "query-only-variable-countermodel",
            "Set v0 and v1 to the root-only tree and query-only v2 to bottom; the premise holds but the query fails at the empty address.",
        ),
        frontend(
            "zero-vars-empty-reflexive",
            0,
            (),
            BOT,
            BOT,
            True,
            "reflexivity",
            "With zero original variables, bottom is still below itself.",
            "guard",
        ),
        frontend(
            "zero-vars-product-bottom",
            0,
            (),
            P(BOT, BOT),
            BOT,
            False,
            "product-root-countermodel",
            "The product has its root node by definition while bottom has no nodes; there are no valuations to restrict this result.",
        ),
        frontend(
            "unsat-zero-variable-query",
            0,
            ((P(BOT, BOT), BOT),),
            BOT,
            BOT,
            True,
            "unsatisfiable-premises",
            "The only premise is impossible because product(bottom,bottom) contains its root and bottom does not; entailment is vacuous.",
            "guard",
        ),
        frontend(
            "unsat-query-variable",
            1,
            ((P(BOT, BOT), BOT),),
            V(0),
            BOT,
            True,
            "unsatisfiable-premises",
            "The same variable-free impossible premise has no model, so the unrelated query v0 <= bottom is vacuously entailed.",
            "guard",
        ),
        frontend(
            "bottom-premise-reverse",
            1,
            ((BOT, V(0)),),
            V(0),
            BOT,
            False,
            "root-bottom-countermodel",
            "Set v0 to the root-only tree. bottom <= v0 holds, but v0 <= bottom fails at the empty address.",
        ),
        frontend(
            "bottom-to-product",
            1,
            (),
            BOT,
            P(V(0), BOT),
            True,
            "bottom-left",
            "Bottom is below every product tree, independently of v0.",
        ),
        frontend(
            "duplicate-product-reflexive",
            2,
            ((P(V(0), V(1)), P(V(0), V(1))),),
            P(V(0), V(1)),
            P(V(0), V(1)),
            True,
            "duplicate-reflexivity",
            "The same product occurs on both sides of a premise and in the query; reflexivity is independent of slot allocation.",
        ),
        frontend(
            "duplicate-product-reverse",
            3,
            ((P(V(0), V(1)), V(2)),),
            V(2),
            P(V(0), V(1)),
            False,
            "duplicate-product-countermodel",
            "Set v0=bottom, v1=bottom, and v2 to product(root-only,bottom). The premise holds at every address, but v2 has a false-left child absent from product(v0,v1).",
        ),
        frontend(
            "nested-duplicate-reflexive",
            2,
            (),
            P(P(V(0), V(1)), P(V(0), V(1))),
            P(P(V(0), V(1)), P(V(0), V(1))),
            True,
            "duplicate-reflexivity",
            "A nested product expression is repeated exactly; reflexivity remains valid with duplicate product occurrences.",
        ),
        frontend(
            "duplicate-product-derived",
            2,
            ((V(0), V(1)),),
            P(V(0), V(0)),
            P(V(1), V(1)),
            True,
            "product-monotonicity",
            "Apply the premise twice and product covariance; the duplicated variable children are intentional.",
        ),
        frontend(
            "necessarily-infinite-zero-spine",
            1,
            ((P(V(0), BOT), V(0)),),
            V(0),
            BOT,
            False,
            "regular-infinite-countermodel",
            "The regular zeroSpine tree satisfies product(zeroSpine,bottom) <= zeroSpine and has the empty node, so it refutes zeroSpine <= bottom. The premise also forces arbitrarily long false spines in every model.",
            "infinite",
        ),
        frontend(
            "necessarily-infinite-premise",
            1,
            ((P(V(0), BOT), V(0)),),
            P(V(0), BOT),
            V(0),
            True,
            "premise",
            "The queried inequality is the premise, even though its models include the regular infinite zeroSpine model.",
            "infinite",
        ),
        frontend(
            "query-not-premise-reverse-product",
            3,
            ((P(V(0), V(1)), V(2)),),
            V(2),
            P(V(0), V(1)),
            False,
            "duplicate-product-countermodel",
            "This repeats the product from the premise in the reversed query; the explicit root-plus-left-child v2 countermodel separates the directions.",
        ),
        frontend(
            "empty-product-swap",
            2,
            (),
            P(V(0), V(1)),
            P(V(1), V(0)),
            False,
            "product-swap-countermodel",
            "Set v0 to root-only and v1 to bottom. The two products disagree at the first child address.",
        ),
        raw(
            "raw-empty-cross",
            2,
            (),
            0,
            1,
            False,
            "root-bottom-countermodel",
            "The normalized variable instance has the root-only/bottom countermodel at the empty address.",
            "backend",
        ),
        raw(
            "raw-premise-forward",
            2,
            (LEQ(0, 1),),
            0,
            1,
            True,
            "premise",
            "The variable inequality is explicitly present in the normalized premise list.",
            "backend",
        ),
        raw(
            "raw-premise-reverse",
            2,
            (LEQ(0, 1),),
            1,
            0,
            False,
            "premise-reverse-countermodel",
            "The root-only/bottom valuation satisfies 0 <= 1 but refutes 1 <= 0 at the empty address.",
            "backend",
        ),
        raw(
            "raw-reflexive",
            1,
            (),
            0,
            0,
            True,
            "reflexivity",
            "The raw two-branch backend must preserve reflexivity without a frontend guard.",
            "backend",
        ),
        raw(
            "raw-unsat-denial-lower",
            1,
            (DENIAL(0), LOWER(0, 0, 0)),
            0,
            0,
            True,
            "reflexivity-under-unsat",
            "Denial forces v0 below bottom, while lower requires product(v0,v0) below v0; these conflict at the product root, but reflexivity remains true.",
            "backend",
        ),
        raw(
            "raw-equality-both-directions",
            2,
            (LEQ(0, 1), LEQ(1, 0)),
            1,
            0,
            True,
            "two-premise-equality",
            "The two listed inequalities establish both directions; query the reverse one without a frontend guard.",
            "backend",
        ),
        raw(
            "raw-upper-only",
            2,
            (UPPER(0, 1, 1),),
            0,
            1,
            False,
            "upper-countermodel",
            "Take v1=root-only and v0=product(v1,v1). The upper premise holds by equality, but v0 has a child absent from v1.",
            "backend",
        ),
        normalized(
            "normalized-empty-cross",
            2,
            (),
            0,
            1,
            False,
            "root-bottom-countermodel",
            "The normalized fast path sees a root-only/bottom countermodel at the empty address.",
            "backend",
        ),
        normalized(
            "normalized-premise-forward",
            2,
            (LEQ(0, 1),),
            0,
            1,
            True,
            "premise",
            "The queried normalized leq clause is explicitly present.",
            "backend",
        ),
        normalized(
            "normalized-premise-reverse",
            2,
            (LEQ(0, 1),),
            1,
            0,
            False,
            "premise-reverse-countermodel",
            "A root-only/bottom valuation satisfies the premise and refutes the reversed query.",
            "backend",
        ),
        normalized(
            "normalized-reflexive",
            1,
            (),
            0,
            0,
            True,
            "reflexivity",
            "This calls the guarded normalized entry point directly, so its reflexivity guard returns true.",
            "backend",
        ),
        normalized(
            "normalized-unsat-denial-lower",
            1,
            (DENIAL(0), LOWER(0, 0, 0)),
            0,
            0,
            True,
            "reflexivity-under-unsat",
            "The normalized constraints are contradictory at the product root; reflexivity remains valid.",
            "backend",
        ),
    ]


def fin(i: int, n: int) -> str:
    return f"(⟨{i}, by decide⟩ : Fin {n})"


def render_expr(expr: Expr, n: int) -> str:
    if expr.op == "var":
        return f"(Subtail.ExpressionNormalization.Expr.var {fin(int(expr.args[0]), n)})"
    if expr.op == "bot":
        return "Subtail.ExpressionNormalization.Expr.bot"
    if expr.op == "prod":
        return (
            "(Subtail.ExpressionNormalization.Expr.prod "
            f"{render_expr(expr.args[0], n)} {render_expr(expr.args[1], n)})"
        )
    raise ValueError(f"unknown expression operator: {expr.op}")


def render_input(fixture: Fixture) -> str:
    rows = [
        f"({render_expr(left, fixture.n)}, {render_expr(right, fixture.n)})"
        for left, right in fixture.premises
    ]
    return f"([{', '.join(rows)}] : Subtail.ExpressionNormalization.Input {fixture.n})"


def render_constraint(item: tuple[str, tuple[int, ...]], n: int) -> str:
    kind, args = item
    fs = [fin(i, n) for i in args]
    if kind == "leq":
        return f"(.leq {fs[0]} {fs[1]})"
    if kind == "upper":
        return f"(.upper {fs[0]} {fs[1]} {fs[2]})"
    if kind == "lower":
        return f"(.lower {fs[0]} {fs[1]} {fs[2]})"
    if kind == "denial":
        return f"(.denial {fs[0]})"
    raise ValueError(f"unknown constraint kind: {kind}")


def render_constraints(fixture: Fixture) -> str:
    rows = [render_constraint(item, fixture.n) for item in fixture.constraints]
    return f"([{', '.join(rows)}] : List (Subtail.TreeSemantics.Constraint {fixture.n}))"


def lean_source(fixture: Fixture) -> str:
    if fixture.kind == "frontend":
        call = (
            "Subtail.EntailmentDecision.entailsCheck "
            f"{render_input(fixture)} {render_expr(fixture.left, fixture.n)} "
            f"{render_expr(fixture.right, fixture.n)}"
        )
    else:
        function = (
            "Subtail.EntailmentDecision.rawNormalizedEntailsCheck"
            if fixture.kind == "raw"
            else "Subtail.EntailmentDecision.normalizedEntailsCheck"
        )
        call = (
            f"{function} {render_constraints(fixture)} "
            f"{fin(int(fixture.a), fixture.n)} {fin(int(fixture.b), fixture.n)}"
        )
    return f'''import Subtail.EntailmentDecision

def main : IO Unit := do
  let actual : Bool := {call}
  IO.println ("{RESULT_MARKER}" ++ (if actual then "true" else "false"))

#eval main
'''


def validate_corpus(fixtures: list[Fixture]) -> None:
    names: set[str] = set()
    for fixture in fixtures:
        if fixture.name in names:
            raise AssertionError(f"duplicate fixture name: {fixture.name}")
        names.add(fixture.name)
        if fixture.kind == "frontend":
            assert fixture.left is not None and fixture.right is not None
            for expression in (fixture.left, fixture.right):
                validate_expr(expression, fixture.n)
            for left, right in fixture.premises:
                validate_expr(left, fixture.n)
                validate_expr(right, fixture.n)
        else:
            assert fixture.a is not None and fixture.b is not None
            assert 0 < fixture.n
            assert 0 <= fixture.a < fixture.n and 0 <= fixture.b < fixture.n
            for _, args in fixture.constraints:
                assert all(0 <= i < fixture.n for i in args)
        if fixture.reason in {
            "reflexivity",
            "reflexivity-under-unsat",
            "bottom-left",
            "premise",
            "transitivity",
            "product-monotonicity",
            "duplicate-reflexivity",
            "two-premise-equality",
            "unsatisfiable-premises",
        }:
            assert fixture.expected, fixture.name
        if fixture.reason in {
            "root-bottom-countermodel",
            "product-child-countermodel",
            "premise-reverse-countermodel",
            "product-reverse-countermodel",
            "query-only-variable-countermodel",
            "product-root-countermodel",
            "duplicate-product-countermodel",
            "regular-infinite-countermodel",
            "upper-countermodel",
            "product-swap-countermodel",
        }:
            assert not fixture.expected, fixture.name


def validate_expr(expr: Expr, n: int) -> None:
    if expr.op == "var":
        assert 0 <= int(expr.args[0]) < n
    elif expr.op == "bot":
        return
    elif expr.op == "prod":
        validate_expr(expr.args[0], n)
        validate_expr(expr.args[1], n)
    else:
        raise AssertionError(f"unknown expression operator: {expr.op}")


def source_hashes() -> dict[str, str]:
    paths = [
        "experiments/check_entailment_decision.py",
        "lean/Subtail/EntailmentDecision.lean",
        "lean/Subtail/ExpressionNormalization.lean",
        "lean/Subtail/TreeSemantics.lean",
        "lean/Subtail/SummaryAutomaton.lean",
        "lean/Subtail/SubtypeTerminalBridge.lean",
        "lean/Subtail/AbsorbingTerminal.lean",
        "lean/Subtail/InfiniteDecision.lean",
        "lean/Subtail/RankQueryDecision.lean",
    ]
    return {
        path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in paths
        if (ROOT / path).is_file()
    }


def git_revision() -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, capture_output=True, check=True
    )
    return proc.stdout.strip()


def run_lean(source: str, path: Path, timeout: float) -> dict[str, object]:
    path = path.resolve()
    path.write_text(source)
    if ENV_SH.is_file():
        quoted = shlex.quote(str(path))
        command = ["zsh", "-lc", f"source {shlex.quote(str(ENV_SH))} && exec lake env lean {quoted}"]
    else:
        command = ["lake", "env", "lean", str(path)]
    started = time.monotonic()
    proc = subprocess.Popen(
        command, cwd=LEAN_ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        # Killing only lake can leave its Lean child consuming resources.
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
        return {
            "status": "UNKNOWN",
            "seconds": round(time.monotonic() - started, 3),
            "timeout_seconds": timeout,
            "stdout": stdout[-2000:],
            "stderr": stderr[-2000:],
        }
    proc.stdout, proc.stderr = stdout, stderr
    output = proc.stdout + proc.stderr
    marker = [line.strip() for line in output.splitlines() if line.startswith(RESULT_MARKER)]
    if proc.returncode != 0:
        return {
            "status": "NOT RUN",
            "seconds": round(time.monotonic() - started, 3),
            "returncode": proc.returncode,
            "stdout": proc.stdout[-2000:],
            "stderr": proc.stderr[-4000:],
        }
    if not marker or marker[-1] not in (RESULT_MARKER + "true", RESULT_MARKER + "false"):
        return {
            "status": "NOT RUN",
            "seconds": round(time.monotonic() - started, 3),
            "returncode": proc.returncode,
            "stdout": proc.stdout[-2000:],
            "stderr": "Missing result marker",
        }
    return {
        "status": "PASS",
        "actual": marker[-1][len(RESULT_MARKER) :] == "true",
        "seconds": round(time.monotonic() - started, 3),
        "returncode": proc.returncode,
    }


SMOKE_NAMES = {
    "empty-reflexive", "empty-variable-cross", "empty-variable-bottom",
    "empty-product-left", "premise-forward", "premise-reverse",
    "query-only-source", "query-only-target", "zero-vars-empty-reflexive",
    "zero-vars-product-bottom", "unsat-zero-variable-query", "unsat-query-variable",
    "bottom-premise-reverse", "duplicate-product-reflexive",
    "nested-duplicate-reflexive", "necessarily-infinite-zero-spine",
    "necessarily-infinite-premise",
}


def selected(fixtures: list[Fixture], phase: str) -> list[Fixture]:
    if phase == "all":
        return fixtures
    if phase == "smoke":
        assert SMOKE_NAMES <= {fixture.name for fixture in fixtures}
        return [fixture for fixture in fixtures if fixture.name in SMOKE_NAMES]
    if phase == "guards":
        return [fixture for fixture in fixtures if "guard" in fixture.tags]
    if phase == "backend":
        return [fixture for fixture in fixtures if "guard" not in fixture.tags]
    raise ValueError(phase)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase", choices=("all", "guards", "backend", "smoke"), default="all")
    parser.add_argument("--strict", action="store_true", help="Require all selected native cases to complete and agree")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    parser.add_argument("--output", type=Path, default=ROOT / "results/entailment-decision.json")
    parser.add_argument("--scratch", type=Path, default=ROOT / "tmp/entailment-decision-checks")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    all_fixtures = corpus()
    validate_corpus(all_fixtures)
    fixtures = selected(all_fixtures, args.phase)
    required = ROOT / "lean/Subtail/EntailmentDecision.lean"
    rows: list[dict[str, object]] = []
    if not required.is_file():
        rows = [
            {
                "name": fixture.name,
                "kind": fixture.kind,
                "expected": fixture.expected,
                "status": "NOT RUN",
                "reason": "required parent module is absent",
            }
            for fixture in fixtures
        ]
    else:
        args.scratch.mkdir(parents=True, exist_ok=True)
        for index, fixture in enumerate(fixtures):
            result = run_lean(
                lean_source(fixture),
                args.scratch / f"{index:03d}-{fixture.name}.lean",
                args.timeout,
            )
            row = {
                "name": fixture.name,
                "kind": fixture.kind,
                "expected": fixture.expected,
                "reason": fixture.reason,
                "justification": fixture.justification,
                "tags": list(fixture.tags),
                **result,
            }
            if result.get("status") == "PASS" and result.get("actual") != fixture.expected:
                row["status"] = "FAIL"
                row["error"] = f"expected {fixture.expected}, got {result.get('actual')}"
            rows.append(row)
            print(f"{fixture.name}: {row['status']}", flush=True)

    statuses = {str(row["status"]) for row in rows}
    if "FAIL" in statuses:
        overall = "FAIL"
    elif "NOT RUN" in statuses:
        overall = "NOT RUN"
    elif "UNKNOWN" in statuses:
        overall = "UNKNOWN"
    else:
        overall = "PASS"
    corpus_descriptor = [
        {
            "name": fixture.name,
            "kind": fixture.kind,
            "n": fixture.n,
            "expected": fixture.expected,
            "reason": fixture.reason,
            "tags": fixture.tags,
        }
        for fixture in fixtures
    ]
    result = {
        "status": overall,
        "phase": args.phase,
        "cases": len(fixtures),
        "pass": sum(row["status"] == "PASS" for row in rows),
        "unknown": sum(row["status"] == "UNKNOWN" for row in rows),
        "not_run": sum(row["status"] == "NOT RUN" for row in rows),
        "fail": sum(row["status"] == "FAIL" for row in rows),
        "limits": {
            "per_fixture_timeout_seconds": args.timeout,
            "execution": "one fresh Lean process group per fixture, sequentially; entire group killed and reaped on timeout",
            "timeout_boundary": "UNKNOWN, never a negative answer",
            "compile_error_boundary": "NOT RUN and nonzero checker exit; overall NOT RUN unless a mismatch is observed",
        },
        "coverage": {
            "frontend": sum(fixture.kind == "frontend" for fixture in fixtures),
            "completed_by_entrypoint": {kind: sum(row["kind"] == kind and row["status"] == "PASS" for row in rows) for kind in ("frontend", "raw", "normalized")},
            "path_boundary": "Entry points are observed; successful guarded calls do not certify raw branch execution. Only kind=raw directly invokes the two-branch backend. Tags identify fixture groups, not a runtime trace.",
            "raw_normalized_backend": sum(fixture.kind == "raw" for fixture in fixtures),
            "normalized_guarded_backend": sum(fixture.kind == "normalized" for fixture in fixtures),
            "categories": sorted({tag for fixture in fixtures for tag in fixture.tags}),
            "independent_answers": "Elementary order laws, explicit root/child finite-tree countermodels, and regular zeroSpine witness; no second Boolean implementation.",
        },
        "source_revision": git_revision(),
        "source_sha256": source_hashes(),
        "corpus_sha256": hashlib.sha256(
            json.dumps(corpus_descriptor, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": overall,
                "phase": args.phase,
                "cases": len(fixtures),
                "pass": result["pass"],
                "unknown": result["unknown"],
                "not_run": result["not_run"],
                "fail": result["fail"],
                "output": str(args.output),
            },
            sort_keys=True,
        )
    )
    return 1 if overall in ("FAIL", "NOT RUN") or (args.strict and overall != "PASS") else 0


if __name__ == "__main__":
    raise SystemExit(main())
