#!/usr/bin/env python3
"""Capped validation for the cached finite-summary and positive frontend layers.

This harness is deliberately separate from the implementation and its proof
audit.  It compares the cached component API with the independent
``check_stack_summary.py`` P-automaton oracle, then runs the matched E054
corpus.  The raw backend is always the existing
``TerminalDecisionLazy.rawNormalizedEntailsCheckLazy`` call.  A timeout or
resource failure is UNKNOWN; a completed disagreement or compiler error is a
failure.

The parent worktree supplies the Fast modules.  This file owns no result
ledger, workflow, source import, or implementation path.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import itertools
import json
import platform
from pathlib import Path
import random
import subprocess
import sys
from typing import Iterable, Optional


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
EXPERIMENT_ROOT = ROOT / "experiments"
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(EXPERIMENT_ROOT))

from subtail import run_process  # noqa: E402
import check_entailment_decision as decision  # noqa: E402
import check_stack_summary as stack_oracle  # noqa: E402


SEED = 2026092020
COMPONENT_MARKER = "SUBTAIL_FAST_COMPONENT:"
BENCHMARK_MARKER = "SUBTAIL_FAST_BENCHMARK:"
GENERATED_MARKER = "SUBTAIL_FAST_GENERATED:"
RESOURCE_WORDS = (
    "memory",
    "out of memory",
    "heartbeat",
    "stack overflow",
    "resource",
    "killed",
    "interrupted",
    "maximum resident",
)

COMPONENT_KINDS = ("forward", "backward", "paths", "reaches", "control")
DIGEST1_MOD = 18446744073709551557
DIGEST2_MOD = 2147483629
DIGEST1_BASE = 1000003
DIGEST2_BASE = 1000033


@dataclass(frozen=True)
class GeneratedCase:
    name: str
    kind: str
    n: int
    constraints: tuple[tuple, ...]
    a: int
    b: int
    word: tuple[int, ...] = ()
    expected: bool = True
    justification: str = ""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes() -> dict[str, str]:
    """Hash every source that a generated probe can import or use.

    Missing Fast modules are recorded explicitly so a name-only match cannot
    be mistaken for source identity while the implementation is being
    integrated.
    """

    relative = [
        "scripts/subtail.py",
        "experiments/check_fast_summary.py",
        "experiments/check_entailment_decision.py",
        "experiments/check_entailment_lazy.py",
        "experiments/check_stack_summary.py",
        "lean/Subtail/StackSummary.lean",
        "lean/Subtail/StackReachability.lean",
        "lean/Subtail/CanonicalReachability.lean",
        "lean/Subtail/SummaryAutomaton.lean",
        "lean/Subtail/EntailmentDecision.lean",
        "lean/Subtail/TerminalDecisionLazy.lean",
        "lean/Subtail/FiniteSearch.lean",
        "lean/Subtail/StackSummaryFast.lean",
        "lean/Subtail/CanonicalReachabilityFast.lean",
        "lean/Subtail/EntailmentFast.lean",
    ]
    result: dict[str, str] = {}
    for name in relative:
        path = ROOT / name
        result[name] = sha256(path) if path.is_file() else "MISSING"
    return result


def git_revision() -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return proc.stdout.strip()


def fast_modules_ready() -> tuple[bool, list[str]]:
    required = [
        "lean/Subtail/StackSummaryFast.lean",
        "lean/Subtail/CanonicalReachabilityFast.lean",
        "lean/Subtail/EntailmentFast.lean",
    ]
    missing = [name for name in required if not (ROOT / name).is_file()]
    return not missing, missing


def render_fin(i: int, n: int) -> str:
    return f"(⟨{i}, by decide⟩ : Fin {n})"


def render_word(word: Iterable[int]) -> str:
    return "[" + ", ".join("true" if bit else "false" for bit in word) + "]"


def render_constraint(constraint: tuple, n: int) -> str:
    kind, *args = constraint
    if kind == "leq":
        return f".leq {render_fin(args[0], n)} {render_fin(args[1], n)}"
    if kind == "upper":
        return (
            f".upper {render_fin(args[0], n)} {render_fin(args[1], n)} "
            f"{render_fin(args[2], n)}"
        )
    if kind == "lower":
        return (
            f".lower {render_fin(args[0], n)} {render_fin(args[1], n)} "
            f"{render_fin(args[2], n)}"
        )
    if kind == "denial":
        return f".denial {render_fin(args[0], n)}"
    raise ValueError(f"unknown constraint: {constraint!r}")


def render_constraints(constraints: Iterable[tuple], n: int) -> str:
    rows = ", ".join(render_constraint(c, n) for c in constraints)
    return f"([{rows}] : List (Subtail.TreeSemantics.Constraint {n}))"


def render_system(system: stack_oracle.System) -> str:
    eps = "[" + ", ".join(f"({p}, {q})" for p, q in sorted(system.eps)) + "]"

    def triples(edges: Iterable[tuple[int, int, int]]) -> str:
        rows = []
        for a, p, q in sorted(edges):
            letter = "true" if a else "false"
            rows.append(f"({letter}, {p}, {q})")
        return "[" + ", ".join(rows) + "]"

    return (
        "{ eps := fun p q => decide ((p.val, q.val) ∈ "
        + eps
        + "), push := fun a p q => decide ((a, p.val, q.val) ∈ "
        + triples(system.push)
        + "), pop := fun a p q => decide ((a, p.val, q.val) ∈ "
        + triples(system.pop)
        + ") }"
    )


def reverse_system(system: stack_oracle.System) -> stack_oracle.System:
    return stack_oracle.System(
        system.n,
        frozenset((q, p) for p, q in system.eps),
        frozenset((a, q, p) for a, p, q in system.pop),
        frozenset((a, q, p) for a, p, q in system.push),
    )


def component_systems() -> list[tuple[str, stack_oracle.System]]:
    """Small deterministic systems covering empty, epsilon, push/pop, dense and reverse cases."""

    systems: list[tuple[str, stack_oracle.System]] = []
    for mask in range(32):
        bits = [(mask >> i) & 1 for i in range(5)]
        systems.append(
            (
                f"one-state-{mask:02d}",
                stack_oracle.System(
                    1,
                    frozenset({(0, 0)} if bits[0] else ()),
                    frozenset((a, 0, 0) for a in (0, 1) if bits[1 + a]),
                    frozenset((a, 0, 0) for a in (0, 1) if bits[3 + a]),
                ),
            )
        )

    named = [
        (
            "empty-two",
            stack_oracle.System(2, frozenset(), frozenset(), frozenset()),
        ),
        (
            "epsilon-two",
            stack_oracle.System(2, frozenset({(0, 1)}), frozenset(), frozenset()),
        ),
        (
            "push-pop-zero",
            stack_oracle.System(
                2,
                frozenset(),
                frozenset({(0, 0, 1)}),
                frozenset({(0, 1, 0)}),
            ),
        ),
        (
            "reverse-labelled",
            stack_oracle.System(
                2,
                frozenset({(1, 0)}),
                frozenset({(0, 0, 1), (1, 1, 0)}),
                frozenset({(0, 1, 0), (1, 0, 1)}),
            ),
        ),
        (
            "dense-two",
            stack_oracle.System(
                2,
                frozenset(itertools.product(range(2), repeat=2)),
                frozenset((a, p, q) for a in (0, 1) for p in range(2) for q in range(2)),
                frozenset((a, p, q) for a in (0, 1) for p in range(2) for q in range(2)),
            ),
        ),
    ]
    systems.extend(named)

    rng = random.Random(SEED)
    for mode in ("mixed", "no_push", "no_pop"):
        for index in range(8):
            eps = frozenset(
                (p, q)
                for p in range(2)
                for q in range(2)
                if rng.random() < 0.25
            )
            push = frozenset(
                (a, p, q)
                for a in (0, 1)
                for p in range(2)
                for q in range(2)
                if mode != "no_push" and rng.random() < 0.25
            )
            pop = frozenset(
                (a, p, q)
                for a in (0, 1)
                for p in range(2)
                for q in range(2)
                if mode != "no_pop" and rng.random() < 0.25
            )
            systems.append((f"{mode}-two-{index}", stack_oracle.System(2, eps, push, pop)))
    return systems


def component_words(n: int) -> list[stack_oracle.Word]:
    return stack_oracle.words(3 if n == 1 else 2)


def component_expected(system: stack_oracle.System) -> dict[str, dict[str, object]]:
    words = component_words(system.n)
    reverse = reverse_system(system)
    balanced = stack_oracle.predecessor
    bits: dict[str, list[bool]] = {
        "forward": [],
        "backward": [],
        "paths": [],
        "reaches": [],
        "control": [],
    }
    for p in range(system.n):
        for q in range(system.n):
            bits["forward"].append(balanced(system, q, ())(p, ()))
            bits["backward"].append(balanced(reverse, q, ())(p, ()))
            bits["paths"].append(balanced(reverse, q, None)(p, ()))
    for p in range(system.n):
        for u in words:
            for q in range(system.n):
                for v in words:
                    bits["reaches"].append(balanced(system, q, v)(p, u))
    for p in range(system.n):
        for u in words:
            for q in range(system.n):
                bits["control"].append(balanced(system, q, None)(p, u))
    result = {}
    for key, values in bits.items():
        encoded = "".join("1" if value else "0" for value in values)
        result[key] = {
            "length": len(encoded),
            "code": int(encoded, 2) if encoded else 0,
            "sha256": hashlib.sha256(encoded.encode()).hexdigest(),
            "bits": encoded,
        }
    return result


def component_digests(encoded: str) -> tuple[int, int]:
    digest1 = 0
    digest2 = 0
    for bit in encoded:
        value = 1 if bit == "1" else 0
        digest1 = (digest1 * DIGEST1_BASE + value) % DIGEST1_MOD
        digest2 = (digest2 * DIGEST2_BASE + value) % DIGEST2_MOD
    return digest1, digest2


def component_source(tagged_systems: list[tuple[str, stack_oracle.System]]) -> tuple[str, dict[str, dict[str, object]]]:
    per_system = [(tag, component_expected(system)) for tag, system in tagged_systems]
    expected: dict[str, dict[str, object]] = {}
    for kind in COMPONENT_KINDS:
        encoded = "".join(details[kind]["bits"] for _, details in per_system)
        digest1, digest2 = component_digests(encoded)
        expected[kind] = {
            "systems": len(per_system),
            "length": len(encoded),
            "digest1": digest1,
            "digest2": digest2,
            "sha256": hashlib.sha256(encoded.encode()).hexdigest(),
        }

    blocks: list[str] = [
        "import Subtail.CanonicalReachabilityFast",
        "open Subtail Subtail.StackSummary Subtail.StackReachability",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "structure ComponentRow where",
        "  forward : List Bool",
        "  backward : List Bool",
        "  paths : List Bool",
        "  reaches : List Bool",
        "  control : List Bool",
        "def digest1 (xs : List Bool) : Nat :=",
        f"  xs.foldl (fun acc b => (acc * {DIGEST1_BASE} + (if b then 1 else 0)) % {DIGEST1_MOD}) 0",
        "def digest2 (xs : List Bool) : Nat :=",
        f"  xs.foldl (fun acc b => (acc * {DIGEST2_BASE} + (if b then 1 else 0)) % {DIGEST2_MOD}) 0",
        "def emit (tag : String) (xs : List Bool) : IO Unit :=",
        '  IO.println ("' + COMPONENT_MARKER + '" ++ tag ++ ":" ++ toString xs.length ++ ":" ++ toString (digest1 xs) ++ ":" ++ toString (digest2 xs))',
    ]
    rows: list[str] = []
    for tag, system in tagged_systems:
        n = system.n
        words = component_words(n)
        word_text = "[" + ", ".join(render_word(word) for word in words) + "]"
        system_text = render_system(system)
        rows.append(
            f'''(let M : System {n} := {system_text}
  let cache := Subtail.CanonicalReachabilityFast.prepare M
  let qs := List.finRange {n}
  let ws : List Word := {word_text}
  let forward := qs.flatMap (fun p => qs.map (fun q =>
    Subtail.CanonicalReachabilityFast.lookup cache.forward p q))
  let backward := qs.flatMap (fun p => qs.map (fun q =>
    Subtail.CanonicalReachabilityFast.lookup cache.backward p q))
  let paths := qs.flatMap (fun p => qs.map (fun q =>
    Subtail.CanonicalReachabilityFast.lookup cache.paths p q))
  let reaches := qs.flatMap (fun p => ws.flatMap (fun u =>
    qs.flatMap (fun q => ws.map (fun v =>
      Subtail.CanonicalReachabilityFast.reachesCheck M cache p u q v))))
  let control := qs.flatMap (fun p => ws.flatMap (fun u =>
    qs.map (fun q =>
      Subtail.CanonicalReachabilityFast.controlReachCheck M cache p u q)))
  {{ forward := forward, backward := backward, paths := paths,
     reaches := reaches, control := control }})'''
        )
    blocks.extend(
        [
            "def main : IO Unit := do",
            "  let rows : List ComponentRow := [",
            ",\n".join("    " + row for row in rows),
            "  ]",
            "  let forward := rows.flatMap (fun row => row.forward)",
            "  let backward := rows.flatMap (fun row => row.backward)",
            "  let paths := rows.flatMap (fun row => row.paths)",
            "  let reaches := rows.flatMap (fun row => row.reaches)",
            "  let control := rows.flatMap (fun row => row.control)",
            '  emit "forward" forward',
            '  emit "backward" backward',
            '  emit "paths" paths',
            '  emit "reaches" reaches',
            '  emit "control" control',
            "#eval main",
        ]
    )
    return "\n\n".join(blocks) + "\n", expected


def normalized_cases() -> list[tuple[str, int, tuple[tuple, ...], list[stack_oracle.Word]]]:
    return [
        ("empty", 2, (), stack_oracle.words(2)),
        ("epsilon", 2, (("leq", 0, 1),), stack_oracle.words(2)),
        (
            "push-pop",
            2,
            (("lower", 0, 1, 1), ("upper", 1, 0, 1)),
            stack_oracle.words(2),
        ),
        (
            "reverse",
            2,
            (("lower", 0, 1, 0), ("upper", 0, 0, 1)),
            stack_oracle.words(2),
        ),
        (
            "denial-unsat",
            2,
            (("lower", 0, 1, 0), ("denial", 0)),
            stack_oracle.words(2),
        ),
        (
            "epsilon-and-denial",
            2,
            (("leq", 0, 1), ("denial", 1)),
            stack_oracle.words(2),
        ),
    ]


def normalized_expected(constraints: list[tuple], n: int, words: list[stack_oracle.Word]) -> list[bool]:
    return stack_oracle.semantic_case(constraints, n, words)


def normalized_source() -> tuple[str, dict[str, dict[str, object]]]:
    expected: dict[str, dict[str, object]] = {}
    blocks: list[str] = [
        "import Subtail.CanonicalReachabilityFast",
        "open Subtail Subtail.TreeSemantics",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "def code (xs : List Bool) : Nat :=",
        "  xs.foldl (fun acc b => acc * 2 + (if b then 1 else 0)) 0",
        "def emit (tag : String) (xs : List Bool) : IO Unit :=",
        '  IO.println ("' + COMPONENT_MARKER + '" ++ tag ++ ":" ++ toString xs.length ++ ":" ++ toString (code xs))',
    ]
    for tag, n, constraints, words in normalized_cases():
        key = f"normalized-{tag}"
        encoded = "".join("1" if value else "0" for value in normalized_expected(list(constraints), n, words))
        expected[key] = {
            "length": len(encoded),
            "code": int(encoded, 2) if encoded else 0,
            "sha256": hashlib.sha256(encoded.encode()).hexdigest(),
        }
        ctext = render_constraints(constraints, n)
        word_text = "[" + ", ".join(render_word(word) for word in words) + "]"
        blocks.append(
            f'''#eval emit "{key}" (let C : List (Constraint {n}) := {ctext}
  let M := Subtail.CanonicalReachability.systemOf C
  let cache := Subtail.CanonicalReachabilityFast.prepare M
  let ws : List Word := {word_text}
  [Subtail.CanonicalReachabilityFast.satCheck C cache] ++
    (List.finRange {n}).flatMap (fun a => (List.finRange {n}).flatMap (fun b =>
      ws.map (fun w => Subtail.CanonicalReachabilityFast.separationCheck C cache a b w))))'''
        )
    return "\n\n".join(blocks) + "\n", expected


def generated_cases() -> list[GeneratedCase]:
    cases: list[GeneratedCase] = []
    for n in (2, 4, 6, 8, 10):
        constraints = tuple(("leq", i, i + 1) for i in range(n - 1))
        cases.append(
            GeneratedCase(
                name=f"positive-transitive-{n}",
                kind="positive-transitivity",
                n=n,
                constraints=constraints,
                a=0,
                b=n - 1,
                expected=True,
                justification="A finite chain of listed leq premises entails its transitive endpoint.",
            )
        )
    for depth in (1, 2, 3, 4):
        width = depth + 1
        x = list(range(width))
        y = list(range(width, 2 * width))
        product = list(range(2 * width, 3 * width))
        constraints: list[tuple] = []
        constraints.extend(("leq", x[i], x[i + 1]) for i in range(depth))
        constraints.extend(("leq", y[i], y[i + 1]) for i in range(depth))
        for i in range(width):
            constraints.append(("upper", product[i], x[i], y[i]))
            constraints.append(("lower", x[i], y[i], product[i]))
        cases.append(
            GeneratedCase(
                name=f"positive-covariance-depth-{depth}",
                kind="positive-covariance",
                n=3 * width,
                constraints=tuple(constraints),
                a=product[0],
                b=product[-1],
                expected=True,
                justification="Component chains plus exact upper/lower product definitions imply covariance.",
            )
        )
    for depth in (0, 1, 2, 4, 8, 12):
        # Each lower premise contributes a false-labelled push edge i -> i+1.
        # The queried target is one state beyond that chain, so the supplied
        # address is a genuine deeper-path case while the independent oracle
        # still has an explicit finite reason for returning separation true.
        constraints = tuple(("lower", i, 0, i + 1) for i in range(depth))
        n = depth + 2
        word = (0,) * depth
        values = normalized_expected(list(constraints), n, [word])
        expected = values[1 + 0 * n + (depth + 1)]
        cases.append(
            GeneratedCase(
                name=f"negative-supplied-separation-depth-{depth}",
                kind="negative-supplied-separation",
                n=n,
                constraints=constraints,
                a=0,
                b=depth + 1,
                word=word,
                expected=expected,
                justification=(
                    "Independent P-automaton predecessor oracle accepts the supplied "
                    "source path; the target is outside the false-push chain."
                ),
            )
        )
    return cases


def generated_source(case: GeneratedCase) -> str:
    ctext = render_constraints(case.constraints, case.n)
    word = render_word(case.word)
    if case.kind == "negative-supplied-separation":
        call = (
            "let M := Subtail.CanonicalReachability.systemOf C; "
            "let cache := Subtail.CanonicalReachabilityFast.prepare M; "
            f"Subtail.CanonicalReachabilityFast.separationCheck C cache "
            f"{render_fin(case.a, case.n)} {render_fin(case.b, case.n)} {word}"
        )
    else:
        call = (
            f"Subtail.EntailmentFast.normalizedEntailsCheck C "
            f"{render_fin(case.a, case.n)} {render_fin(case.b, case.n)}"
        )
    return f'''import Subtail.EntailmentFast
import Subtail.CanonicalReachabilityFast
open Subtail Subtail.TreeSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def main : IO Unit := do
  let C : List (Constraint {case.n}) := {ctext}
  let actual : Bool := {call}
  IO.println ("{GENERATED_MARKER}{case.name}:" ++ (if actual then "true" else "false"))
#eval main
'''


def benchmark_call(fixture: decision.Fixture, variant: str) -> tuple[str, str, bool]:
    """Return import, call and whether the raw call is deliberately unchanged."""

    if fixture.kind == "raw":
        return (
            "Subtail.TerminalDecisionLazy",
            "Subtail.TerminalDecisionLazy.rawNormalizedEntailsCheckLazy",
            True,
        )
    if variant == "baseline":
        module = "Subtail.TerminalDecisionLazy"
        function = (
            "Subtail.TerminalDecisionLazy.entailsCheckLazy"
            if fixture.kind == "frontend"
            else "Subtail.TerminalDecisionLazy.normalizedEntailsCheckLazy"
        )
        return module, function, False
    module = "Subtail.EntailmentFast"
    function = (
        "Subtail.EntailmentFast.entailsCheck"
        if fixture.kind == "frontend"
        else "Subtail.EntailmentFast.normalizedEntailsCheck"
    )
    return module, function, False


def benchmark_source(fixture: decision.Fixture, variant: str) -> tuple[str, bool, str]:
    module, function, raw_unchanged = benchmark_call(fixture, variant)
    if fixture.kind == "frontend":
        call = (
            f"{function} {decision.render_input(fixture)} "
            f"{decision.render_expr(fixture.left, fixture.n)} "
            f"{decision.render_expr(fixture.right, fixture.n)}"
        )
    else:
        call = (
            f"{function} {decision.render_constraints(fixture.constraints, fixture.n)} "
            f"{render_fin(int(fixture.a), fixture.n)} {render_fin(int(fixture.b), fixture.n)}"
        )
    source = f'''import {module}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def main : IO Unit := do
  let actual : Bool := {call}
  IO.println ("{BENCHMARK_MARKER}{variant}:{fixture.name}:" ++
    (if actual then "true" else "false"))
#eval main
'''
    return source, raw_unchanged, function


def parse_marker(output: str, marker: str) -> tuple[Optional[str], Optional[str]]:
    rows = [line.strip() for line in output.splitlines() if line.startswith(marker)]
    if len(rows) != 1:
        return None, "missing_or_ambiguous_marker"
    return rows[0], None


def run_generated_source(path: Path, marker: str, timeout: float) -> dict:
    result = run_process(["lake", "env", "lean", str(path)], LEAN_ROOT, timeout)
    output = result.pop("output", "")
    result["output_tail"] = output[-2000:]
    if result.get("status") == "PASS":
        marker_line, error = parse_marker(output, marker)
        if error:
            result.update(status="FAIL", reason=error)
        else:
            result["marker"] = marker_line
    elif result.get("reason") in ("time_limit", "tool_unavailable"):
        # These are resource/tool availability outcomes, not phase errors.
        result["status"] = "UNKNOWN"
    elif any(word in output.lower() for word in RESOURCE_WORDS):
        result["status"] = "UNKNOWN"
        result["reason"] = "resource_limit_or_runtime_abort"
    else:
        result["status"] = "FAIL"
        result["reason"] = "phase_error"
    return result


def component_phase(timeout: float, scratch: Path) -> dict:
    ready, missing = fast_modules_ready()
    if not ready:
        return {"status": "NOT_READY", "reason": "missing_fast_modules", "missing": missing}
    systems = component_systems()
    source, expected = component_source(systems)
    path = scratch / "fast-components.lean"
    path.write_text(source)
    run = run_generated_source(path, COMPONENT_MARKER, timeout)
    rows: list[dict] = []
    if run.get("status") == "PASS":
        output = run.get("output_tail", "")
        for line in output.splitlines():
            if line.startswith(COMPONENT_MARKER):
                body = line[len(COMPONENT_MARKER) :]
                tag, length_text, digest1_text, digest2_text = body.split(":", 3)
                wanted = expected.get(
                    tag,
                    {"length": -1, "digest1": -1, "digest2": -1, "sha256": ""},
                )
                actual_length = int(length_text)
                actual_digest1 = int(digest1_text)
                actual_digest2 = int(digest2_text)
                row = {
                    "name": tag,
                    "status": "PASS"
                    if (wanted["length"], wanted["digest1"], wanted["digest2"])
                    == (actual_length, actual_digest1, actual_digest2)
                    else "FAIL",
                    "expected_sha256": wanted["sha256"],
                    "actual_length": actual_length,
                    "actual_digest1": actual_digest1,
                    "actual_digest2": actual_digest2,
                    "expected_length": wanted["length"],
                    "expected_digest1": wanted["digest1"],
                    "expected_digest2": wanted["digest2"],
                }
                if (wanted["length"], wanted["digest1"], wanted["digest2"]) != (
                    actual_length,
                    actual_digest1,
                    actual_digest2,
                ):
                    row["reason"] = "oracle_disagreement"
                rows.append(row)
        if len(rows) != len(expected):
            run = {
                **run,
                "status": "FAIL",
                "reason": "missing_component_rows",
                "rows_seen": len(rows),
            }
    else:
        rows = [
            {"name": tag, "status": run.get("status"), "reason": run.get("reason")}
            for tag in expected
        ]
    counts = Counter(row["status"] for row in rows)
    return {
        "status": "FAIL" if counts["FAIL"] else "UNKNOWN" if counts["UNKNOWN"] else run.get("status", "PASS"),
        "oracle": "experiments/check_stack_summary.py P-automaton predecessor saturation",
        "systems": len(systems),
        "component_kinds": list(COMPONENT_KINDS),
        "rows": rows,
        "counts": dict(counts),
        "cache_reuse": {"prepare_calls_per_system": 1, "same_cache_for_all_queries": True},
        "native": run,
    }


def normalized_component_phase(timeout: float, scratch: Path) -> dict:
    ready, missing = fast_modules_ready()
    if not ready:
        return {"status": "NOT_READY", "reason": "missing_fast_modules", "missing": missing}
    source, expected = normalized_source()
    path = scratch / "fast-normalized-components.lean"
    path.write_text(source)
    run = run_generated_source(path, COMPONENT_MARKER, timeout)
    rows: list[dict] = []
    if run.get("status") == "PASS":
        for line in run.get("output_tail", "").splitlines():
            if line.startswith(COMPONENT_MARKER):
                body = line[len(COMPONENT_MARKER) :]
                tag, length_text, code_text = body.split(":", 2)
                wanted = expected.get(tag, {"length": -1, "code": -1, "sha256": ""})
                actual_length = int(length_text)
                actual_code = int(code_text)
                rows.append({
                    "name": tag,
                    "status": "PASS" if (wanted["length"], wanted["code"]) == (actual_length, actual_code) else "FAIL",
                    "expected_sha256": wanted["sha256"],
                    "actual_length": actual_length,
                    "actual_code": actual_code,
                    "expected_length": wanted["length"],
                    "expected_code": wanted["code"],
                })
        if len(rows) != len(expected):
            run = {**run, "status": "FAIL", "reason": "missing_normalized_rows", "rows_seen": len(rows)}
    else:
        rows = [{"name": tag, "status": run.get("status"), "reason": run.get("reason")} for tag in expected]
    counts = Counter(row["status"] for row in rows)
    return {
        "status": "FAIL" if counts["FAIL"] else "UNKNOWN" if counts["UNKNOWN"] else run.get("status", "PASS"),
        "oracle": "experiments/check_stack_summary.py semantic_case using P-automaton predecessors",
        "rows": rows,
        "counts": dict(counts),
        "cache_reuse": {"prepare_calls_per_system": 1, "same_cache_for_all_constraints": True},
        "native": run,
    }


def benchmark_phase(timeout: float, scratch: Path, compare_baseline: bool) -> dict:
    ready, missing = fast_modules_ready()
    if not ready:
        return {"status": "NOT_READY", "reason": "missing_fast_modules", "missing": missing}
    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    variants = ["baseline", "candidate"] if compare_baseline else ["candidate"]
    rows: list[dict] = []
    raw_calls: set[str] = set()
    for fixture in fixtures:
        row: dict = {
            "name": fixture.name,
            "kind": fixture.kind,
            "expected": fixture.expected,
            "justification": fixture.justification,
        }
        for variant in variants:
            source, unchanged, function = benchmark_source(fixture, variant)
            path = scratch / f"{fixture.name}-{variant}.lean"
            path.write_text(source)
            run = run_generated_source(path, BENCHMARK_MARKER, timeout)
            actual_marker = run.get("marker")
            if run.get("status") == "PASS":
                actual = actual_marker.endswith(":true") if actual_marker else None
                run["actual"] = actual
                if actual != fixture.expected:
                    run.update(status="FAIL", reason="independent_expected_answer_mismatch")
            run.update(function=function, raw_backend_unchanged=unchanged)
            row[variant] = run
            if fixture.kind == "raw":
                raw_calls.add(function)
        rows.append(row)

    counts = {
        variant: {
            kind: dict(
                Counter(
                    row[variant].get("status", "FAIL")
                    for row in rows
                    if row["kind"] == kind
                )
            )
            for variant in variants
            for kind in ("frontend", "normalized", "raw")
        }
    }
    disagreements = []
    if compare_baseline:
        for row in rows:
            before = row["baseline"]
            after = row["candidate"]
            if before.get("status") == after.get("status") == "PASS":
                if before.get("actual") != after.get("actual"):
                    disagreements.append(row["name"])
    failures = [
        row["name"]
        for row in rows
        for variant in variants
        if row[variant].get("status") == "FAIL"
    ]
    return {
        "status": "FAIL" if failures or disagreements else "UNKNOWN" if any(
            row[variant].get("status") == "UNKNOWN" for row in rows for variant in variants
        ) else "PASS",
        "corpus": "experiments/check_entailment_decision.py E054 38 fixtures",
        "variants": variants,
        "counts_by_variant_and_kind": counts,
        "cases": rows,
        "baseline_candidate_disagreements": disagreements,
        "failures": failures,
        "raw_backend_warning": {
            "unchanged_call": "Subtail.TerminalDecisionLazy.rawNormalizedEntailsCheckLazy",
            "observed_functions": sorted(raw_calls),
            "candidate_does_not_use_EntailmentFast_for_raw": True,
        },
    }


def generated_phase(timeout: float, scratch: Path) -> dict:
    ready, missing = fast_modules_ready()
    if not ready:
        return {"status": "NOT_READY", "reason": "missing_fast_modules", "missing": missing}
    cases = generated_cases()
    rows: list[dict] = []
    for case in cases:
        path = scratch / f"{case.name}.lean"
        path.write_text(generated_source(case))
        run = run_generated_source(path, GENERATED_MARKER, timeout)
        if run.get("status") == "PASS":
            marker = run.get("marker", "")
            actual = marker.endswith(":true")
            run["actual"] = actual
            if actual != case.expected:
                run.update(status="FAIL", reason="independent_expected_answer_mismatch")
        rows.append({
            "name": case.name,
            "kind": case.kind,
            "n": case.n,
            "word_length": len(case.word),
            "expected": case.expected,
            "justification": case.justification,
            "cache_reuse": case.kind == "negative-supplied-separation",
            "run": run,
        })
    counts = Counter(row["run"].get("status", "FAIL") for row in rows)
    return {
        "status": "FAIL" if counts["FAIL"] else "UNKNOWN" if counts["UNKNOWN"] else "PASS",
        "oracle": "independent P-automaton supplied-address predicate plus order-law justifications",
        "rows": rows,
        "counts": dict(counts),
        "families": {
            "positive-transitivity": "Listed leq chain; expected true by transitivity.",
            "positive-covariance": "Monotone component chains with exact upper/lower product definitions; expected true by product_mono.",
            "negative-supplied-separation": "C=[] and an explicit source path; expected separation true, hence negative entailment.",
        },
    }


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--components", action="store_true", help="run cached component and normalized checks")
    ap.add_argument("--benchmark", action="store_true", help="run the matched 38-case benchmark")
    ap.add_argument("--compare-baseline", action="store_true", help="run current TerminalDecisionLazy beside candidate")
    ap.add_argument("--generated", action="store_true", help="run generated positive and supplied-separation families")
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--output", type=Path, default=ROOT / "tmp/entailment-fast.json")
    ap.add_argument("--scratch", type=Path, default=ROOT / "tmp/entailment-fast")
    return ap


def main() -> int:
    args = parser().parse_args()
    if args.timeout <= 0:
        parser().error("--timeout must be positive")
    if not (args.components or args.benchmark or args.generated):
        args.components = args.benchmark = args.generated = True
    if args.compare_baseline and not args.benchmark:
        parser().error("--compare-baseline requires --benchmark")
    args.scratch.mkdir(parents=True, exist_ok=True)
    result: dict = {
        "status": "PASS",
        "checked_revision": git_revision(),
        "host": platform.node(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "seed": SEED,
        "caps": {
            "wall_seconds_per_process": args.timeout,
            "cpu_seconds_per_process": args.timeout,
            "address_space_GiB_linux": 16,
            "lean_threads": 1,
            "lean_stack_KiB": 32768,
        },
        "source_sha256": source_hashes(),
        "phases": {},
        "limitations": [
            "Component comparisons use the independent finite P-automaton oracle; they do not replace the Lean all-input proofs.",
            "Generated negative cases validate supplied addresses, not shortest-witness or global search completeness.",
            "UNKNOWN is preserved for resource caps and is never converted into a Boolean answer.",
        ],
    }
    phase_specs = []
    if args.components:
        phase_specs.extend(
            [("components", component_phase), ("normalized", normalized_component_phase)]
        )
    if args.benchmark:
        phase_specs.append(
            ("benchmark", lambda timeout, scratch: benchmark_phase(timeout, scratch, args.compare_baseline))
        )
    if args.generated:
        phase_specs.append(("generated", generated_phase))
    for name, function in phase_specs:
        phase = function(args.timeout, args.scratch)
        result["phases"][name] = phase
        if phase.get("status") == "FAIL":
            result["status"] = "FAIL"
        elif phase.get("status") == "UNKNOWN" and result["status"] == "PASS":
            result["status"] = "UNKNOWN"
        elif phase.get("status") == "NOT_READY" and result["status"] == "PASS":
            result["status"] = "NOT_READY"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if result["status"] == "FAIL" else 0


if __name__ == "__main__":
    raise SystemExit(main())
