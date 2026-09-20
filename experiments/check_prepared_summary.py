#!/usr/bin/env python3
"""Capped E058 validation for the prepared transition representation.

This harness compares the existing ``EntailmentFast`` endpoints with the
same-signature endpoints in ``Subtail.EntailmentPrepared``.  It reuses the
E054 fixture corpus, the E055 generated families, and the existing capped
``scripts.subtail.run_process`` runner.  A timeout or other resource failure
is UNKNOWN; a completed disagreement or an independent-oracle mismatch is a
failure.

The prepared Lean module and its equality proofs are owned by the parent
workstream.  This file measures the interface and does not establish whole-
function equality, completeness, or a speedup.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, is_dataclass
import hashlib
import json
import math
import platform
from pathlib import Path
import subprocess
import sys
from typing import Iterable, Optional


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "experiments"))

import check_entailment_decision as decision  # noqa: E402
import check_fast_summary as fast  # noqa: E402


SEED = 2026092020
BENCHMARK_MARKER = "SUBTAIL_PREPARED_BENCHMARK:"
GENERATED_MARKER = "SUBTAIL_PREPARED_GENERATED:"
COMPONENT_MARKER = "SUBTAIL_PREPARED_COMPONENT:"
PREPARED_MODULE = "lean/Subtail/EntailmentPrepared.lean"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def git_revision() -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return proc.stdout.strip()


def source_hashes() -> dict[str, str]:
    """Hash the runner, fixture generators, prepared module, and Lean imports."""

    names = {
        "scripts/subtail.py",
        "experiments/check_entailment_decision.py",
        "experiments/check_fast_summary.py",
        "experiments/check_prepared_summary.py",
        "experiments/check_stack_summary.py",
        PREPARED_MODULE,
    }
    names.update(
        str(path.relative_to(ROOT))
        for path in sorted((ROOT / "lean/Subtail").glob("*.lean"))
    )
    return {
        name: sha256(ROOT / name) if (ROOT / name).is_file() else "MISSING"
        for name in sorted(names)
    }


def prepared_ready() -> tuple[bool, list[str]]:
    required = [
        "lean/Subtail/StackSummaryFast.lean",
        "lean/Subtail/CanonicalReachabilityFast.lean",
        "lean/Subtail/EntailmentFast.lean",
        PREPARED_MODULE,
    ]
    missing = [name for name in required if not (ROOT / name).is_file()]
    return not missing, missing


def render_marker_source(marker: str, variant: str, name: str, call: str, imports: Iterable[str]) -> str:
    imports_text = "\n".join(f"import {item}" for item in imports)
    return f'''{imports_text}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO Unit := do
  let actual : Bool := {call}
  IO.println ("{marker}{variant}:{name}:" ++ (if actual then "true" else "false"))

#eval main
'''


def render_fin(i: int, n: int) -> str:
    return fast.render_fin(i, n)


def render_word(word: Iterable[int]) -> str:
    return fast.render_word(word)


def prepared_benchmark_source(fixture: decision.Fixture, variant: str) -> tuple[str, str, bool]:
    """Return source, endpoint name, and whether the old raw backend is unchanged."""

    if fixture.kind == "raw":
        module = "Subtail.TerminalDecisionLazy"
        function = "Subtail.TerminalDecisionLazy.rawNormalizedEntailsCheckLazy"
        unchanged = True
        call = (
            f"{function} {decision.render_constraints(fixture)} "
            f"{decision.fin(int(fixture.a), fixture.n)} {decision.fin(int(fixture.b), fixture.n)}"
        )
    elif fixture.kind == "frontend":
        module = "Subtail.EntailmentPrepared" if variant == "prepared" else "Subtail.EntailmentFast"
        function = f"{module}.entailsCheck"
        unchanged = False
        call = (
            f"{function} {decision.render_input(fixture)} "
            f"{decision.render_expr(fixture.left, fixture.n)} "
            f"{decision.render_expr(fixture.right, fixture.n)}"
        )
    else:
        module = "Subtail.EntailmentPrepared" if variant == "prepared" else "Subtail.EntailmentFast"
        function = f"{module}.normalizedEntailsCheck"
        unchanged = False
        call = (
            f"{function} {decision.render_constraints(fixture)} "
            f"{decision.fin(int(fixture.a), fixture.n)} {decision.fin(int(fixture.b), fixture.n)}"
        )
    imports = [module]
    return render_marker_source(BENCHMARK_MARKER, variant, fixture.name, call, imports), function, unchanged


def nested_generated_cases() -> list[decision.Fixture]:
    """The four original-expression E055 depth fixtures."""

    cases: list[decision.Fixture] = []
    for depth in (3, 4, 6, 8):
        left, right = decision.V(0), decision.V(1)
        for _ in range(depth):
            left, right = decision.P(left, decision.BOT), decision.P(right, decision.BOT)
        cases.append(
            decision.frontend(
                f"negative-frontend-products-depth-{depth}",
                2,
                (),
                left,
                right,
                False,
                "finite_countermodel",
                "Set x=product(bottom,bottom), y=bottom; the first separating address is d zeroes.",
            )
        )
    return cases


def generated_cases() -> list[object]:
    """Return the exact 15 fast-generated plus 4 nested-product E055 cases."""

    cases: list[object] = list(fast.generated_cases())
    cases.extend(nested_generated_cases())
    names = [case.name for case in cases]
    if len(cases) != 19 or len(names) != len(set(names)):
        raise AssertionError(f"expected 19 unique generated cases, got {len(names)}")
    return cases


def generated_source(case: object, variant: str) -> tuple[str, str, str, bool]:
    """Return source, endpoint, result semantics, and raw-backend flag."""

    if isinstance(case, fast.GeneratedCase):
        constraints = fast.render_constraints(case.constraints, case.n)
        if case.kind == "negative-supplied-separation":
            imports = ["Subtail.CanonicalReachabilityFast"]
            if variant == "prepared":
                imports.insert(0, "Subtail.EntailmentPrepared")
                call = (
                    "Subtail.EntailmentPrepared.separationCheck "
                    "C "
                    "(Subtail.EntailmentPrepared.prepare "
                    "(Subtail.CanonicalReachability.systemOf C)) "
                    f"{render_fin(case.a, case.n)} {render_fin(case.b, case.n)} {render_word(case.word)}"
                )
                endpoint = "Subtail.EntailmentPrepared.separationCheck"
            else:
                call = (
                    "Subtail.CanonicalReachabilityFast.separationCheck "
                    "C "
                    f"(Subtail.CanonicalReachabilityFast.prepare "
                    f"(Subtail.CanonicalReachability.systemOf C)) "
                    f"{render_fin(case.a, case.n)} {render_fin(case.b, case.n)} {render_word(case.word)}"
                )
                endpoint = "Subtail.CanonicalReachabilityFast.separationCheck"
            imports_text = "\n".join("import " + item for item in imports)
            source = f'''{imports_text}
open Subtail Subtail.TreeSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO Unit := do
  let C : List (Constraint {case.n}) := {constraints}
  let actual : Bool := {call}
  IO.println ("{GENERATED_MARKER}{variant}:{case.name}:" ++ (if actual then "true" else "false"))

#eval main
'''
            return source, endpoint, "supplied_separation_bool", False

        imports = ["Subtail.EntailmentPrepared" if variant == "prepared" else "Subtail.EntailmentFast"]
        module = imports[0]
        call = (
            f"{module}.normalizedEntailsCheck C "
            f"{render_fin(case.a, case.n)} {render_fin(case.b, case.n)}"
        )
        imports_text = "\n".join("import " + item for item in imports)
        source = f'''{imports_text}
open Subtail Subtail.TreeSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO Unit := do
  let C : List (Constraint {case.n}) := {constraints}
  let actual : Bool := {call}
  IO.println ("{GENERATED_MARKER}{variant}:{case.name}:" ++ (if actual then "true" else "false"))

#eval main
'''
        return source, f"{module}.normalizedEntailsCheck", "normalized_entailment_bool", False

    assert isinstance(case, decision.Fixture)
    module = "Subtail.EntailmentPrepared" if variant == "prepared" else "Subtail.EntailmentFast"
    call = (
        f"{module}.entailsCheck {decision.render_input(case)} "
        f"{decision.render_expr(case.left, case.n)} {decision.render_expr(case.right, case.n)}"
    )
    source = render_marker_source(GENERATED_MARKER, variant, case.name, call, [module])
    return source, f"{module}.entailsCheck", "expression_entailment_bool", False


def run_marked(
    source: str,
    path: Path,
    marker: str,
    timeout: float,
    expected_markers: int = 1,
) -> dict[str, object]:
    path.write_text(source)
    result = fast.run_generated_source(path, marker, timeout, expected_markers)
    result["generated_source_sha256"] = sha256_bytes(source.encode())
    return result


def marker_bool(run: dict[str, object], prefix: str) -> Optional[bool]:
    marker = run.get("marker")
    if not isinstance(marker, str):
        return None
    if marker == prefix + "true":
        return True
    if marker == prefix + "false":
        return False
    return None


def check_expected(run: dict[str, object], marker_prefix: str, expected: bool) -> None:
    if run.get("status") != "PASS":
        return
    actual = marker_bool(run, marker_prefix)
    run["actual"] = actual
    if actual is None:
        run.update(status="FAIL", reason="missing_or_ambiguous_boolean_marker")
    elif actual != expected:
        run.update(status="FAIL", reason="independent_expected_answer_mismatch")


def benchmark_phase(timeout: float, scratch: Path, compare_baseline: bool) -> dict[str, object]:
    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    variants = ["baseline", "prepared"] if compare_baseline else ["prepared"]
    rows: list[dict[str, object]] = []
    disagreements: list[str] = []
    failures: list[str] = []
    raw_calls: set[str] = set()

    for fixture in fixtures:
        row: dict[str, object] = {
            "name": fixture.name,
            "kind": fixture.kind,
            "expected": fixture.expected,
            "justification": fixture.justification,
        }
        for variant in variants:
            source, function, unchanged = prepared_benchmark_source(fixture, variant)
            path = scratch / f"e054-{fixture.name}-{variant}.lean"
            run = run_marked(source, path, BENCHMARK_MARKER + variant + ":" + fixture.name + ":", timeout)
            check_expected(run, BENCHMARK_MARKER + variant + ":" + fixture.name + ":", fixture.expected)
            run.update(function=function, raw_backend_unchanged=unchanged)
            row[variant] = run
            if unchanged:
                raw_calls.add(function)
            if run.get("status") == "FAIL":
                failures.append(f"{fixture.name}:{variant}")
        if compare_baseline:
            before, after = row["baseline"], row["prepared"]
            if (
                isinstance(before, dict)
                and isinstance(after, dict)
                and before.get("status") == after.get("status") == "PASS"
                and before.get("actual") != after.get("actual")
            ):
                disagreements.append(fixture.name)
        rows.append(row)
        print(f"{fixture.name}: " + "; ".join(f"{v} {row[v]['status']}" for v in variants), flush=True)

    counts = {
        variant: {
            kind: dict(
                Counter(
                    row[variant].get("status", "FAIL")
                    for row in rows
                    if row["kind"] == kind
                )
            )
            for kind in ("frontend", "normalized", "raw")
        }
        for variant in variants
    }
    any_unknown = any(
        row[variant].get("status") == "UNKNOWN" for row in rows for variant in variants
    )
    return {
        "status": "FAIL" if failures or disagreements else "UNKNOWN" if any_unknown else "PASS",
        "corpus": "experiments/check_entailment_decision.py E054 38 fixtures",
        "fixture_count": len(fixtures),
        "variants": variants,
        "counts_by_variant_and_kind": counts,
        "cases": rows,
        "baseline_prepared_disagreements": disagreements,
        "failures": failures,
        "raw_backend_warning": {
            "unchanged_call": "Subtail.TerminalDecisionLazy.rawNormalizedEntailsCheckLazy",
            "observed_functions": sorted(raw_calls),
            "prepared_does_not_replace_raw_backend": True,
        },
    }


def machine_bits(system: fast.stack_oracle.System) -> str:
    bits: list[bool] = []
    for p in range(system.n):
        for q in range(system.n):
            bits.append((p, q) in system.eps)
            bits.append((0, p, q) in system.push)
            bits.append((1, p, q) in system.push)
            bits.append((0, p, q) in system.pop)
            bits.append((1, p, q) in system.pop)
    return "".join("1" if bit else "0" for bit in bits)


def component_expected(
    systems: list[tuple[str, fast.stack_oracle.System]] | None = None,
) -> dict[str, dict[str, object]]:
    if systems is None:
        systems = fast.component_systems()
    encoded: dict[str, str] = {"machine": "", **{kind: "" for kind in fast.COMPONENT_KINDS}}
    for _, system in systems:
        expected = fast.component_expected(system)
        encoded["machine"] += machine_bits(system)
        for kind in fast.COMPONENT_KINDS:
            encoded[kind] += expected[kind]["bits"]
    result: dict[str, dict[str, object]] = {}
    for kind, bits in encoded.items():
        digest1, digest2 = fast.component_digests(bits)
        result[kind] = {
            "length": len(bits),
            "digest1": digest1,
            "digest2": digest2,
            "sha256": sha256_bytes(bits.encode()),
        }
    return result


def component_source() -> tuple[str, dict[str, dict[str, object]]]:
    systems = fast.component_systems()
    expected = component_expected(systems)
    lines = [
        "import Subtail.EntailmentPrepared",
        "import Subtail.CanonicalReachabilityFast",
        "open Subtail Subtail.StackSummary Subtail.StackReachability",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "structure ComponentRow where",
        "  machine : List Bool",
        "  forward : List Bool",
        "  backward : List Bool",
        "  paths : List Bool",
        "  reaches : List Bool",
        "  control : List Bool",
        "def digest1 (xs : List Bool) : Nat :=",
        f"  xs.foldl (fun acc b => (acc * {fast.DIGEST1_BASE} + (if b then 1 else 0)) % {fast.DIGEST1_MOD}) 0",
        "def digest2 (xs : List Bool) : Nat :=",
        f"  xs.foldl (fun acc b => (acc * {fast.DIGEST2_BASE} + (if b then 1 else 0)) % {fast.DIGEST2_MOD}) 0",
        "def emit (tag : String) (xs : List Bool) : IO Unit :=",
        f'  IO.println ("{COMPONENT_MARKER}" ++ tag ++ ":" ++ toString xs.length ++ ":" ++ toString (digest1 xs) ++ ":" ++ toString (digest2 xs))',
    ]
    rows: list[str] = []
    for tag, system in systems:
        n = system.n
        words = fast.component_words(n)
        word_text = "[" + ", ".join(render_word(word) for word in words) + "]"
        system_text = fast.render_system(system)
        rows.append(
            f'''(let M : System {n} := {system_text}
  let prepared := Subtail.EntailmentPrepared.prepare M
  let machine := prepared.machine
  let cache := prepared.cache
  let qs := List.finRange {n}
  let ws : List Word := {word_text}
  let machineBits := qs.flatMap (fun p => qs.flatMap (fun q =>
    [machine.eps p q, machine.push false p q, machine.push true p q,
     machine.pop false p q, machine.pop true p q]))
  let forward := qs.flatMap (fun p => qs.map (fun q =>
    Subtail.CanonicalReachabilityFast.lookup cache.forward p q))
  let backward := qs.flatMap (fun p => qs.map (fun q =>
    Subtail.CanonicalReachabilityFast.lookup cache.backward p q))
  let paths := qs.flatMap (fun p => qs.map (fun q =>
    Subtail.CanonicalReachabilityFast.lookup cache.paths p q))
  let reaches := qs.flatMap (fun p => ws.flatMap (fun u =>
    qs.flatMap (fun q => ws.map (fun v =>
      Subtail.CanonicalReachabilityFast.reachesCheck machine cache p u q v))))
  let control := qs.flatMap (fun p => ws.flatMap (fun u =>
    qs.map (fun q =>
      Subtail.CanonicalReachabilityFast.controlReachCheck machine cache p u q)))
  {{ machine := machineBits, forward := forward, backward := backward, paths := paths,
     reaches := reaches, control := control }})'''
        )
    lines.extend(
        [
            "def main : IO Unit := do",
            "  let rows : List ComponentRow := [",
            ",\n".join("    " + row for row in rows),
            "  ]",
            "  let machine := rows.flatMap (fun row => row.machine)",
            "  let forward := rows.flatMap (fun row => row.forward)",
            "  let backward := rows.flatMap (fun row => row.backward)",
            "  let paths := rows.flatMap (fun row => row.paths)",
            "  let reaches := rows.flatMap (fun row => row.reaches)",
            "  let control := rows.flatMap (fun row => row.control)",
            '  emit "machine" machine',
            '  emit "forward" forward',
            '  emit "backward" backward',
            '  emit "paths" paths',
            '  emit "reaches" reaches',
            '  emit "control" control',
            "#eval main",
        ]
    )
    return "\n\n".join(lines) + "\n", expected


def component_phase(timeout: float, scratch: Path) -> dict[str, object]:
    source, expected = component_source()
    path = scratch / "prepared-components.lean"
    run = run_marked(source, path, COMPONENT_MARKER, timeout, len(expected))
    rows: list[dict[str, object]] = []
    seen_tags: list[str] = []
    if run.get("status") == "PASS":
        for marker in run.get("markers", []):
            body = marker[len(COMPONENT_MARKER) :]
            try:
                tag, length_text, digest1_text, digest2_text = body.split(":", 3)
                actual = (int(length_text), int(digest1_text), int(digest2_text))
            except (AttributeError, ValueError):
                rows.append({"name": str(body), "status": "FAIL", "reason": "malformed_component_marker"})
                continue
            seen_tags.append(tag)
            wanted = expected.get(tag)
            if wanted is None:
                rows.append({"name": tag, "status": "FAIL", "reason": "unknown_component_kind"})
                continue
            target = (wanted["length"], wanted["digest1"], wanted["digest2"])
            row = {
                "name": tag,
                "status": "PASS" if actual == target else "FAIL",
                "actual_length": actual[0],
                "actual_digest1": actual[1],
                "actual_digest2": actual[2],
                "expected_length": target[0],
                "expected_digest1": target[1],
                "expected_digest2": target[2],
                "expected_sha256": wanted["sha256"],
            }
            if row["status"] == "FAIL":
                row["reason"] = "independent_oracle_disagreement"
            rows.append(row)
        if len(rows) != len(expected) or set(seen_tags) != set(expected):
            run = {
                **run,
                "status": "FAIL",
                "reason": "missing_or_ambiguous_component_rows",
                "rows_seen": len(rows),
                "tags_seen": seen_tags,
            }
    else:
        rows = [
            {"name": name, "status": run.get("status"), "reason": run.get("reason")}
            for name in expected
        ]
    counts = Counter(row["status"] for row in rows)
    status = (
        "FAIL"
        if run.get("status") == "FAIL" or counts["FAIL"]
        else "UNKNOWN"
        if counts["UNKNOWN"]
        else "PASS"
    )
    return {
        "status": status,
        "oracle": "experiments/check_stack_summary.py P-automaton predecessor saturation",
        "systems": len(fast.component_systems()),
        "component_kinds": ["machine", *fast.COMPONENT_KINDS],
        "rows": rows,
        "counts": dict(counts),
        "native": run,
        "digest_comparison": {
            "fields": ["length", "digest1", "digest2"],
            "sha256_recorded_for_each_kind": True,
            "independent_oracle": "Python P-automaton predecessor saturation",
        },
        "limitation": "This checks the prepared record and cache interface; it does not prove whole-function solver equality.",
    }


def fixture_identity() -> dict[str, object]:
    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    generated = generated_cases()

    def normalize(value):
        if is_dataclass(value):
            return normalize(asdict(value))
        if isinstance(value, decision.Expr):
            return {"op": value.op, "args": normalize(value.args)}
        if isinstance(value, dict):
            return {str(k): normalize(v) for k, v in sorted(value.items(), key=lambda item: str(item[0]))}
        if isinstance(value, (tuple, list)):
            return [normalize(item) for item in value]
        return value

    payload = {
        "e054": [normalize(fixture) for fixture in fixtures],
        "e055_generated": [normalize(case) for case in generated],
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return {
        "e054_count": len(fixtures),
        "e055_generated_count": len(generated),
        "e054_names": [fixture.name for fixture in fixtures],
        "e055_generated_names": [case.name for case in generated],
        "sha256": sha256_bytes(encoded),
    }


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--components", action="store_true", help="run independent prepared-record/cache component checks")
    ap.add_argument("--benchmark", action="store_true", help="run the matched 38-case E054 corpus")
    ap.add_argument("--generated", action="store_true", help="run all 19 E055 generated families")
    ap.add_argument("--compare-baseline", action="store_true", help="run EntailmentFast beside prepared endpoints")
    ap.add_argument("--timeout", type=float, default=20.0, help="per-process wall/CPU cap")
    ap.add_argument("--output", type=Path, default=ROOT / "tmp/entailment-prepared.json")
    ap.add_argument("--scratch", type=Path, default=ROOT / "tmp/entailment-prepared")
    return ap


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser().error("--timeout must be finite and positive")
    if not (args.components or args.benchmark or args.generated):
        args.benchmark = args.generated = True
    if args.compare_baseline and not (args.benchmark or args.generated):
        parser().error("--compare-baseline requires --benchmark or --generated")
    ready, missing = prepared_ready()
    args.scratch = args.scratch.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)
    result: dict[str, object] = {
        "status": "PASS" if ready else "NOT_READY",
        "checked_revision": git_revision(),
        "host": platform.node(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "seed": SEED,
        "caps": {
            "wall_seconds_per_process": args.timeout,
            "cpu_seconds_limit_rounded_up": max(1, math.ceil(args.timeout)),
            "address_space_GiB": 16,
            "address_space_enforced_on_linux": True,
            "address_space_enforced_here": platform.system() == "Linux",
            "lean_threads": 1,
            "lean_stack_KiB": 32768,
            "runner": "scripts/subtail.py:run_process",
        },
        "source_sha256": source_hashes(),
        "fixture_identity": fixture_identity(),
        "phases": {},
        "limitations": [
            "The prepared module's equality theorem and whole-function correctness are parent-owned and are not established by this harness.",
            "A completed baseline/prepared agreement is a regression result, not a proof of completeness or an unrestricted speedup.",
            "Raw fixtures call TerminalDecisionLazy.rawNormalizedEntailsCheckLazy in every variant; they are deliberately unchanged.",
            "Supplied-address rows report a separation Boolean, while normalized and frontend rows report entailment Booleans.",
            "Missing prepared modules are reported as NOT_READY; caps and failed process execution remain UNKNOWN and are never converted into Boolean answers.",
            "The wall cap is exact per process; the runner rounds the CPU RLIMIT up to at least one second and enforces the address-space cap only on Linux.",
            "The original E055 #eval launch and scripts.subtail.run_process caps are retained for matched validation.",
        ],
    }
    if not ready:
        result["missing"] = missing

    phase_specs = []
    if args.components:
        phase_specs.append(("components", component_phase))
    if args.benchmark:
        phase_specs.append(("benchmark", lambda timeout, scratch: benchmark_phase(timeout, scratch, args.compare_baseline)))
    if args.generated:
        phase_specs.append(("generated", lambda timeout, scratch: generated_phase(timeout, scratch, args.compare_baseline)))

    if ready:
        for name, function in phase_specs:
            phase = function(args.timeout, args.scratch)
            result["phases"][name] = phase
            if phase.get("status") == "FAIL":
                result["status"] = "FAIL"
            elif phase.get("status") == "UNKNOWN" and result["status"] == "PASS":
                result["status"] = "UNKNOWN"
    else:
        for name, _ in phase_specs:
            result["phases"][name] = {"status": "NOT_READY", "missing": missing}

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if result["status"] == "FAIL" else 0


def generated_phase(timeout: float, scratch: Path, compare_baseline: bool) -> dict[str, object]:
    cases = generated_cases()
    variants = ["baseline", "prepared"] if compare_baseline else ["prepared"]
    rows: list[dict[str, object]] = []
    failures: list[str] = []
    disagreements: list[str] = []
    for case in cases:
        expected = case.expected
        row: dict[str, object] = {
            "name": case.name,
            "kind": case.kind if isinstance(case, fast.GeneratedCase) else "negative-frontend-products",
            "n": case.n,
            "expected": expected,
            "justification": case.justification,
        }
        for variant in variants:
            source, endpoint, result_semantics, unchanged = generated_source(case, variant)
            prefix = GENERATED_MARKER + variant + ":" + case.name + ":"
            path = scratch / f"e055-{case.name}-{variant}.lean"
            run = run_marked(source, path, prefix, timeout)
            check_expected(run, prefix, expected)
            run.update(endpoint=endpoint, result_semantics=result_semantics, raw_backend_unchanged=unchanged)
            row[variant] = run
            if run.get("status") == "FAIL":
                failures.append(f"{case.name}:{variant}")
        if compare_baseline:
            before, after = row["baseline"], row["prepared"]
            if (
                isinstance(before, dict)
                and isinstance(after, dict)
                and before.get("status") == after.get("status") == "PASS"
                and before.get("actual") != after.get("actual")
            ):
                disagreements.append(case.name)
        rows.append(row)
        print(f"{case.name}: " + "; ".join(f"{v} {row[v]['status']}" for v in variants), flush=True)
    counts = {
        variant: dict(Counter(row[variant].get("status", "FAIL") for row in rows))
        for variant in variants
    }
    any_unknown = any(row[variant].get("status") == "UNKNOWN" for row in rows for variant in variants)
    return {
        "status": "FAIL" if failures or disagreements else "UNKNOWN" if any_unknown else "PASS",
        "fixture_count": len(cases),
        "variants": variants,
        "counts": counts,
        "rows": rows,
        "baseline_prepared_disagreements": disagreements,
        "failures": failures,
        "oracle": "E055 independent case justifications reused from check_fast_summary.py and check_entailment_decision.py",
        "families": {
            "positive-transitivity": "Listed leq chain; expected true by transitivity.",
            "positive-covariance": "Component chains plus exact upper/lower product definitions; expected true by product_mono.",
            "negative-supplied-separation": "Independent P-automaton supplied-address predicate; expected result is separation true/false.",
            "negative-frontend-products": "Explicit finite-tree countermodel; expected expression entailment is false.",
        },
    }


if __name__ == "__main__":
    raise SystemExit(main())
