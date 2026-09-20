#!/usr/bin/env python3
"""Bounded validation for the cached raw summary construction.

The raw phase calls the new prepared endpoint directly and compares it with
the previous complete endpoint.  The component phase emits every field of
the cached and reference summary instances and checks both exact equality and
an independent Python P-automaton construction on small inputs.

This is validation evidence.  It does not replace the Lean equality proofs,
and a timeout or unavailable parent module is never a Boolean answer.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, is_dataclass, replace
import hashlib
import json
import math
import platform
from pathlib import Path
import subprocess
import sys
from typing import Iterable, Optional


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "experiments"))

import check_entailment_decision as decision  # noqa: E402
import check_fast_summary as fast  # noqa: E402
import check_subtype_summary as summary_oracle  # noqa: E402
import check_prepared_summary as prepared  # noqa: E402


SEED = 2026092020
TIMEOUT_DEFAULT = 20.0
RAW_MARKER = "SUBTAIL_SUMMARY_CACHED_RAW:"
COMPONENT_MARKER = "SUBTAIL_SUMMARY_CACHED_COMPONENT:"
CACHED_MODULE = "lean/Subtail/SummaryInstanceCached.lean"
PREPARED_MODULE = "lean/Subtail/EntailmentPrepared.lean"


@dataclass(frozen=True)
class ComponentCase:
    name: str
    n: int
    constraints: tuple[tuple, ...]
    tags: tuple[str, ...]
    queries: tuple[tuple[int, int], ...]


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
    names = {
        "scripts/subtail.py",
        "experiments/check_entailment_decision.py",
        "experiments/check_fast_summary.py",
        "experiments/check_prepared_summary.py",
        "experiments/check_stack_summary.py",
        "experiments/check_subtype_summary.py",
        "experiments/check_finishing_trace.py",
        "experiments/check_summary_cached.py",
        "lean/Subtail/CanonicalReachability.lean",
        "lean/Subtail/CanonicalReachabilityFast.lean",
        "lean/Subtail/EntailmentPrepared.lean",
        "lean/Subtail/InfiniteDecisionLazy.lean",
        "lean/Subtail/SummaryAutomaton.lean",
        CACHED_MODULE,
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


def normalize(value):
    if is_dataclass(value):
        return normalize(asdict(value))
    if isinstance(value, dict):
        return {
            str(key): normalize(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if isinstance(value, (tuple, list)):
        return [normalize(item) for item in value]
    if isinstance(value, (set, frozenset)):
        return sorted(normalize(item) for item in value)
    return value


def old_raw_fixtures() -> list[decision.Fixture]:
    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    raw = [fixture for fixture in fixtures if fixture.kind == "raw"]
    if len(raw) != 7:
        raise AssertionError(f"expected seven E052 raw fixtures, found {len(raw)}")
    return raw


def stress_raw_fixtures() -> list[decision.Fixture]:
    """E059 n=3/n=4 rows plus separately named n=5/n=6 extensions."""

    rows: list[decision.Fixture] = []
    for n, cohort in ((3, "e059"), (4, "e059"), (5, "extended"), (6, "extended")):
        rows.append(
            decision.raw(
                f"empty-n{n}-query-0-1",
                n,
                (),
                0,
                1,
                False,
                "root-bottom-countermodel",
                "The empty premise set permits variable 0 to be root-only and variable 1 to be bottom.",
                cohort,
            )
        )
    return rows


def all_queries(n: int) -> tuple[tuple[int, int], ...]:
    return tuple((a, b) for a in range(n) for b in range(n))


def component_cases() -> list[ComponentCase]:
    """Small exact corpora with explicit primitive-direction coverage."""

    cases: list[ComponentCase] = []
    primitive = (
        ("leq", 0, 0),
        ("upper", 0, 0, 0),
        ("lower", 0, 0, 0),
        ("denial", 0),
    )
    for mask in range(16):
        constraints = tuple(
            item for index, item in enumerate(primitive) if mask >> index & 1
        )
        cases.append(
            ComponentCase(
                f"n1-exhaustive-{mask:02d}",
                1,
                constraints,
                ("n1", "primitive", "diagonal"),
                all_queries(1),
            )
        )

    named_n2 = [
        ("n2-empty-unreachable", (), ("empty", "unreachable")),
        ("n2-forward-epsilon", (("leq", 0, 1),), ("forward", "ordered")),
        ("n2-reverse-epsilon", (("leq", 1, 0),), ("reverse", "ordered")),
        ("n2-lower", (("lower", 0, 1, 1),), ("lower",)),
        ("n2-upper", (("upper", 0, 1, 1),), ("upper",)),
        ("n2-denial", (("denial", 1),), ("denial",)),
        (
            "n2-unsat-lower-denial",
            (("lower", 0, 0, 1), ("denial", 1)),
            ("lower", "denial", "unsat"),
        ),
        ("n2-diagonal", (("leq", 0, 0),), ("diagonal", "ordered")),
        (
            "n2-mixed-reverse",
            (("lower", 0, 1, 0), ("upper", 1, 0, 1), ("leq", 1, 0), ("denial", 0)),
            ("lower", "upper", "reverse", "denial"),
        ),
        (
            "n2-unreachable-state",
            (("lower", 0, 1, 1), ("denial", 0)),
            ("unreachable", "lower", "denial"),
        ),
    ]
    for name, constraints, tags in named_n2:
        cases.append(ComponentCase(name, 2, tuple(constraints), tuple(tags), all_queries(2)))

    named_n3 = [
        (
            "n3-unreachable-variable",
            (("leq", 0, 1), ("denial", 2)),
            ("n3", "unreachable", "denial"),
        ),
        (
            "n3-reverse-lower-upper",
            (("lower", 0, 2, 1), ("upper", 1, 0, 2), ("leq", 1, 0)),
            ("n3", "reverse", "lower", "upper"),
        ),
        (
            "n3-unsat-forced-denial",
            (("lower", 0, 0, 2), ("denial", 2)),
            ("n3", "unsat", "denial"),
        ),
    ]
    for name, constraints, tags in named_n3:
        cases.append(ComponentCase(name, 3, tuple(constraints), tuple(tags), all_queries(3)))
    return cases


def fixture_identity() -> dict[str, object]:
    raw = old_raw_fixtures()
    stress = stress_raw_fixtures()
    components = component_cases()
    payload = {
        "e054_all": [normalize(fixture) for fixture in decision.corpus()],
        "e052_raw": [normalize(fixture) for fixture in raw],
        "e059_stress": [normalize(fixture) for fixture in stress[:2]],
        "extended_stress": [normalize(fixture) for fixture in stress[2:]],
        "components": [normalize(case) for case in components],
    }
    digest = sha256_bytes(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode())
    return {
        "e054_all_count": len(decision.corpus()),
        "e052_raw_count": len(raw),
        "e052_raw_names": [fixture.name for fixture in raw],
        "e059_stress_count": 2,
        "e059_stress_names": [fixture.name for fixture in stress[:2]],
        "extended_stress_count": 2,
        "extended_stress_names": [fixture.name for fixture in stress[2:]],
        "component_case_count": len(components),
        "component_instance_count": sum(len(case.queries) for case in components),
        "component_case_names": [case.name for case in components],
        "sha256": digest,
    }


def missing_modules(kind: str) -> list[str]:
    required = {
        "raw": [
            CACHED_MODULE,
            PREPARED_MODULE,
            "lean/Subtail/InfiniteDecisionLazy.lean",
            "lean/Subtail/CanonicalReachabilityFast.lean",
        ],
        "stress_raw": [
            CACHED_MODULE,
            PREPARED_MODULE,
            "lean/Subtail/InfiniteDecisionLazy.lean",
        ],
        "components": [
            CACHED_MODULE,
            PREPARED_MODULE,
            "lean/Subtail/CanonicalReachabilityFast.lean",
            "lean/Subtail/SummaryAutomaton.lean",
        ],
        "full38": [
            CACHED_MODULE,
            PREPARED_MODULE,
            "lean/Subtail/EntailmentFast.lean",
            "lean/Subtail/InfiniteDecisionLazy.lean",
        ],
        "generated19": [
            PREPARED_MODULE,
            "lean/Subtail/EntailmentFast.lean",
        ],
    }[kind]
    return [name for name in required if not (ROOT / name).is_file()]


def render_constraints(constraints: Iterable[tuple], n: int) -> str:
    rows = ", ".join(
        decision.render_constraint((kind, tuple(args)), n)
        for kind, *args in constraints
    )
    return f"([{rows}] : List (Subtail.TreeSemantics.Constraint {n}))"


def render_bool_source(marker: str, call: str, imports: Iterable[str]) -> str:
    imports_text = "\n".join(f"import {item}" for item in imports)
    return f'''{imports_text}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO Unit := do
  let actual : Bool := {call}
  IO.println ("{marker}" ++ (if actual then "true" else "false"))

#eval main
'''


def raw_source(fixture: decision.Fixture, variant: str, marker: str) -> tuple[str, str]:
    if variant == "baseline":
        module = "Subtail.InfiniteDecisionLazy"
        function = "Subtail.InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy"
    elif variant == "candidate":
        module = "Subtail.EntailmentPrepared"
        function = "Subtail.EntailmentPrepared.rawNormalizedEntailsCheck"
    else:
        raise ValueError(f"unknown raw variant: {variant}")
    call = (
        f"{function} {decision.render_constraints(fixture)} "
        f"{decision.fin(int(fixture.a), fixture.n)} "
        f"{decision.fin(int(fixture.b), fixture.n)}"
    )
    return render_bool_source(marker, call, [module]), function


def run_marked(
    source: str, path: Path, marker: str, timeout: float, expected_markers: int = 1
) -> dict[str, object]:
    path.write_text(source)
    result = fast.run_generated_source(path, marker, timeout, expected_markers)
    result["generated_source_sha256"] = sha256_bytes(source.encode())
    return result


def selected_variants(compare_baseline: bool) -> tuple[str, ...]:
    return ("baseline", "candidate") if compare_baseline else ("candidate",)


def parse_bool(run: dict[str, object], marker: str) -> Optional[bool]:
    if run.get("status") != "PASS":
        return None
    value = run.get("marker")
    if value == marker + "true":
        return True
    if value == marker + "false":
        return False
    run.update(status="FAIL", reason="missing_or_ambiguous_boolean_marker")
    return None


def check_raw_run(run: dict[str, object], marker: str, expected: bool) -> None:
    actual = parse_bool(run, marker)
    if actual is not None:
        run["actual"] = actual
        if actual != expected:
            run.update(status="FAIL", reason="independent_expected_answer_mismatch")


def aggregate_status(rows: list[dict[str, object]]) -> str:
    statuses = [
        value.get("status", "FAIL")
        for row in rows
        for value in row.get("variants", {}).values()
        if isinstance(value, dict)
    ]
    if any(status == "FAIL" for status in statuses) or any(
        row.get("disagreement") or row.get("python_disagreement") for row in rows
    ):
        return "FAIL"
    if any(status == "UNKNOWN" for status in statuses):
        return "UNKNOWN"
    return "PASS"


def raw_phase(
    fixtures: list[decision.Fixture],
    marker_base: str,
    timeout: float,
    scratch: Path,
    compare_baseline: bool,
) -> dict[str, object]:
    variants = selected_variants(compare_baseline)
    rows: list[dict[str, object]] = []
    for fixture in fixtures:
        row: dict[str, object] = {
            "name": fixture.name,
            "n": fixture.n,
            "expected": fixture.expected,
            "reason": fixture.reason,
            "justification": fixture.justification,
            "tags": list(fixture.tags),
            "variants": {},
        }
        for variant in variants:
            marker = f"{marker_base}{variant}:{fixture.name}:"
            source, endpoint = raw_source(fixture, variant, marker)
            run = run_marked(
                source,
                scratch / f"raw-{fixture.name}-{variant}.lean",
                marker,
                timeout,
            )
            check_raw_run(run, marker, fixture.expected)
            run["endpoint"] = endpoint
            row["variants"][variant] = run
        if compare_baseline:
            baseline = row["variants"]["baseline"]
            candidate = row["variants"]["candidate"]
            if (
                baseline.get("status") == candidate.get("status") == "PASS"
                and baseline.get("actual") != candidate.get("actual")
            ):
                row["disagreement"] = True
                row["reason_code"] = "baseline_candidate_disagreement"
        rows.append(row)
        print(
            f"{fixture.name}: "
            + "; ".join(
                f"{variant} {row['variants'][variant].get('status')}"
                for variant in variants
            ),
            flush=True,
        )
    return {
        "status": aggregate_status(rows),
        "fixture_count": len(rows),
        "variants": list(variants),
        "rows": rows,
        "unknown_is_not_no": True,
        "baseline_endpoint": "Subtail.InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy",
        "candidate_endpoint": "Subtail.EntailmentPrepared.rawNormalizedEntailsCheck",
        "limitation": "Raw agreement and independent fixture answers do not establish the cached Lean equality or subtype completeness theorem.",
    }


def python_instance(n: int, constraints: tuple[tuple, ...], a: int, b: int):
    """Return the independent P-automaton instance and satisfiability bit."""

    return summary_oracle.reference(n, list(constraints), a, b)


def instance_encoding(instance) -> dict[str, object]:
    return {
        "initial": int(instance.initial),
        "transitions": [int(target) for row in instance.delta for target in row],
        "bad": "".join("1" if q in instance.bad else "0" for q in range(len(instance.delta))),
        "final": "".join("1" if q in instance.finals else "0" for q in range(len(instance.delta))),
        "flags": "".join(
            "1" if (p, q) in instance.flags else "0"
            for p in range(len(instance.delta))
            for q in range(len(instance.delta))
        ),
    }


def component_source(case: ComponentCase, marker: str, variant: str) -> tuple[str, dict[str, dict[str, object]]]:
    """Emit one variant; the caller uses one query to fit the capped output."""

    if variant not in ("candidate", "reference"):
        raise ValueError(f"unknown component variant: {variant}")

    ctext = render_constraints(case.constraints, case.n)
    query_rows: dict[str, dict[str, object]] = {}
    for a, b in case.queries:
        reference, satisfiable = python_instance(case.n, case.constraints, a, b)
        key = f"{case.name}|{a}|{b}"
        query_rows[key] = {
            "reference": instance_encoding(reference),
            "satisfiable": bool(satisfiable),
            "state_count": len(reference.delta),
        }
    prelude = f'''import Subtail.SummaryInstanceCached
import Subtail.EntailmentPrepared
import Subtail.SummaryAutomaton
import Subtail.CanonicalReachability
open Subtail
open Subtail.TreeSemantics
open Subtail.StackSummary
open Subtail.SummaryAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def optionCode {{k : Nat}} : Option (Fin k) -> String
  | none => "-1"
  | some q => toString q.val

def bitCode (b : Bool) : String := if b then "1" else "0"

def emitInstance {{k : Nat}} (tag : String) (I : Subtail.Instance k) : IO Unit := do
  let transitions := (List.finRange k).flatMap (fun q =>
    [optionCode (Subtail.step I q false), optionCode (Subtail.step I q true)])
  let bad := (List.finRange k).map (fun q => bitCode (I.bad.get q))
  let finals := (List.finRange k).map (fun q => bitCode (I.final.get q))
  let flags := (List.finRange k).flatMap (fun p =>
    (List.finRange k).map (fun q => bitCode ((I.flags.get p).get q)))
  IO.println ("{marker}" ++ tag ++ "|" ++ toString I.initial.val ++ "|" ++
    String.intercalate "," transitions ++ "|" ++ String.intercalate "" bad ++ "|" ++
    String.intercalate "" finals ++ "|" ++ String.intercalate "" flags)

def C : List (Constraint {case.n}) := {ctext}
'''
    body = ["def main : IO Unit := do"]
    if variant == "candidate":
        body.extend([
            "  let M := Subtail.CanonicalReachability.systemOf C",
            "  let P := Subtail.EntailmentPrepared.prepare M",
        ])
    for a, b in case.queries:
        key = f"{case.name}|{a}|{b}"
        fin_a = decision.fin(a, case.n)
        fin_b = decision.fin(b, case.n)
        if variant == "candidate":
            body.append(f'  emitInstance "candidate|{key}" (Subtail.SummaryInstanceCached.summaryInstance C P.machine P.cache {fin_a} {fin_b})')
        else:
            body.append(f'  emitInstance "reference|{key}" (Subtail.SummaryAutomaton.summaryInstance C {fin_a} {fin_b})')
    body.append("\n#eval main")
    return prelude + "\n".join(body) + "\n", query_rows


def parse_instance_marker(marker: str, prefix: str) -> tuple[str, dict[str, object]]:
    if not marker.startswith(prefix):
        raise ValueError("wrong marker prefix")
    body = marker[len(prefix) :]
    fields = body.split("|")
    if len(fields) < 6:
        raise ValueError("missing instance fields")
    tag = "|".join(fields[:-5])
    initial, transitions, bad, finals, flags = fields[-5:]
    parsed = {
        "initial": int(initial),
        "transitions": [int(value) for value in transitions.split(",") if value],
        "bad": bad,
        "final": finals,
        "flags": flags,
    }
    return tag, parsed


def compare_instance(actual: dict[str, object], expected: dict[str, object]) -> Optional[str]:
    for field in ("initial", "transitions", "bad", "final", "flags"):
        if actual.get(field) != expected.get(field):
            return field
    return None


def component_phase(
    cases: list[ComponentCase], timeout: float, scratch: Path
) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for case in cases:
        marker = COMPONENT_MARKER + case.name + ":"
        expected: dict[str, dict[str, object]] = {}
        processes: list[dict[str, object]] = []
        for a, b in case.queries:
            for variant in ("candidate", "reference"):
                source, query_expected = component_source(replace(case, queries=((a, b),)), marker, variant)
                expected.update(query_expected)
                path = scratch / f"component-{case.name}-{a}-{b}-{variant}.lean"
                process = run_marked(source, path, marker, timeout, expected_markers=1)
                process.update(query=[a, b], variant=variant)
                processes.append(process)
        statuses = [process.get("status", "FAIL") for process in processes]
        run: dict[str, object] = {
            "status": "FAIL" if "FAIL" in statuses else "UNKNOWN" if "UNKNOWN" in statuses else "PASS",
            "process_scope": "One query and one variant per capped process",
            "processes": processes,
            "markers": [item for process in processes for item in process.get("markers", [])],
        }
        by_tag: dict[str, dict[str, object]] = {}
        parse_error: Optional[str] = None
        if run.get("status") == "PASS":
            for raw_marker in run.get("markers", []):
                try:
                    tag, value = parse_instance_marker(raw_marker, marker)
                except (TypeError, ValueError) as error:
                    parse_error = f"malformed_instance_marker:{error}"
                    break
                if tag in by_tag:
                    parse_error = f"duplicate_instance_marker:{tag}"
                    break
                by_tag[tag] = value
        if parse_error:
            run.update(status="FAIL", reason=parse_error)
        component_rows: list[dict[str, object]] = []
        if run.get("status") == "PASS":
            for key, wanted in expected.items():
                candidate_tag = f"candidate|{key}"
                reference_tag = f"reference|{key}"
                candidate = by_tag.get(candidate_tag)
                reference = by_tag.get(reference_tag)
                row: dict[str, object] = {
                    "name": key,
                    "state_count": wanted["state_count"],
                    "independent_satisfiable": wanted["satisfiable"],
                    "candidate_present": candidate is not None,
                    "reference_present": reference is not None,
                }
                if candidate is None or reference is None:
                    row.update(status="FAIL", reason="missing_instance_marker")
                else:
                    candidate_field = compare_instance(candidate, reference)
                    python_field = compare_instance(candidate, wanted["reference"])
                    row.update(
                        status="PASS" if candidate_field is None and python_field is None else "FAIL",
                        candidate_reference_field=candidate_field,
                        candidate_python_field=python_field,
                        exact_fields=("initial", "transitions", "bad", "final", "flags"),
                    )
                    if candidate_field is not None:
                        row["reason"] = "candidate_reference_disagreement"
                    elif python_field is not None:
                        row["reason"] = "independent_python_disagreement"
                component_rows.append(row)
        else:
            component_rows = [
                {
                    "name": key,
                    "state_count": value["state_count"],
                    "independent_satisfiable": value["satisfiable"],
                    "status": run.get("status", "UNKNOWN"),
                    "reason": run.get("reason", "process_not_completed"),
                }
                for key, value in expected.items()
            ]
        if any(row.get("status") == "FAIL" for row in component_rows):
            phase_status = "FAIL"
        elif any(row.get("status") == "UNKNOWN" for row in component_rows):
            phase_status = "UNKNOWN"
        else:
            phase_status = "PASS"
        rows.append(
            {
                "name": case.name,
                "n": case.n,
                "tags": list(case.tags),
                "query_count": len(case.queries),
                "status": phase_status,
                "native": run,
                "rows": component_rows,
            }
        )
        print(f"{case.name}: {phase_status}", flush=True)
    return {
        "status": (
            "FAIL"
            if any(row["status"] == "FAIL" for row in rows)
            else "UNKNOWN"
            if any(row["status"] == "UNKNOWN" for row in rows)
            else "PASS"
        ),
        "case_count": len(rows),
        "instance_count": sum(row["query_count"] for row in rows),
        "exact_fields": ["initial", "transitions", "bad", "final", "flags"],
        "oracle": "Independent P-automaton predecessor saturation in check_subtype_summary.reference",
        "process_count": sum(len(row["native"]["processes"]) for row in rows),
        "process_scope": "One query and one variant per capped process; case totals are not solver timings",
        "rows": rows,
        "limitation": "Reference equality and Python agreement are finite validation evidence; they do not prove the all-input Lean equality theorem.",
    }


def full38_phase(timeout: float, scratch: Path, compare_baseline: bool) -> dict[str, object]:
    """Optional E054 reuse with the new raw endpoints and old nonraw renderer."""

    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    variants = ("baseline", "candidate") if compare_baseline else ("candidate",)
    rows: list[dict[str, object]] = []
    for fixture in fixtures:
        row: dict[str, object] = {"name": fixture.name, "kind": fixture.kind, "expected": fixture.expected, "variants": {}}
        for variant in variants:
            if fixture.kind == "raw":
                marker = f"{RAW_MARKER}full38-{variant}:{fixture.name}:"
                source, endpoint = raw_source(fixture, variant, marker)
            else:
                prepared_variant = "baseline" if variant == "baseline" else "prepared"
                source, endpoint, _ = prepared.prepared_benchmark_source(fixture, prepared_variant)
                marker = f"{prepared.BENCHMARK_MARKER}{prepared_variant}:{fixture.name}:"
            run = run_marked(source, scratch / f"full38-{fixture.name}-{variant}.lean", marker, timeout)
            check_raw_run(run, marker, fixture.expected)
            run["endpoint"] = endpoint
            row["variants"][variant] = run
        if compare_baseline:
            before = row["variants"]["baseline"]
            after = row["variants"]["candidate"]
            if before.get("status") == after.get("status") == "PASS" and before.get("actual") != after.get("actual"):
                row["disagreement"] = True
        rows.append(row)
    statuses = [value.get("status") for row in rows for value in row["variants"].values()]
    return {
        "status": "FAIL" if any(status == "FAIL" for status in statuses) or any(row.get("disagreement") for row in rows) else "UNKNOWN" if any(status == "UNKNOWN" for status in statuses) else "PASS",
        "fixture_count": len(rows),
        "variants": list(variants),
        "rows": rows,
        "limitation": "Nonraw rows reuse the audited E058 renderer; this phase is optional regression evidence and does not prove the cached summary theorem.",
    }


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--raw", action="store_true", help="run the seven fixed E052 raw fixtures")
    ap.add_argument("--stress-raw", action="store_true", help="run E059 n=3/n=4 and separate n=5/n=6 stress rows")
    ap.add_argument("--components", action="store_true", help="run exact cached/reference component checks")
    ap.add_argument("--full38", "--benchmark", dest="full38", action="store_true", help="reuse E054 with the new raw endpoint")
    ap.add_argument("--generated", action="store_true", help="reuse the optional E055 generated phase")
    ap.add_argument("--compare-baseline", action="store_true", help="also run the previous raw endpoint; default is candidate only")
    ap.add_argument("--timeout", type=float, default=TIMEOUT_DEFAULT, help="wall and CPU process cap in seconds")
    ap.add_argument("--output", type=Path, default=ROOT / "tmp/summary-cached-validation.json")
    ap.add_argument("--scratch", type=Path, default=ROOT / "tmp/summary-cached-validation")
    return ap


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser().error("--timeout must be finite and positive")
    if not any((args.raw, args.stress_raw, args.components, args.full38, args.generated)):
        args.raw = True
        args.components = True
    args.scratch = args.scratch.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)

    result: dict[str, object] = {
        "status": "PASS",
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
            "protocol": "lake env lean <source.lean> with #eval main",
            "component_process_scope": "One query and one variant; all queries and both variants retained",
            "variants": list(selected_variants(args.compare_baseline)),
        },
        "source_sha256": source_hashes(),
        "fixture_identity": fixture_identity(),
        "endpoints": {
            "raw_baseline": "Subtail.InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy",
            "raw_candidate": "Subtail.EntailmentPrepared.rawNormalizedEntailsCheck",
            "component_reference": "Subtail.SummaryAutomaton.summaryInstance",
            "component_candidate": "Subtail.SummaryInstanceCached.summaryInstance",
        },
        "phases": {},
        "limitations": [
            "SummaryInstanceCached equality is a parent-owned Lean obligation; this harness compares finite emitted values only.",
            "The independent Python reference is a P-automaton construction, not another reading of candidate output.",
            "Raw endpoint agreement and fixture expectations do not establish subtype entailment completeness.",
            "UNKNOWN is preserved for caps, interruption, or resource-limit ambiguity; ordinary compiler errors and malformed or ambiguous completed markers are FAIL; NOT_READY is preserved for missing parent modules.",
            "The address-space limit is enforced by scripts/subtail.py only on Linux; CPU RLIMIT is rounded up to at least one second.",
        ],
    }

    phase_specs: list[tuple[str, str, object]] = []
    if args.raw:
        phase_specs.append(("raw", "raw", old_raw_fixtures()))
    if args.stress_raw:
        phase_specs.append(("stress_raw", "stress_raw", stress_raw_fixtures()))
    if args.components:
        phase_specs.append(("components", "components", component_cases()))
    if args.full38:
        phase_specs.append(("full38", "full38", None))
    if args.generated:
        phase_specs.append(("generated19", "generated19", None))

    for name, kind, payload in phase_specs:
        missing = missing_modules(kind)
        if missing:
            result["phases"][name] = {"status": "NOT_READY", "missing": missing}
            if result["status"] == "PASS":
                result["status"] = "NOT_READY"
            continue
        if kind in ("raw", "stress_raw"):
            phase = raw_phase(payload, RAW_MARKER + name + "-", args.timeout, args.scratch, args.compare_baseline)
        elif kind == "components":
            phase = component_phase(payload, args.timeout, args.scratch)
        elif kind == "full38":
            phase = full38_phase(args.timeout, args.scratch, args.compare_baseline)
        elif kind == "generated19":
            phase = prepared.generated_phase(args.timeout, args.scratch, args.compare_baseline)
        else:
            raise AssertionError(kind)
        result["phases"][name] = phase
        if phase.get("status") == "FAIL":
            result["status"] = "FAIL"
        elif phase.get("status") == "UNKNOWN" and result["status"] in ("PASS", "NOT_READY"):
            result["status"] = "UNKNOWN"

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "phases": {key: value.get("status") for key, value in result["phases"].items()},
                "output": str(args.output),
            },
            sort_keys=True,
        )
    )
    return 1 if result["status"] == "FAIL" else 0


if __name__ == "__main__":
    raise SystemExit(main())
