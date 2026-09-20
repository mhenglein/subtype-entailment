#!/usr/bin/env python3
"""Bounded differential checks for the streamed C029 raw backend.

The fixed raw corpus compares the original ``TerminalDecisionLazy`` endpoint
with the new ``InfiniteDecisionLazy`` endpoint.  Component probes compare the
two C029 Boolean implementations directly on named adversarial instances.
The optional full and generated phases reuse the already audited E058 driver
for the prepared nonraw endpoints.

This is validation evidence, not a replacement for the Lean equality or
semantic theorems.  A process cap, interruption, unavailable tool, or missing
module is never turned into a Boolean answer.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, is_dataclass
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

import check_absorbing_terminal as absorbing_oracle  # noqa: E402
import check_entailment_decision as decision  # noqa: E402
import check_fast_summary as fast  # noqa: E402
import check_finishing_trace as trace_oracle  # noqa: E402
import check_infinite_decision as infinite_oracle  # noqa: E402
import check_prepared_summary as prepared  # noqa: E402
from check_terminal_decision import PREAMBLE as INSTANCE_DECODER  # noqa: E402


SEED = 2026092020
TIMEOUT_DEFAULT = 20.0
RAW_MARKER = "SUBTAIL_INFINITE_LAZY_RAW:"
COMPONENT_MARKER = "SUBTAIL_INFINITE_LAZY_COMPONENT:"
STRESS_MARKER = "SUBTAIL_INFINITE_LAZY_STRESS:"
LAZY_MODULE = "lean/Subtail/InfiniteDecisionLazy.lean"
PREPARED_MODULE = "lean/Subtail/EntailmentPrepared.lean"


@dataclass(frozen=True)
class ComponentCase:
    name: str
    instance: trace_oracle.Instance
    expected: Optional[bool]
    oracle: str
    semantic_scope: str


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
        "experiments/check_infinite_decision.py",
        "experiments/check_absorbing_terminal.py",
        "experiments/check_finishing_trace.py",
        "experiments/check_prepared_summary.py",
        "experiments/check_terminal_decision.py",
        "experiments/check_infinite_lazy.py",
        "lean/Subtail/InfiniteDecision.lean",
        "lean/Subtail/InfiniteDecisionLazy.lean",
        "lean/Subtail/TerminalDecisionLazy.lean",
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


def fixture_identity() -> dict[str, object]:
    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    raw = [fixture for fixture in fixtures if fixture.kind == "raw"]
    if len(raw) != 7:
        raise AssertionError(f"expected seven raw fixtures, found {len(raw)}")
    generated = prepared.generated_cases()
    components = component_cases()
    payload = {
        "e054_all": [normalize(fixture) for fixture in fixtures],
        "e052_raw": [normalize(fixture) for fixture in raw],
        "e055_generated": [normalize(case) for case in generated],
        "component_cases": [
            {
                "name": case.name,
                "instance": normalize(case.instance),
                "expected": case.expected,
                "semantic_scope": case.semantic_scope,
            }
            for case in components
        ],
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return {
        "e054_all_count": len(fixtures),
        "e054_all_names": [fixture.name for fixture in fixtures],
        "e052_raw_count": len(raw),
        "e052_raw_names": [fixture.name for fixture in raw],
        "e055_generated_count": len(generated),
        "e055_generated_names": [case.name for case in generated],
        "component_count": len(components),
        "component_names": [case.name for case in components],
        "sha256": sha256_bytes(encoded),
    }


def missing_modules(kind: str) -> list[str]:
    required = {
        "raw": [
            "lean/Subtail/InfiniteDecision.lean",
            "lean/Subtail/TerminalDecisionLazy.lean",
            LAZY_MODULE,
        ],
        "components": [
            "lean/Subtail/InfiniteDecision.lean",
            LAZY_MODULE,
        ],
        "stress_raw": [
            "lean/Subtail/TerminalDecisionLazy.lean",
            LAZY_MODULE,
        ],
        "full38": [
            "lean/Subtail/EntailmentFast.lean",
            "lean/Subtail/TerminalDecisionLazy.lean",
            PREPARED_MODULE,
            LAZY_MODULE,
        ],
        "generated19": [
            "lean/Subtail/EntailmentFast.lean",
            PREPARED_MODULE,
        ],
    }[kind]
    return [name for name in required if not (ROOT / name).is_file()]


def render_bool_source(
    marker: str,
    call: str,
    imports: Iterable[str],
    prelude: str = "",
) -> str:
    import_text = "\n".join(f"import {item}" for item in imports)
    return f'''{import_text}
{prelude}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO Unit := do
  let actual : Bool := {call}
  IO.println ("{marker}" ++ (if actual then "true" else "false"))

#eval main
'''


def raw_source(fixture: decision.Fixture, variant: str, marker: str) -> tuple[str, str]:
    if fixture.kind != "raw":
        raise ValueError("raw_source requires a raw fixture")
    if variant == "baseline":
        module = "Subtail.TerminalDecisionLazy"
        function = "Subtail.TerminalDecisionLazy.rawNormalizedEntailsCheckLazy"
    elif variant == "candidate":
        module = "Subtail.InfiniteDecisionLazy"
        function = "Subtail.InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy"
    else:
        raise ValueError(f"unknown raw variant: {variant}")
    call = (
        f"{function} {decision.render_constraints(fixture)} "
        f"{decision.fin(int(fixture.a), fixture.n)} "
        f"{decision.fin(int(fixture.b), fixture.n)}"
    )
    source = render_bool_source(marker, call, [module])
    return source, function


def raw_stress_fixtures() -> list[decision.Fixture]:
    return [
        decision.raw(
            "empty-n3-query-0-1",
            3,
            (),
            0,
            1,
            False,
            "root-bottom-countermodel",
            "The empty premise set permits variable 0 to be root-only and variable 1 to be bottom.",
            "stress",
        ),
        decision.raw(
            "empty-n4-query-0-1",
            4,
            (),
            0,
            1,
            False,
            "root-bottom-countermodel",
            "The empty premise set permits variable 0 to be root-only and variable 1 to be bottom.",
            "stress",
        ),
    ]


def encode_instance(instance: trace_oracle.Instance) -> tuple[int, tuple[int, int, int, int, int]]:
    k = len(instance.delta)
    transition_code = sum(
        (target if target >= 0 else k) * (k + 1) ** (2 * state + letter)
        for state, row in enumerate(instance.delta)
        for letter, target in enumerate(row)
    )
    return k, (
        instance.initial,
        transition_code,
        sum(1 << state for state in instance.finals),
        sum(1 << state for state in instance.bad),
        sum(1 << (p * k + q) for p, q in instance.flags),
    )


def component_source(case: ComponentCase, variant: str, marker: str) -> tuple[str, str]:
    k, (start, transitions, finals, bad, flags) = encode_instance(case.instance)
    if variant == "baseline":
        module = "Subtail.InfiniteDecision"
        function = "Subtail.InfiniteDecision.infiniteWitnessCheck"
    elif variant == "candidate":
        module = "Subtail.InfiniteDecisionLazy"
        function = "Subtail.InfiniteDecisionLazy.infiniteWitnessCheckLazy"
    else:
        raise ValueError(f"unknown component variant: {variant}")
    # The existing decoder is the same finite Instance representation used by
    # the exhaustive C029 harness.  A later option line removes its auxiliary
    # heartbeat cap; the process cap remains the recorded acceptance boundary.
    prelude = (
        INSTANCE_DECODER
        + "\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    )
    call = (
        f"{function} (decoded {k} (by decide) {start} {transitions} "
        f"{finals} {bad} {flags})"
    )
    return render_bool_source(marker, call, [module], prelude), function


def component_cases() -> list[ComponentCase]:
    cases: list[ComponentCase] = []
    for name, k, data in infinite_oracle.fixtures():
        start, transitions, finals, bad, flags, expected = data
        instance = absorbing_oracle.decoded(k, start, transitions, finals, bad, flags)
        if not absorbing_oracle.absorbing(instance):
            raise AssertionError(f"known fixture is not absorbing: {name}")
        cases.append(
            ComponentCase(
                name=f"known-{name}",
                instance=instance,
                expected=bool(expected),
                oracle="existing check_infinite_decision named C029 guard",
                semantic_scope="absorbing; named independent guard only",
            )
        )

    bad_initial = trace_oracle.Instance(
        ((0, 0),), 0, frozenset({0}), frozenset({0}), frozenset()
    )
    diagonal_unsafe = trace_oracle.Instance(
        ((0, 0),), 0, frozenset({0}), frozenset(), frozenset({(0, 0)})
    )
    safe_no_witness = trace_oracle.Instance(
        ((-1, -1),), 0, frozenset(), frozenset(), frozenset()
    )
    missing_transition = trace_oracle.Instance(
        ((1, -1), (-1, -1)), 0, frozenset({1}), frozenset(), frozenset()
    )
    stem_cycle = trace_oracle.Instance(
        ((1, -1), (2, -1), (2, -1)), 0, frozenset({2}), frozenset(), frozenset()
    )
    nonabsorbing_exit = trace_oracle.Instance(
        ((1, -1), (-1, -1)), 0, frozenset({0}), frozenset(), frozenset()
    )
    nonabsorbing_flagged = trace_oracle.Instance(
        ((1, -1), (-1, -1)), 0, frozenset({0, 1}), frozenset(), frozenset({(0, 1)})
    )

    if not absorbing_oracle.absorbing(stem_cycle):
        raise AssertionError("stem-cycle probe should be absorbing")
    if not trace_oracle.literal_witness(stem_cycle, "00"):
        raise AssertionError("stem-cycle probe lost its independent finite stem")
    if 2 not in absorbing_oracle.infinite_endpoints(stem_cycle):
        raise AssertionError("stem-cycle probe lost its independent safe cycle")
    if absorbing_oracle.infinite_endpoints(missing_transition):
        raise AssertionError("missing-transition probe unexpectedly has a safe cycle")

    cases.extend(
        [
            ComponentCase(
                "bad-initial",
                bad_initial,
                False,
                "safeCheck at the initial cut is false",
                "absorbing; direct necessary-condition guard",
            ),
            ComponentCase(
                "diagonal-unsafe-initial",
                diagonal_unsafe,
                False,
                "the initial cut compares with itself and is diagonally flagged",
                "nonabsorbing; direct initial-safety guard and Boolean equality only",
            ),
            ComponentCase(
                "initial-safe-but-no-witness",
                safe_no_witness,
                False,
                "there is no final state, so no Witness endpoint exists",
                "absorbing; direct finite-state guard",
            ),
            ComponentCase(
                "missing-transition-no-cycle",
                missing_transition,
                False,
                "independent safe-transition closure has no cyclic endpoint",
                "absorbing; independent graph guard",
            ),
            ComponentCase(
                "stem-cycle-positive",
                stem_cycle,
                True,
                "literal witness 00 reaches an independently detected safe cycle",
                "absorbing; independent witness plus graph guard",
            ),
            ComponentCase(
                "nonabsorbing-final-exit",
                nonabsorbing_exit,
                None,
                "final state has a successor outside the final set",
                "nonabsorbing; Boolean equality only, no InfWitness semantic claim",
            ),
            ComponentCase(
                "nonabsorbing-flagged-final-column",
                nonabsorbing_flagged,
                None,
                "final successor has an incoming flag, violating Absorbing",
                "nonabsorbing; Boolean equality only, no InfWitness semantic claim",
            ),
        ]
    )
    return cases


def run_marked(source: str, path: Path, marker: str, timeout: float) -> dict[str, object]:
    path.write_text(source)
    result = fast.run_generated_source(path, marker, timeout)
    result["generated_source_sha256"] = sha256_bytes(source.encode())
    return result


def selected_variants(compare_baseline: bool) -> tuple[str, ...]:
    return ("baseline", "candidate") if compare_baseline else ("candidate",)


def check_boolean(
    run: dict[str, object],
    marker: str,
    expected: Optional[bool],
    validate_expected: bool = True,
) -> None:
    if run.get("status") != "PASS":
        return
    value = run.get("marker")
    if value == marker + "true":
        actual = True
    elif value == marker + "false":
        actual = False
    else:
        run.update(status="FAIL", reason="missing_or_ambiguous_boolean_marker")
        return
    run["actual"] = actual
    if expected is None and not validate_expected:
        run.update(status="UNKNOWN", reason="no_independent_semantic_oracle")
    elif expected is not None and actual != expected:
        run.update(status="FAIL", reason="independent_expected_answer_mismatch")


def aggregate_status(rows: list[dict[str, object]]) -> str:
    statuses = [
        variant.get("status", "FAIL")
        for row in rows
        for variant in row.get("variants", {}).values()
        if isinstance(variant, dict)
    ]
    if any(status == "FAIL" for status in statuses) or any(
        row.get("disagreement") for row in rows
    ):
        return "FAIL"
    if any(status == "UNKNOWN" for status in statuses):
        return "UNKNOWN"
    return "PASS"


def differential_phase(
    cases: list[ComponentCase],
    marker_base: str,
    timeout: float,
    scratch: Path,
    compare_baseline: bool,
) -> dict[str, object]:
    variants = selected_variants(compare_baseline)
    rows: list[dict[str, object]] = []
    for case in cases:
        row: dict[str, object] = {
            "name": case.name,
            "expected": case.expected,
            "oracle": case.oracle,
            "semantic_scope": case.semantic_scope,
            "absorbing": absorbing_oracle.absorbing(case.instance),
            "variants": {},
        }
        for variant in variants:
            marker = f"{marker_base}{variant}:{case.name}:"
            source, endpoint = component_source(case, variant, marker)
            run = run_marked(
                source,
                scratch / f"component-{case.name}-{variant}.lean",
                marker,
                timeout,
            )
            check_boolean(run, marker, case.expected, validate_expected=compare_baseline)
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
                row["reason"] = "baseline_candidate_disagreement"
        rows.append(row)
        print(
            f"{case.name}: "
            + "; ".join(
                f"{variant} {row['variants'][variant].get('status')}"
                for variant in variants
            ),
            flush=True,
        )
    return {
        "status": aggregate_status(rows),
        "case_count": len(rows),
        "variants": list(variants),
        "rows": rows,
        "unknown_is_not_no": True,
        "limitation": "Nonabsorbing rows test only the unconditional Boolean equality; no InfWitness semantic claim is made there.",
    }


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
            "kind": fixture.kind,
            "expected": fixture.expected,
            "justification": fixture.justification,
            "true_means": "entailment",
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
            check_boolean(run, marker, fixture.expected)
            run["endpoint"] = endpoint
            run["raw_backend_unchanged"] = variant == "baseline"
            row["variants"][variant] = run
        if compare_baseline:
            baseline = row["variants"]["baseline"]
            candidate = row["variants"]["candidate"]
            if (
                baseline.get("status") == candidate.get("status") == "PASS"
                and baseline.get("actual") != candidate.get("actual")
            ):
                row["disagreement"] = True
                row["reason"] = "baseline_candidate_disagreement"
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
        "baseline_endpoint": "Subtail.TerminalDecisionLazy.rawNormalizedEntailsCheckLazy",
        "candidate_endpoint": "Subtail.InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy",
        "unknown_is_not_no": True,
        "limitation": "The raw equality theorem is the unconditional target; fixture expectations are independent corpus checks.",
    }


def full38_phase(timeout: float, scratch: Path, compare_baseline: bool) -> dict[str, object]:
    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    raw = raw_phase(
        [fixture for fixture in fixtures if fixture.kind == "raw"],
        RAW_MARKER + "full38-",
        timeout,
        scratch,
        compare_baseline,
    )
    rows: list[dict[str, object]] = []
    failures: list[str] = []
    disagreements: list[str] = []
    for fixture in fixtures:
        if fixture.kind == "raw":
            continue
        row: dict[str, object] = {
            "name": fixture.name,
            "kind": fixture.kind,
            "expected": fixture.expected,
            "justification": fixture.justification,
            "variants": {},
        }
        variants = ("baseline", "prepared") if compare_baseline else ("prepared",)
        for variant in variants:
            source, endpoint, unchanged = prepared.prepared_benchmark_source(fixture, variant)
            marker = f"{prepared.BENCHMARK_MARKER}{variant}:{fixture.name}:"
            run = run_marked(
                source,
                scratch / f"full38-{fixture.name}-{variant}.lean",
                marker,
                timeout,
            )
            check_boolean(run, marker, fixture.expected)
            run.update(endpoint=endpoint, raw_backend_unchanged=unchanged)
            row["variants"][variant] = run
            if run.get("status") == "FAIL":
                failures.append(f"{fixture.name}:{variant}")
        if compare_baseline:
            baseline = row["variants"]["baseline"]
            candidate = row["variants"]["prepared"]
            if (
                baseline.get("status") == candidate.get("status") == "PASS"
                and baseline.get("actual") != candidate.get("actual")
            ):
                disagreements.append(fixture.name)
                row["disagreement"] = True
        rows.append(row)
    nonraw = {
        "status": "FAIL"
        if failures or disagreements
        else "UNKNOWN"
        if any(
            row["variants"][variant].get("status") == "UNKNOWN"
            for row in rows
            for variant in (("baseline", "prepared") if compare_baseline else ("prepared",))
        )
        else "PASS",
        "fixture_count": len(rows),
        "variants": list(("baseline", "prepared") if compare_baseline else ("prepared",)),
        "rows": rows,
        "baseline_prepared_disagreements": disagreements,
        "failures": failures,
        "candidate_endpoint": "Subtail.EntailmentPrepared.entailsCheck or normalizedEntailsCheck",
    }
    statuses = [raw["status"], nonraw["status"]]
    return {
        "status": "FAIL"
        if "FAIL" in statuses
        else "UNKNOWN"
        if "UNKNOWN" in statuses
        else "PASS",
        "fixture_count": len(fixtures),
        "raw_count": raw["fixture_count"],
        "nonraw_count": nonraw["fixture_count"],
        "raw": raw,
        "nonraw_prepared": nonraw,
        "limitation": "Raw rows use InfiniteDecisionLazy directly; nonraw rows use the existing E058 prepared endpoint. No equality or completeness claim is inferred from agreement.",
    }


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--components", action="store_true", help="run direct C029 adversarial instance probes")
    ap.add_argument("--raw", action="store_true", help="run the seven fixed E052 raw fixtures")
    ap.add_argument("--stress-raw", action="store_true", help="run separate n=3/n=4 empty-constraint raw probes")
    ap.add_argument("--full38", "--benchmark", dest="full38", action="store_true", help="run all 38 fixtures, with prepared nonraw rows")
    ap.add_argument("--generated", action="store_true", help="run the optional 19-case E055 prepared comparison")
    ap.add_argument("--compare-baseline", action="store_true", help="also run unchanged baseline endpoints; default is candidate only")
    ap.add_argument("--timeout", type=float, default=TIMEOUT_DEFAULT, help="wall and CPU process cap in seconds")
    ap.add_argument("--output", type=Path, default=ROOT / "tmp/infinite-lazy-validation.json")
    ap.add_argument("--scratch", type=Path, default=ROOT / "tmp/infinite-lazy-validation")
    return ap


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser().error("--timeout must be finite and positive")
    if not any((args.components, args.raw, args.stress_raw, args.full38, args.generated)):
        args.raw = True
    args.scratch = args.scratch.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)

    fixtures = decision.corpus()
    decision.validate_corpus(fixtures)
    raw = [fixture for fixture in fixtures if fixture.kind == "raw"]
    if len(raw) != 7:
        raise AssertionError(f"expected seven raw fixtures, found {len(raw)}")
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
            "variants": list(selected_variants(args.compare_baseline)),
        },
        "source_sha256": source_hashes(),
        "fixture_identity": fixture_identity(),
        "phases": {},
        "limitations": [
            "infiniteWitnessCheckLazy equality and rawNormalizedEntailsCheckLazy equality are Lean obligations, not conclusions from this harness",
            "the C029 semantic correctness theorem remains conditional on Absorbing; nonabsorbing component rows test Boolean equality only",
            "a baseline/candidate agreement is a regression result, not completeness or a performance claim",
            "UNKNOWN is preserved for caps, interruption, launch/tool failure and resource ambiguity; it is never treated as false",
            "the address-space cap is enforced by scripts/subtail.py only on Linux; CPU RLIMIT is rounded up to at least one second",
            "full38 and generated phases reuse the reviewed E058 source generator and do not duplicate its algorithm",
        ],
    }

    phase_specs: list[tuple[str, str, object]] = []
    if args.components:
        phase_specs.append(("components", "components", component_cases()))
    if args.raw:
        phase_specs.append(("raw", "raw", raw))
    if args.stress_raw:
        phase_specs.append(("stress_raw", "stress_raw", raw_stress_fixtures()))
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
        if kind == "components":
            phase = differential_phase(
                payload, COMPONENT_MARKER, args.timeout, args.scratch, args.compare_baseline
            )
        elif kind == "raw":
            phase = raw_phase(
                payload, RAW_MARKER, args.timeout, args.scratch, args.compare_baseline
            )
        elif kind == "stress_raw":
            phase = raw_phase(
                payload, STRESS_MARKER, args.timeout, args.scratch, args.compare_baseline
            )
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
                "phases": {
                    key: value.get("status") for key, value in result["phases"].items()
                },
                "output": str(args.output),
            },
            sort_keys=True,
        )
    )
    return 1 if result["status"] == "FAIL" else 0


if __name__ == "__main__":
    raise SystemExit(main())
