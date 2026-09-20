#!/usr/bin/env python3
"""Compare forced raw-summary phases; these are diagnostic, not benchmark times."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import platform
import sys

import check_entailment_decision as decision
import check_fast_summary as fast
import profile_raw_backend as profile

ROOT = Path(__file__).resolve().parents[1]


def corpus():
    return [decision.Fixture(
        f"raw-empty-{n}", "raw", n, False, "root_only_countermodel",
        "Variable 0 has only a product root; all other variables are bottom.",
        ("raw", "summary-stress"), a=0, b=1) for n in (3, 4, 5, 6)]


def source(fixture, variant):
    if variant not in ("reference", "cached"):
        raise ValueError("unknown variant")
    code = profile.source(fixture, "gated").replace(
        "import Subtail.TerminalDecisionLazy", "import Subtail.EntailmentPrepared")
    code = code.replace("infiniteStream I", "InfiniteDecisionLazy.infiniteWitnessCheckLazy I")
    if variant == "cached":
        needle = "(fun _ => summaryInstance C "
        if code.count(needle) != 1:
            raise ValueError("reference summary marker changed")
        code = code.replace(needle,
            "(fun _ => let P := EntailmentPrepared.prepare (systemOf C); "
            "SummaryInstanceCached.summaryInstance C P.machine P.cache ")
    return code


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--variant", choices=("reference", "cached"), required=True)
    ap.add_argument("--case", choices=[f.name for f in corpus()], action="append")
    ap.add_argument("--timeout", type=float, default=20)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--scratch", type=Path, required=True)
    args = ap.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        ap.error("timeout must be positive and finite")
    args.scratch = args.scratch.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)
    hashes = fast.source_hashes()
    for name in ("experiments/profile_raw_summary.py", "experiments/profile_raw_backend.py",
                 "experiments/check_fast_summary.py", "experiments/check_entailment_decision.py"):
        hashes[name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    result = {"revision": fast.git_revision(), "variant": args.variant,
              "system": platform.platform(), "source_hashes": hashes,
              "caps": {"wall_seconds": args.timeout, "cpu_seconds": math.ceil(args.timeout),
                       "address_space_gib_linux": 16, "threads": 1, "stack_kib": 32768,
                       "address_space_enforced": sys.platform.startswith("linux")},
              "execution": "lake env lean --run; diagnostic only, matched benchmarks use #eval",
              "timing_boundary": "forced phase output includes printing; cached summary includes preparation",
              "cases": []}
    for fixture in corpus():
        if args.case and fixture.name not in args.case:
            continue
        code = source(fixture, args.variant)
        path = args.scratch / (fixture.name + ".lean")
        path.write_text(code)
        row = {"name": fixture.name, "n": fixture.n, "expected": fixture.expected,
               "justification": fixture.justification,
               "generated_source_sha256": hashlib.sha256(code.encode()).hexdigest(),
               **profile.run(path, args.timeout, fixture.expected)}
        result["cases"].append(row)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
        print(fixture.name, row["status"], row.get("unfinished_phase"), flush=True)
    return int(any(row["status"] == "FAIL" for row in result["cases"]))


if __name__ == "__main__":
    raise SystemExit(main())
