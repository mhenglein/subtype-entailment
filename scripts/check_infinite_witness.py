#!/usr/bin/env python3
"""Audit the complete C029 executable decision and its proof dependencies.

Run after the pinned Lake build. This checks complete axiom dependencies,
including executable definitions; it does not replace a semantic review.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "PeriodicTail", "InfiniteCycle", "InfiniteWitness",
    "FiniteSearch", "PeriodicRun", "PeriodicRotation", "PeriodicGood",
    "PeriodicMonitor", "PeriodicMonitorComplete", "InfiniteDecision",
)
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z_0-9.']*)", re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/infinite-witness-axioms.json")
    args = parser.parse_args()
    expected = {}
    for module in MODULES:
        path = ROOT / "lean/Subtail" / (module + ".lean")
        source = path.read_text()
        if re.search(r"\b(sorry|sorryAx|native_decide)\b|^\s*(axiom|opaque|noncomputable|private)\s", source, re.M):
            raise RuntimeError("Unexpected trusted, unfinished, hidden, or noncomputable declaration: " + str(path))
        declarations = DECL.findall(source)
        if not declarations:
            raise RuntimeError("No declarations found in " + str(path))
        for kind, name in declarations:
            full = "Subtail." + module + "." + name
            if full in expected:
                raise RuntimeError("Duplicate declaration: " + full)
            expected[full] = kind
    args.output.parent.mkdir(parents=True, exist_ok=True)
    scratch = args.output.with_suffix(".lean").resolve()
    scratch.write_text(
        "".join("import Subtail." + m + "\n" for m in MODULES)
        + "".join("#print axioms " + n + "\n" for n in expected)
    )
    proc = subprocess.run(["lake", "env", "lean", str(scratch)],
                          cwd=ROOT / "lean", text=True, capture_output=True, check=True)
    rows = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])", proc.stdout)
    if len(rows) != len(expected) or {n for n, _, _ in rows} != set(expected):
        raise RuntimeError("Incomplete axiom report:\n" + proc.stdout)
    result = {}
    for name, _, raw in rows:
        allowed = {"propext", "Quot.sound"}
        if expected[name] == "theorem":
            allowed.add("Classical.choice")
        used = {a.strip() for a in raw.split(",") if a.strip()}
        if not used <= allowed:
            raise RuntimeError(f"Unexpected dependencies: {name}: {sorted(used)}")
        result[name] = {"kind": expected[name], "axioms": sorted(used)}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"PASS: {len(result)} named declaration dependency closures; executable definitions have no Classical.choice")


if __name__ == "__main__":
    main()
