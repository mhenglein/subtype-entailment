#!/usr/bin/env python3
"""Audit the optional equality-proved gated C081 wrapper.

Run after the pinned build. Check every named declaration's transitive axiom
dependencies, including executable definitions and the native audit main.
This does not replace ordinary semantic review or whole-library kernel replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODULES = {"TerminalDecisionLazy": "Subtail.TerminalDecisionLazy."}
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z_0-9.']*)", re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/terminal-lazy-axioms.json")
    args = parser.parse_args()
    expected = {}
    hashes = {}
    for module, namespace in MODULES.items():
        path = ROOT / "lean/Subtail" / (module + ".lean")
        source = path.read_text()
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        if re.search(r"\b(sorry|sorryAx|native_decide)\b|^\s*(axiom|opaque|noncomputable|private)\s", source, re.M):
            raise RuntimeError("Unexpected trusted, unfinished, hidden or noncomputable declaration: " + str(path))
        rows = DECL.findall(source)
        if not rows:
            raise RuntimeError("No declarations found: " + str(path))
        for kind, name in rows:
            full = name if name == "main" else namespace + name
            if full in expected:
                raise RuntimeError("Duplicate declaration: " + full)
            expected[full] = kind
    required = {"Subtail.TerminalDecisionLazy." + name for name in
                ("terminalWitnessCheckLazy_eq", "rawNormalizedEntailsCheckLazy_eq", "normalizedEntailsCheckLazy_eq", "entailsCheckLazy_eq", "entailsCheckLazy_correct")}
    if not required <= expected.keys():
        raise RuntimeError("Missing final executable or correctness declarations")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    scratch = args.output.with_suffix(".lean").resolve()
    scratch.write_text("".join("import Subtail." + m + "\n" for m in MODULES)
                       + "".join("#print axioms " + n + "\n" for n in expected))
    proc = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=ROOT / "lean",
                          text=True, capture_output=True, check=True)
    rows = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])", proc.stdout)
    if len(rows) != len(expected) or {n for n, _, _ in rows} != set(expected):
        raise RuntimeError("Incomplete dependency report:\n" + proc.stdout)
    reports = {}
    for name, _, raw in rows:
        allowed = {"propext", "Quot.sound"}
        if expected[name] == "theorem":
            allowed.add("Classical.choice")
        used = {a.strip() for a in raw.split(",") if a.strip()}
        if not used <= allowed:
            raise RuntimeError(f"Unexpected dependencies: {name}: {sorted(used)}")
        reports[name] = {"kind": expected[name], "axioms": sorted(used)}
    result = {"status": "PASS", "declarations": reports, "source_sha256": hashes}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    runtime = sum(kind != "theorem" for kind in expected.values())
    print(f"PASS: {len(reports)} complete declaration closures, {runtime} non-theorems; no Classical.choice in executable definitions")


if __name__ == "__main__":
    main()
