#!/usr/bin/env python3
"""Build and audit the primitive-table C081 solver representation.

Build and kernel-replay the pinned module first. Check every named declaration's transitive axiom
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
MODULES = {name: "Subtail." + name + "." for name in
           ("EntailmentPrepared",)}
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z_0-9.']*)", re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/prepared-summary-axioms.json")
    args = parser.parse_args()
    version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT / "lean", text=True).strip()
    if "version 4.33.1," not in version:
        raise RuntimeError("Use pinned Lean 4.33.1: " + version)
    for command in (["lake", "build", "+Subtail.EntailmentPrepared"],
                    ["lake", "env", "leanchecker", "Subtail.EntailmentPrepared"]):
        proc = subprocess.run(command, cwd=ROOT / "lean", text=True, capture_output=True)
        if proc.returncode:
            raise RuntimeError(proc.stdout + proc.stderr)
    expected = {}
    hashes = {}
    for module, namespace in MODULES.items():
        path = ROOT / "lean/Subtail" / (module + ".lean")
        source = path.read_text()
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        if re.search(r"\b(sorry|sorryAx|native_decide|implemented_by)\b|^\s*(axiom|opaque|noncomputable|private|unsafe)\s", source, re.M):
            raise RuntimeError("Unexpected trusted, unfinished, hidden or noncomputable declaration: " + str(path))
        rows = DECL.findall(source)
        if not rows:
            raise RuntimeError("No declarations found: " + str(path))
        for kind, name in rows:
            full = name if name == "main" else namespace + name
            if full in expected:
                raise RuntimeError("Duplicate declaration: " + full)
            expected[full] = kind
    required = {"Subtail.EntailmentPrepared." + name for name in (
        "materialize_eq", "prepare_eq", "satCheck_eq", "separationCheck_eq",
        "afterPositive_eq", "normalizedWithPaths_eq", "normalizedEntailsCheck_eq",
        "entailsCheck_eq_fast", "entailsCheck_correct", "entailsCheck_eq")}
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
    result = {"status": "PASS", "declarations": reports, "source_sha256": hashes,
              "checked_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "toolchain": version, "build": "PASS", "kernel_replay": "PASS",
              "runtime_declarations": sum(kind != "theorem" for kind in expected.values()),
              "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    runtime = sum(kind != "theorem" for kind in expected.values())
    print(f"PASS: {len(reports)} complete declaration closures, {runtime} non-theorems; no Classical.choice in executable definitions")


if __name__ == "__main__":
    main()
