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
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULES = {name: "Subtail." + name + "." for name in
           ("EntailmentPrepared",)}
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z_0-9.']*)", re.M)


def cli_smoke(directory):
    rows = []
    inputs = [("reflexive", {"variables": ["x"], "constraints": [], "query": ["x", "x"]}, "ENTAILED", 20),
              ("zero-variables", {"variables": [], "constraints": [], "query": ["bottom", "bottom"]}, "ENTAILED", 20)]
    for depth in (6, 8):
        left, right = "x", "y"
        for _ in range(depth):
            left, right = {"prod": [left, "bottom"]}, {"prod": [right, "bottom"]}
        inputs.append((f"products-depth-{depth}", {"variables": ["x", "y"], "constraints": [],
                                                   "query": [left, right]}, "NOT_ENTAILED", 20))
    inputs.append(("capped", inputs[0][1], "UNKNOWN", .001))
    for name, problem, expected, timeout in inputs:
        path = directory / (name + ".json")
        path.write_text(json.dumps(problem))
        command = [sys.executable, "scripts/subtail.py", str(path), "--timeout", str(timeout)]
        proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout + 10)
        result = json.loads(proc.stdout)
        expected_exit = 2 if expected == "UNKNOWN" else 0
        if proc.returncode != expected_exit or result["status"] != expected:
            raise RuntimeError(f"CLI mismatch for {name}: {proc.returncode} {proc.stdout} {proc.stderr}")
        if expected != "UNKNOWN" and result.get("basis") != "Lean EntailmentPrepared.entailsCheck_correct":
            raise RuntimeError("CLI did not use the checked prepared endpoint")
        if name.startswith("products-depth-"):
            depth = int(name.rsplit("-", 1)[1])
            model = result.get("countermodel", {})
            if model.get("valid") is not True or model.get("separating_path") != [0] * depth:
                raise RuntimeError("Deep CLI case lacks its independently expected separating path")
        rows.append({"name": name, "expected": expected, "answer": result,
                     "input_sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "timeout": timeout})
    return {"status": "PASS", "cases": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/prepared-summary-axioms.json")
    parser.add_argument("--cli", action="store_true", help="also run the actual default JSON endpoint and cap boundary")
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
    if args.cli:
        directory = args.output.resolve().parent / "prepared-cli"
        directory.mkdir(parents=True, exist_ok=True)
        result["cli"] = cli_smoke(directory)
        result["source_sha256"]["scripts/subtail.py"] = hashlib.sha256((ROOT / "scripts/subtail.py").read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    runtime = sum(kind != "theorem" for kind in expected.values())
    print(f"PASS: {len(reports)} complete declaration closures, {runtime} non-theorems; no Classical.choice in executable definitions")


if __name__ == "__main__":
    main()
