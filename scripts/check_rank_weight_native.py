#!/usr/bin/env python3
"""Compile and kernel-replay the additive quantitative proofs on pinned Lean.

Python orchestrates checks; Lean checks all mathematical statements. This does
not alter production imports or execute the full preimage enumerator.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
MODULES = ["RankQueryWeightCounterexample", "RankQueryWeightBound", "RankQueryLengthBound"]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
GENERATED = {"RankQueryWeightBound": ["Estimate.mk", "Estimate.atoms", "Estimate.sizes",
                                      "Estimate.active", "Estimate.activeSizes"],
             "RankQueryLengthBound": ["LengthRun.refl", "LengthRun.step", "LengthRun.rec"]}
COMMANDS: list[dict[str, object]] = []


def run(args: list[str], timeout: int = 900) -> str:
    print("$ " + " ".join(args), flush=True)
    start = time.monotonic()
    result = subprocess.run(args, cwd=LEAN, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=timeout, check=False)
    COMMANDS.append({"command": args, "exit_code": result.returncode,
                     "elapsed_seconds": round(time.monotonic() - start, 3),
                     "wall_timeout_seconds": timeout})
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise RuntimeError(f"Command failed with exit {result.returncode}: {args}")
    return result.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def import_hashes() -> dict[str, str]:
    """Pin every transitive Subtail source dependency, not just the new files."""
    pending = ["Subtail." + name for name in MODULES]
    hashes: dict[str, str] = {}
    while pending:
        module = pending.pop()
        relative = "lean/" + module.replace(".", "/") + ".lean"
        if relative in hashes:
            continue
        path = ROOT / relative
        hashes[relative] = digest(path)
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                pending.extend(x for x in line.split()[1:] if x.startswith("Subtail."))
    return dict(sorted(hashes.items()))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--elaborate-only", action="store_true",
                        help="Use existing dependency oleans and omit C generation; still replay kernel and audit axioms")
    args = parser.parse_args()
    assert (LEAN / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    version = run(["lake", "env", "lean", "--version"], 60).strip()
    assert "4.33.1" in version
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    head = os.environ.get("RANK_WEIGHT_SOURCE_SHA", sha)
    assert head == sha, (head, sha)
    report: dict[str, object] = {
        "source_sha": head, "checkout_sha": sha, "lean": version,
        "python": sys.version, "platform": platform.platform(),
        "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
        "scope": "Lean elaboration, kernel replay, transitive axiom audit",
        "full_lake_build": not args.elaborate_only,
        "source_dependency_sha256": import_hashes(),
        "driver_sha256": digest(Path(__file__)), "modules": {},
        "full_enumerator_executed": False, "large_observer_materialized": False,
        "independent_mathematical_review": False,
    }
    if args.elaborate_only:
        for name in MODULES:
            run(["lake", "env", "lean", "Subtail/" + name + ".lean", "-o",
                 ".lake/build/lib/lean/Subtail/" + name + ".olean"])
    else:
        run(["lake", "build", *("+Subtail." + name for name in MODULES)])
    for name in MODULES:
        path = LEAN / "Subtail" / f"{name}.lean"
        code = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        assert not re.search(r"\b(sorry|sorryAx|axiom|native_decide|unsafe)\b|decide\s*\+native", code)
        parsed = re.findall(r"^(theorem|def|abbrev|structure|inductive)\s+([A-Za-z_][A-Za-z_0-9.]*)", code, re.M)
        declarations = [decl for _, decl in parsed] + GENERATED.get(name, [])
        assert declarations and len(set(declarations)) == len(declarations)
        runtime = {"Subtail." + name + "." + decl for kind, decl in parsed if kind in {"def", "abbrev"}}
        run(["lake", "env", "leanchecker", "Subtail." + name], 600)
        with tempfile.TemporaryDirectory(prefix="rank-weight-audit-", dir=ROOT) as temp:
            audit = Path(temp) / "Audit.lean"
            audit.write_text("import Subtail." + name + "\n" + "\n".join(
                "#print axioms Subtail." + name + "." + decl for decl in declarations) + "\n")
            output = run(["lake", "env", "lean", str(audit)], 300)
        entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
        expected = {"Subtail." + name + "." + decl for decl in declarations}
        assert {decl for decl, _ in entries} == expected
        assert len(entries) == len(declarations)
        for decl, raw in entries:
            deps = {dep.strip() for dep in raw.split(",") if dep.strip()}
            assert deps <= ALLOWED, (decl, deps - ALLOWED)
            if decl in runtime:
                assert "Classical.choice" not in deps, decl
        report["modules"][name] = {  # type: ignore[index]
            "status": "PASS", "sha256": digest(path), "declarations_audited": len(declarations),
            "runtime_definitions_choice_free": True,
            "dependencies": {decl: sorted(dep.strip() for dep in raw.split(",") if dep.strip())
                             for decl, raw in entries}}
    report["commands"] = COMMANDS
    report["status"] = "PASS"
    out = ROOT / "tmp" / "rank-weight-native.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
