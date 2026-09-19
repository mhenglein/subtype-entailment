#!/usr/bin/env python3
"""Check additive rank-weight proofs without changing the production imports.

Run from the repository root. This invokes the pinned Lean toolchain; Python
only orchestrates compilation, kernel replay and dependency-policy checks.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
MODULES = ["RankQueryWeightCounterexample"]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def run(args: list[str], timeout: int = 900) -> str:
    print("$ " + " ".join(args), flush=True)
    result = subprocess.run(args, cwd=LEAN, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=timeout, check=False)
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise RuntimeError(f"Command failed with exit {result.returncode}: {args}")
    return result.stdout


def main() -> None:
    assert (LEAN / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    version = run(["lake", "env", "lean", "--version"], 60).strip()
    assert "4.33.1" in version
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    head = os.environ.get("RANK_WEIGHT_SOURCE_SHA", sha)
    report = {"source_sha": head, "checkout_sha": sha, "lean": version,
              "scope": "native theorem compilation, kernel replay, transitive axiom audit",
              "modules": {}, "full_enumerator_executed": False,
              "large_observer_materialized": False}
    for name in MODULES:
        path = LEAN / "Subtail" / f"{name}.lean"
        text = path.read_text()
        # Source gate is supplementary to the kernel's transitive dependency audit.
        code = re.sub(r"/-.*?-/", "", text, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        assert not re.search(r"\b(sorry|sorryAx|axiom|native_decide|unsafe)\b|decide\s*\+native", code)
        declarations = re.findall(r"^(?:theorem|def|abbrev)\s+([A-Za-z_][A-Za-z_0-9]*)", code, re.M)
        assert declarations
        run(["lake", "build", "+Subtail." + name])
        run(["lake", "env", "leanchecker", "Subtail." + name], 600)
        with tempfile.TemporaryDirectory(prefix="rank-weight-audit-", dir=ROOT) as temp:
            audit = Path(temp) / "Audit.lean"
            audit.write_text("import Subtail." + name + "\n" + "\n".join(
                "#print axioms Subtail." + name + "." + d for d in declarations) + "\n")
            output = run(["lake", "env", "lean", str(audit)], 300)
        entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
        assert len(entries) == len(declarations), (len(entries), len(declarations))
        for decl, raw in entries:
            deps = {d.strip() for d in raw.split(",") if d.strip()}
            assert deps <= ALLOWED, (decl, deps - ALLOWED)
        report["modules"][name] = {
            "status": "PASS", "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "declarations_audited": len(declarations),
            "dependencies": {decl: [d.strip() for d in raw.split(",") if d.strip()]
                             for decl, raw in entries}}
    out = ROOT / "tmp" / "rank-weight-native.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
