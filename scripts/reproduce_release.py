#!/usr/bin/env python3
"""Reproduce a clean project build and selected release checks with pinned tools.

Run in a fresh clone with no lean/.lake directory. The installed toolchain is
reused; this is not an operating-system or toolchain-installation test.
Logs and a machine-readable receipt go to an initially absent directory.
No cache is deleted, no source is changed, and no Git operation writes a ref.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def read(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def c030_audit(output):
    sources = [
        ("TerminalRealization", "Subtail.TerminalRealization"),
        ("TerminalRealizationModel", "Subtail.TerminalRealization"),
        ("TerminalRealizationAudit", "Subtail.TerminalRealization.Audit"),
    ]
    names = []
    for module, prefix in sources:
        source = (ROOT / "lean/Subtail" / (module + ".lean")).read_text()
        names += [prefix + "." + name for name in re.findall(
            r"^(?:@\[[^\n]+\]\s*)?(?:def|theorem)\s+(\w+)", source, re.M)]
    scratch = output / "c030-axioms.lean"
    scratch.write_text("import Subtail.TerminalRealizationAudit\n" +
                       "".join("#print axioms " + n + "\n" for n in names))
    return names, scratch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/release-reproduction")
    args = parser.parse_args()
    output = args.output.resolve()
    # Refuse instead of cleaning another researcher's outputs or build cache.
    if output.exists():
        parser.error("Output already exists; choose an unused --output directory.")
    if (ROOT / "lean/.lake").exists():
        parser.error("lean/.lake already exists; use a fresh clone, not cache deletion.")
    if read(["git", "status", "--porcelain"]):
        parser.error("Checkout must be clean, including untracked files.")
    if sys.version_info[:3] != (3, 13, 14):
        parser.error("Use pinned Python 3.13.14.")
    version = read(["lean", "--version"], ROOT / "lean")
    if "version 4.33.1," not in version:
        parser.error("Use pinned Lean 4.33.1: " + version)
    output.mkdir(parents=True)
    receipt = {
        "status": "RUNNING", "revision": read(["git", "rev-parse", "HEAD"]),
        "python": platform.python_version(), "platform": platform.platform(),
        "machine": platform.machine(), "lean": version,
        "lake": read(["lake", "--version"], ROOT / "lean"),
        "initial_git_status": "", "initial_lake_absent": True,
        "project_cache_copied": False, "installed_toolchain_reused": True,
        "third_party_lean_packages": json.loads((ROOT / "lean/lake-manifest.json").read_text())["packages"],
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for folder in ("lean", "scripts", "experiments", "examples", "paper")
                          for p in sorted((ROOT / folder).rglob("*"))
                          if p.is_file() and p.suffix in (".lean", ".py", ".json", ".toml")},
        "steps": [],
        "limits": "Selected release checks; not every historical experiment or a fresh OS/toolchain installation."
    }
    receipt_path = output / "receipt.json"

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

    def run(name, command, *, lean=False, cap=600, validate=None):
        log = output / (name + ".log")
        started = time.monotonic()
        row = {"name": name, "command": [str(x).replace(str(ROOT), "<checkout>") for x in command],
               "directory": "lean" if lean else ".", "cap_seconds": cap}
        with log.open("w") as stream:
            proc = subprocess.Popen(command, cwd=ROOT / "lean" if lean else ROOT,
                                    stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = proc.wait(timeout=cap)
                row.update(exit_code=code, status="PASS" if code == 0 else "FAIL")
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                row.update(status="UNKNOWN", reason="Time cap reached; process group stopped.")
        if row["status"] == "PASS" and validate:
            try:
                row["validated"] = validate(log.read_text())
            except (AssertionError, ValueError, KeyError) as error:
                row.update(status="FAIL", reason="Output validation: " + str(error))
        row.update(wall_seconds=round(time.monotonic() - started, 3),
                   log=log.name, log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
        receipt["steps"].append(row)
        save()
        print(name, row["status"], row["wall_seconds"], flush=True)
        if row["status"] != "PASS":
            raise RuntimeError(name + ": " + row["status"] + "; inspect " + str(log))

    py = sys.executable
    save()
    try:
        run("fresh_build", ["lake", "build", "Subtail", "+Subtail.ExpressionNormalizationAudit",
            "+Subtail.EntailmentPrepared", "+Subtail.FiniteTreeDecision",
            "+Subtail.RegularTreeCertificate", "+Subtail.TerminalRealizationAudit"], lean=True, cap=2400)
        run("default_core", [py, "scripts/check_lean.py"], cap=1200)
        run("normalization_kernel", ["lake", "env", "leanchecker", "Subtail.ExpressionNormalizationAudit"], lean=True)
        for name, script, options in [
            ("c081", "check_entailment_decision.py", []),
            ("summary", "check_summary_cached.py", ["--cli"]),
            ("finite", "check_finite_tree_decision.py", []),
            ("certificate", "check_regular_certificate.py", []),
        ]:
            run(name, [py, "scripts/" + script, "--output", str(output / (name + ".json")), *options])
        for module in ("TerminalRealization", "TerminalRealizationModel", "TerminalRealizationAudit"):
            run("kernel_" + module, ["lake", "env", "leanchecker", "Subtail." + module], lean=True)
        names, scratch = c030_audit(output)

        def validate_axioms(text):
            entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
            found = {name: set(filter(None, (a.strip() for a in axioms.split(',')))) for name, axioms in entries}
            assert set(found) == set(names), "Incomplete declaration readback"
            assert all(a <= {"propext", "Quot.sound", "Classical.choice"} for a in found.values()), "Unexpected axiom"
            for name in ("a", "v", "b", "child", "upperClause", "lowerClause", "constraints"):
                assert "Classical.choice" not in found["Subtail.TerminalRealization." + name], name
            return {"declarations": len(found), "executable_constructors_choice_free": 7}

        run("c030_axioms", ["lake", "env", "lean", str(scratch)], lean=True, validate=validate_axioms)
        run("c030_independent", [py, "experiments/replay_c030_independent.py", "--output", str(output / "c030.json")])
        run("border_experiments", [py, "experiments/run_experiments.py"])

        def validate_example(text):
            values = re.findall(r": (true|false)\s*$", text, re.M)
            assert values == ["true", "false", "false", "true"], repr(values)
            return values

        run("paper_example", ["lake", "env", "lean", "--run", "../paper/example.lean"], lean=True, validate=validate_example)

        def validate_certificate(text):
            answer = json.loads(text)
            assert answer["status"] == "NOT_ENTAILED", answer.get("status")
            assert answer["certificate_verification"]["status"] == "VERIFIED", answer.get("certificate_verification")
            return answer

        run("actual_checked_countermodel", [py, "scripts/subtail.py", "examples/countermodels/alternating-spine.json",
            "--timeout", "60", "--verify-certificate"], cap=75, validate=validate_certificate)
        run("python_tests", [py, "-m", "unittest", "discover", "-s", "scripts", "-p", "test_*.py"])
        run("index", [py, "scripts/research_index.py", "--check"])
        run("paper_map", [py, "paper/check.py"])
        receipt["final_git_status"] = read(["git", "status", "--porcelain"])
        if receipt["final_git_status"]:
            raise RuntimeError("Validation changed the tracked/untracked working tree; inspect receipt.")
        receipt["status"] = "PASS"
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = str(error).replace(str(ROOT), "<checkout>")
        save()
        raise SystemExit(str(error))
    save()
    print(receipt_path)


if __name__ == "__main__":
    main()
