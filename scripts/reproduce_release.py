#!/usr/bin/env python3
"""Reproduce a clean project build and selected release checks with pinned tools.

Run in a fresh clone with no lean/.lake directory. The installed toolchain is
reused; this is not an operating-system or toolchain-installation test.
Logs and a machine-readable receipt go to an initially absent directory.
No cache is deleted, no source is changed, and no Git operation writes a ref.
The full release run requires Linux for the native process-group RSS checks.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
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


def receipt_status(path):
    """A successful launcher is insufficient: require the check's own verdict."""
    data = json.loads(path.read_text())
    if data.get("status") != "PASS":
        raise ValueError(f"Incomplete receipt {path.name}: {data.get('status')}")
    return {"status": "PASS", "receipt": str(path),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def native_receipt(path, *, diagnostic=False):
    data = json.loads(path.read_text())
    expected = native_case_ids(diagnostic)
    rows = data.get("rows", [])
    allowed = {"PASS", "UNKNOWN"} if diagnostic else {"PASS"}
    if data.get("status") != ("DIAGNOSTIC" if diagnostic else "PASS"):
        raise ValueError("Unexpected native receipt status")
    if len(rows) != len(expected) or {r["id"] for r in rows} != expected:
        raise ValueError("Native cases differ from the exact acceptance/diagnostic suite")
    if any(r.get("status") not in allowed for r in rows):
        raise ValueError("Native cases did not meet their strict/diagnostic contract")
    counts = {s: sum(r["status"] == s for r in rows) for s in ("PASS", "FAIL", "UNKNOWN", "NOT_RUN")}
    if data.get("counts") != counts:
        raise ValueError("Native case counts do not match rows")
    promotion = any(r["status"] == "PASS" and r["id"] in
                    {"direct 3 plain", "lazy 3 plain"} for r in rows)
    if type(data.get("automatic_two_promotion_success")) is not bool or data["automatic_two_promotion_success"] != promotion:
        raise ValueError("Missing or inconsistent automatic promotion coverage")
    return {"status": data["status"], "counts": counts,
            "automatic_two_promotion_success": promotion,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "meaning": "UNKNOWN rows provide no answer; inspections/frontend shortcuts are not promotion coverage"}


def native_case_ids(diagnostic=False):
    spec = importlib.util.spec_from_file_location("release_native_probe", ROOT / "experiments/issue67_native_probe.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return {" ".join(argv) for argv in module.selected("stress" if diagnostic else "acceptance")}


def paper_artifacts(root=ROOT):
    """Require the PDF, manifest and committed render sources to agree."""
    names = {"paper/" + name for name in
             ("manuscript.md", "header.tex", "build.py", "lean-map.json", "references.bib", "references.csl")}
    pdf = root / "output/pdf/subtail-paper.pdf"
    manifest = root / "output/pdf/subtail-paper-manifest.json"
    data = json.loads(manifest.read_text())
    if not isinstance(data, dict) or not isinstance(data.get("sources"), dict):
        raise ValueError("Malformed paper render manifest")
    if data.get("source_files_match_render_revision") is not True or set(data.get("sources", {})) != names:
        raise ValueError("Missing or uncommitted paper render sources")
    revision = data.get("repository_revision_at_render")
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Invalid paper render revision")
    for name, expected in data["sources"].items():
        current = (root / name).read_bytes()
        committed = subprocess.check_output(["git", "show", revision + ":" + name], cwd=root)
        if hashlib.sha256(current).hexdigest() != expected or current != committed:
            raise ValueError("Stale paper source: " + name)
    if hashlib.sha256(pdf.read_bytes()).hexdigest() != data.get("pdf_sha256"):
        raise ValueError("PDF does not match its render manifest")
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (pdf, manifest)}


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
    if not sys.platform.startswith("linux"):
        parser.error("Full release reproduction requires Linux for native RSS guards; individual portable checks remain available.")
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
        "source_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                          for name in read(["git", "ls-files", "lean", "scripts", "experiments", "examples", "paper", "tests", ".github/workflows"]).splitlines()},
        "paper_artifact_sha256": {},
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
            except (AssertionError, ValueError, KeyError, OSError) as error:
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
        receipt["paper_artifact_sha256"] = paper_artifacts()
        save()
        run("fresh_build", ["lake", "build", "Subtail", "+Subtail.ExpressionNormalizationAudit",
            "+Subtail.EntailmentPrepared", "+Subtail.FiniteTreeDecision",
            "+Subtail.RegularTreeCertificate", "+Subtail.TerminalRealizationAudit",
            "+Subtail.TerminalDecisionLazy"], lean=True, cap=2400)
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
        run("corrected_quantitative_bound", [py, "scripts/check_rank_weight_native.py"], cap=2400,
            validate=lambda _: receipt_status(ROOT / "tmp/rank-weight-native.json"))
        for name, script in (("original_bounds", "check_original_bounds.py"),
                             ("explicit_top_and_hardness", "check_explicit_top.py")):
            target = output / (name + ".json")
            run(name, [py, "scripts/" + script, "--timeout", "180", "--output", str(target)],
                cap=3600, validate=lambda _, p=target: receipt_status(p))
        target = output / "submissions/receipt.json"
        run("ordinary_extension_corpora", [py, "scripts/check_research_submissions.py", "--output", str(target)],
            validate=lambda _: receipt_status(target))
        target = output / "raw-summary-guards.json"
        run("raw_summary_diagnostic_guards", [py, "experiments/profile_raw_summary_66.py", "--self-test", "--output", str(target)],
            validate=lambda _: receipt_status(target))
        run("native_probe_typecheck", ["lake", "env", "lean", "Issue67NativeProbe.lean"], lean=True)
        target = output / "native-supervisor.json"
        run("native_supervisor_guards", [py, "experiments/issue67_native_probe.py", "--mode", "selftest", "--output", str(target)],
            validate=lambda _: receipt_status(target))
        for mode in ("acceptance", "stress"):
            target = output / ("native-" + mode + ".json")
            run("native_" + mode, [py, "experiments/issue67_native_probe.py", "--mode", mode, "--output", str(target)],
                validate=lambda _, p=target, diagnostic=mode == "stress": native_receipt(p, diagnostic=diagnostic))
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
        changed = [name for name, digest in receipt["source_sha256"].items()
                   if not (ROOT / name).is_file() or hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest]
        if changed:
            raise RuntimeError("Checked sources changed during reproduction: " + ", ".join(changed))
        if paper_artifacts() != receipt["paper_artifact_sha256"]:
            raise RuntimeError("Paper artifacts changed during reproduction")
        receipt["final_git_status"] = read(["git", "status", "--porcelain"])
        if receipt["final_git_status"]:
            raise RuntimeError("Validation changed the tracked/untracked working tree; inspect receipt.")
        receipt["status"] = "PASS"
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = str(error).replace(str(ROOT), "<checkout>")
        save()
        raise SystemExit(str(error))
    save()
    print(receipt_path)


if __name__ == "__main__":
    main()
