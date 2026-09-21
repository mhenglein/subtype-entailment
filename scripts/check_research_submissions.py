#!/usr/bin/env python3
"""Replay the accepted ordinary extension corpora without changing old receipts.

These finite checks do not implement or prove the general transfer theorems.
Only environment and elapsed-time fields are excluded from receipt comparison.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CORPORA = (
    ("ternary", "ternary_transfer.py", "ternary-transfer.json",
     ("python", "platform", "elapsed_seconds")),
    ("first_return", "standalone_first_return_astra.py", "standalone-first-return-astra.json",
     ("python",)),
    ("function", "check_function_only_transfer.py", "function-only-transfer.json",
     ("environment", "elapsed_seconds")),
)


def compare(actual, saved, ignored):
    if actual.get("status") != "PASS":
        raise ValueError("Corpus did not complete with PASS")
    left = {k: v for k, v in actual.items() if k not in ignored}
    right = {k: v for k, v in saved.items() if k not in ignored}
    if left != right:
        changed = sorted(k for k in left.keys() | right.keys() if left.get(k) != right.get(k))
        raise ValueError("Scientific receipt fields differ: " + ", ".join(changed))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/research-submissions/receipt.json")
    args = parser.parse_args()
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    report = {"status": "RUNNING", "revision": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), "corpora": []}
    try:
        for name, script, saved_name, ignored in CORPORA:
            script_path = ROOT / "experiments" / script
            saved_path = ROOT / "results" / saved_name
            target = output.parent / saved_name
            log = output.parent / (name + ".log")
            row = {"name": name, "status": "RUNNING", "receipt": target.name,
                   "source_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
                   "saved_receipt_sha256": hashlib.sha256(saved_path.read_bytes()).hexdigest(),
                   "ignored_fields": list(ignored), "cap_seconds": 180}
            report["corpora"].append(row)
            start = time.monotonic()
            with log.open("w") as stream:
                try:
                    proc = subprocess.run([sys.executable, str(script_path), "--output", str(target)],
                                          cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
                except subprocess.TimeoutExpired:
                    row["status"] = "UNKNOWN"
                    raise ValueError(name + " hit its cap; no negative mathematical answer")
            row["exit_code"] = proc.returncode
            if proc.returncode:
                row["status"] = "FAIL"
                raise ValueError(name + " failed; see " + str(log))
            compare(json.loads(target.read_text()), json.loads(saved_path.read_text()), ignored)
            row.update(status="PASS", wall_seconds=round(time.monotonic() - start, 3),
                       receipt_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
                       log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
        report["status"] = "PASS"
    except (ValueError, OSError) as error:
        if report["corpora"] and report["corpora"][-1]["status"] == "RUNNING":
            report["corpora"][-1]["status"] = "FAIL"
        report["status"] = "UNKNOWN" if any(r["status"] == "UNKNOWN" for r in report["corpora"]) else "FAIL"
        report["error"] = str(error)
    report["limits"] = "Bounded component evidence; no generic compiler implementation, new Lean proof or priority claim."
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": report["status"], "receipt": str(output)}))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
