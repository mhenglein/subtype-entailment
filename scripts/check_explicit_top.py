#!/usr/bin/env python3
"""Check the explicit-top language core and two independent finite corpora.

The full labelled-tree/expression reduction is an ordinary theorem. This gate
does not certify or expose an executable Lean explicit-top decision procedure.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time

from check_original_bounds import CheckFailure, audit_axioms, compare_receipt, stop_process_group

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
MODULE = "Subtail.ExplicitTopDualProjection"
SOURCE = "lean/Subtail/ExplicitTopDualProjection.lean"


def hashes() -> dict[str, str]:
    paths = (SOURCE, "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
             "scripts/check_explicit_top.py", "scripts/check_original_bounds.py",
             "experiments/check_explicit_top_dual_projection.py",
             "experiments/check_hr_topfree_transfer_70.py",
             "results/explicit-top-dual-projection.json", "results/hr-topfree-transfer-70.json")
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/explicit-top-check.json")
    parser.add_argument("--timeout", type=int, default=900, help="Seconds per command")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="explicit-top-", dir=output.parent))
    receipt = {"status": "PENDING", "scope": __doc__.strip(),
               "python": platform.python_version(), "platform": platform.platform(),
               "commands": [], "source_sha256": hashes()}

    def run(name: str, command: list[str], cwd: Path = LEAN) -> str:
        print(name, flush=True)
        log = scratch / (name + ".log")
        row = {"name": name, "command": [a.replace(str(ROOT), "<checkout>") for a in command],
               "cwd": str(cwd.relative_to(ROOT)) or ".", "status": "PENDING",
               "wall_timeout_seconds": args.timeout, "log": str(log.relative_to(output.parent))}
        receipt["commands"].append(row)
        start = time.monotonic()
        with log.open("w") as stream:
            proc = subprocess.Popen(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
                                    start_new_session=True, text=True)
            try:
                proc.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                stop_process_group(proc)
                row["status"] = "UNKNOWN"
            row["exit_code"] = proc.returncode
            row["elapsed_seconds"] = round(time.monotonic() - start, 3)
        if row["status"] == "UNKNOWN":
            raise CheckFailure(name + " exceeded its wall-clock limit", "UNKNOWN")
        row["status"] = "PASS" if proc.returncode == 0 else "FAIL"
        if proc.returncode:
            raise CheckFailure(name + " failed; see " + row["log"])
        return log.read_text()

    try:
        receipt["git_head"] = run("git-head", ["git", "rev-parse", "HEAD"], ROOT).strip()
        receipt["tracked_status_before"] = run("git-status", ["git", "status", "--short", "--untracked-files=no"], ROOT).splitlines()
        version = run("toolchain", ["lean", "--version"]).strip()
        receipt["lean_version"] = version
        if "version 4.33.1," not in version:
            raise CheckFailure("Use the pinned Lean 4.33.1 toolchain: " + version)
        source = (ROOT / SOURCE).read_text()
        # This isolated language core imports only the pinned standard library.
        if re.findall(r"^import (.+)$", source, re.M) != ["Std"]:
            raise CheckFailure("Imports changed: extend the source/dependency audit")
        pairs = re.findall(r"^(?:@\[[^\]]*\]\s*)?(theorem|def|abbrev|structure|inductive)\s+([A-Za-z_][\w.]*)", source, re.M)
        expected = {MODULE + "." + name: kind for kind, name in pairs}
        critical = {"remaining_model", "positive_projection_surjective", "negative_projection_surjective",
                    "satisfiable_iff_projections", "entails_iff_projections", "positive_countermodel_lift"}
        if len(pairs) != 29 or len(expected) != 29 or not critical <= {n for _, n in pairs}:
            raise CheckFailure("The 29-declaration inventory changed: review the audit")
        run("build", ["lake", "build", "+" + MODULE])
        run("kernel", ["lake", "env", "leanchecker", MODULE])
        audit = scratch / "axioms.lean"
        audit.write_text("import " + MODULE + "\n" + "".join("#print axioms " + n + "\n" for n in expected))
        receipt["axioms"] = audit_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), expected)
        receipt["declarations"] = len(expected)
        receipt["non_theorem_definitions_choice_free"] = True
        corpora = {}
        for name, script, saved, ignored in (
            ("top-corpus", "check_explicit_top_dual_projection.py", "explicit-top-dual-projection.json", ("python", "platform")),
            ("hardness-corpus", "check_hr_topfree_transfer_70.py", "hr-topfree-transfer-70.json", ("python", "platform", "machine")),
        ):
            target = scratch / saved
            run(name, [sys.executable, "experiments/" + script, "--output", str(target)], ROOT)
            compare_receipt(target, ROOT / "results" / saved, ignored)
            if json.loads(target.read_text())["status"] != "PASS":
                raise CheckFailure(name + " did not pass")
            corpora[name] = {"status": "PASS", "receipt": str(target.relative_to(output.parent)),
                             "comparison": "MATCH_EXCEPT_ENVIRONMENT", "ignored_fields": list(ignored)}
        receipt["finite_diagnostics"] = corpora
        if hashes() != receipt["source_sha256"]:
            raise CheckFailure("Checked sources changed during execution")
        receipt["status"] = "PASS"
    except (CheckFailure, OSError, ValueError, KeyError) as error:
        receipt["status"] = error.status if isinstance(error, CheckFailure) else "FAIL"
        receipt["error"] = str(error)
    receipt["limits"] = [
        "Labelled-tree identification, finite naming/projection and the four-call decision remain ordinary proofs.",
        "This is no native explicit-top solver, parser or end-to-end Lean theorem.",
        "Finite diagnostic corpora supply no universal model bound; capped misses remain UNKNOWN.",
        "The hardness theorem is ordinary mathematics for arbitrary and regular trees, not finite trees.",
    ]
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(output), "error": receipt.get("error")}))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
