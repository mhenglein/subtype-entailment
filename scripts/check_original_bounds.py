#!/usr/bin/env python3
"""Check the integrated smaller compiler and original terminal witness bound.

Lean proves the all-input statements. Python comparisons are bounded regression
evidence only. This check never fetches or overlays a historical proof source.
Run in a checkout with its own Lake build directory.
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
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
MODULES = {
    "Subtail.SmallerCompilerAstra": (22, {"closureFor", "closureStatement", "preSmall"}),
    "FOnlyAstra": (20, {"originalF", "original_F_small", "finishPlusQuery"}),
    "FOnlyCompilerBridge": (6, {"small_preimage_bounded", "coverage_small", "original_F"}),
}


class CheckFailure(RuntimeError):
    def __init__(self, message: str, status: str = "FAIL"):
        super().__init__(message)
        self.status = status


def declarations() -> dict[str, str]:
    expected = {}
    for module, (count, required) in MODULES.items():
        source = (LEAN / (module.replace(".", "/") + ".lean")).read_text()
        pairs = re.findall(r"^(?:@\[[^\n]*\] )?(def|theorem|abbrev|opaque|axiom)\s+(\w+)",
                           source, re.M)
        names = {name for _, name in pairs}
        if len(pairs) != count or len(names) != count or not required <= names:
            raise CheckFailure(f"Public declaration inventory changed in {module}: {pairs}")
        prefix = module if module.startswith("Subtail.") else "Subtail." + module
        for kind, name in pairs:
            if kind not in {"def", "theorem"}:
                raise CheckFailure(f"Unexpected declaration kind: {kind} {name}")
            expected[prefix + "." + name] = kind
    return expected


def audit_axioms(output: str, expected: dict[str, str]) -> dict[str, list[str]]:
    rows = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                      output)
    found = {}
    for name, raw in rows:
        if name in found:
            raise CheckFailure("Duplicate axiom report: " + name)
        found[name] = sorted({a.strip() for a in raw.split(",") if a.strip()})
    if set(found) != set(expected):
        raise CheckFailure("Incomplete or unexpected axiom report: " + repr({
            "missing": sorted(set(expected) - set(found)),
            "extra": sorted(set(found) - set(expected)),
        }))
    for name, axioms in found.items():
        allowed = {"propext", "Quot.sound"}
        if expected[name] == "theorem":
            allowed.add("Classical.choice")
        if not set(axioms) <= allowed:
            raise CheckFailure(f"Forbidden dependency in {name}: {axioms}")
    return found


def source_hashes() -> dict[str, str]:
    """Include transitive local Lean imports and the independent checkers."""
    pending = list(MODULES)
    paths = set()
    while pending:
        module = pending.pop()
        path = LEAN / (module.replace(".", "/") + ".lean")
        if path in paths or not path.is_file():
            continue  # Toolchain imports are identified by lean --version.
        paths.add(path)
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                pending.extend(line.split()[1:])
    paths.update(ROOT / p for p in (
        "scripts/check_original_bounds.py", "scripts/test_check_original_bounds.py",
        "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
        "experiments/check_smaller_compiler_astra.py", "experiments/f_only_astra.py",
        "results/smaller-compiler-astra.json", "results/f-only-astra.json",
    ))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def compare_receipt(actual: Path, saved: Path, ignored: tuple[str, ...] = ()) -> None:
    fresh, old = json.loads(actual.read_text()), json.loads(saved.read_text())
    for field in ignored:
        fresh.pop(field, None)
        old.pop(field, None)
    if fresh != old:
        changed = sorted(k for k in fresh.keys() | old.keys() if fresh.get(k) != old.get(k))
        raise CheckFailure(f"Saved regression receipt differs in {saved.name}: {changed}")


def stop_process_group(proc: subprocess.Popen) -> None:
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass  # The group can exit between the timeout and this cleanup.
    proc.wait()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/original-bounds-check.json")
    parser.add_argument("--timeout", type=int, default=900, help="Wall-clock limit per command, seconds")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="original-bounds-", dir=output.parent))
    receipt = {
        "status": "PENDING", "scope": "smaller compiler U contract and original terminal witness F",
        "python": platform.python_version(), "platform": platform.platform(),
        "commands": [], "limits": [
            "Python searches are bounded diagnostics, not proofs of nonexistence.",
            "This does not profile or replace the production subtype decision backend.",
            "The older concrete compiler U counterexample remains valid.",
        ],
    }

    def run(name: str, argv: list[str], cwd: Path = LEAN) -> str:
        print(name, flush=True)
        log = scratch / (name + ".log")
        start = time.monotonic()
        row = {"name": name, "command": [a.replace(str(ROOT), "<checkout>") for a in argv],
               "cwd": str(cwd.relative_to(ROOT)) or ".", "wall_timeout_seconds": args.timeout,
               "log": str(log.relative_to(output.parent)), "status": "PENDING"}
        receipt["commands"].append(row)
        with log.open("w") as stream:
            proc = subprocess.Popen(argv, cwd=cwd, text=True, stdout=stream,
                                    stderr=subprocess.STDOUT, start_new_session=True)
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
        receipt["source_sha256"] = source_hashes()
        version = run("toolchain", ["lean", "--version"]).strip()
        receipt["lean_version"] = version
        if "version 4.33.1," not in version:
            raise CheckFailure("Use the pinned Lean 4.33.1 toolchain: " + version)
        expected = declarations()
        run("build-dependencies", ["lake", "build", "+Subtail.RankQueryLengthBound", "+Subtail.SmallerCompilerAstra"])
        for module in ("FOnlyAstra", "FOnlyCompilerBridge"):
            run("compile-" + module, ["lake", "env", "lean", "-o", ".lake/build/lib/lean/" + module + ".olean", module + ".lean"])
        for module in MODULES:
            run("kernel-" + module, ["lake", "env", "leanchecker", module])
        audit = scratch / "axioms.lean"
        audit.write_text("import FOnlyCompilerBridge\n" + "".join("#print axioms " + n + "\n" for n in expected))
        receipt["axioms"] = audit_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), expected)
        receipt["declaration_counts"] = {m: n for m, (n, _) in MODULES.items()}
        receipt["runtime_choice_free"] = True
        native = scratch / "native.lean"
        native.write_text("""import FOnlyCompilerBridge
open Subtail Subtail.RankQueryWeightCounterexample Subtail.SmallerCompilerAstra
#eval FOnlyAstra.originalF 1
#eval FOnlyAstra.originalF 2
#eval compact inst input diagram
#eval (preSmall inst []).length
""")
        actual = run("native-guards", ["lake", "env", "lean", str(native)])
        if actual != "0\n6\nfalse\n0\n":
            raise CheckFailure("Native guard output differs: " + repr(actual))
        receipt["native_guards"] = {"status": "PASS", "output": actual.splitlines()}
        compiler = scratch / "compiler-standalone.json"
        run("python-compiler", [sys.executable, "experiments/check_smaller_compiler_astra.py", "--output", str(compiler)], ROOT)
        compare_receipt(compiler, ROOT / "results/smaller-compiler-astra.json")
        repository = scratch / "compiler-repository.json"
        run("python-compiler-repository", [sys.executable, "experiments/check_smaller_compiler_astra.py", "--repository", "--output", str(repository)], ROOT)
        repo_result = json.loads(repository.read_text())
        if repo_result["status"] != "PASS" or repo_result["counts"].get("unchanged_python_counterexample_replays") != 1:
            raise CheckFailure("Repository compiler comparison did not complete")
        f_result = scratch / "f-bounded.json"
        run("python-f-bounded", [sys.executable, "experiments/f_only_astra.py", "--output", str(f_result)], ROOT)
        compare_receipt(f_result, ROOT / "results/f-only-astra.json", ("python", "platform", "elapsed_seconds"))
        receipt["python_diagnostics"] = {"status": "PASS", "compiler_saved_receipt": "MATCH",
            "repository_counterexample_replays": 1, "f_saved_receipt": "MATCH_EXCEPT_ENVIRONMENT_AND_TIME",
            "f_status": json.loads(f_result.read_text())["status"],
            "negative_search_semantics": "UNKNOWN unless an independent all-length proof is supplied"}
        if source_hashes() != receipt["source_sha256"]:
            raise CheckFailure("A checked source changed during validation")
        receipt["status"] = "PASS"
    except (CheckFailure, OSError, ValueError, KeyError) as error:
        receipt["status"] = error.status if isinstance(error, CheckFailure) else "FAIL"
        receipt["error"] = str(error)
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(output), "error": receipt.get("error")}))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
