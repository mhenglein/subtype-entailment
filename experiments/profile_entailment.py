#!/usr/bin/env python3
"""Measure exact solver phases on the deeper E055 inputs; caps stay UNKNOWN.

The trace executes the same finite tests in the same order as EntailmentFast.
It forces a small summary before stopping each timer. Trace overhead is included;
these phase timings are diagnostic, not a replacement for matched end-to-end runs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
import check_fast_summary as fast
import check_entailment_decision as decision

PREFIX = "SUBTAIL_PROFILE:"
CASES = ("supplied-8", "supplied-12", "frontend-3", "frontend-4", "frontend-6", "frontend-8")

PRELUDE = r'''import Subtail.EntailmentFast
open Subtail Subtail.TreeSemantics Subtail.StackSummary Subtail.CanonicalReachability
open Subtail.ExpressionNormalization
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def emit (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn ("SUBTAIL_PROFILE:" ++ text)
  out.flush

@[noinline] def timed {α : Type} (name : String) (work : Unit → α)
    (force : α → String) : IO α := do
  emit ("begin:" ++ name)
  let start ← IO.monoMsNow
  let value := work ()
  -- Printing forces the observable result before the end timestamp.
  emit ("value:" ++ name ++ ":" ++ force value)
  let stop ← IO.monoMsNow
  emit ("end:" ++ name ++ ":" ++ toString (stop - start))
  return value

def matrixSummary {n : Nat} (m : CanonicalReachabilityFast.Matrix n) : String :=
  toString ((List.finRange n).foldl (fun count p =>
    count + (List.finRange n).countP (fun q => CanonicalReachabilityFast.lookup m p q)) 0)

def tabulate (edge : Fin n → Fin n → Bool) : CanonicalReachabilityFast.Matrix n :=
  Vector.ofFn fun p => Vector.ofFn fun q => edge p q

def materialize (m : System n) : System n :=
  let eps := tabulate m.eps
  let push0 := tabulate (m.push false)
  let push1 := tabulate (m.push true)
  let pop0 := tabulate (m.pop false)
  let pop1 := tabulate (m.pop true)
  ⟨CanonicalReachabilityFast.lookup eps,
   fun a => CanonicalReachabilityFast.lookup (if a then push1 else push0),
   fun a => CanonicalReachabilityFast.lookup (if a then pop1 else pop0)⟩

def systemSummary {n : Nat} (m : System n) : String :=
  toString ((List.finRange n).foldl (fun count p => count +
    (List.finRange n).countP (m.eps p) +
    (List.finRange n).countP (m.push false p) + (List.finRange n).countP (m.push true p) +
    (List.finRange n).countP (m.pop false p) + (List.finRange n).countP (m.pop true p)) 0)

def prepareTrace (m : System n) (useTables : Bool) : IO (CanonicalReachabilityFast.Cache m) := do
  let input ← if useTables then timed "primitive_tables" (fun _ => materialize m) systemSummary
    else pure m
  let forward ← timed "forward" (fun _ =>
    CanonicalReachabilityFast.matrix (StackSummaryFast.balancedTable input)) matrixSummary
  let backward ← timed "backward" (fun _ =>
    CanonicalReachabilityFast.matrix (StackSummaryFast.balancedTable (reverse input))) matrixSummary
  let edge := fun p q => CanonicalReachabilityFast.lookup backward p q ||
    (reverse input).pop false p q || (reverse input).pop true p q
  let paths ← timed "control_paths" (fun _ => CanonicalReachabilityFast.pathMatrix edge) matrixSummary
  return ⟨forward, backward, paths⟩

def separateTrace (C : List (Constraint n))
    (cache : CanonicalReachabilityFast.Cache (systemOf C)) (a b : Fin n)
    (paths : List Word) : IO Bool := do
  for (word, i) in paths.zipIdx do
    let found ← timed ("separation_" ++ toString i ++ "_length_" ++ toString word.length)
      (fun _ => CanonicalReachabilityFast.separationCheck C cache a b word) toString
    if found then return true
  return false
'''


def source(case: str, primitive_tables: bool = False) -> tuple[str, bool]:
    kind, depth_text = case.split("-")
    depth = int(depth_text)
    if kind == "supplied":
        row = next(c for c in fast.generated_cases()
                   if c.kind == "negative-supplied-separation" and len(c.word) == depth)
        body = f'''  let C : List (Constraint {row.n}) := {fast.render_constraints(row.constraints, row.n)}
  emit "input:controls:{row.n}"
  let cache ← prepareTrace (systemOf C)
  let answer ← timed "separation" (fun _ => CanonicalReachabilityFast.separationCheck C cache
    {fast.render_fin(row.a, row.n)} {fast.render_fin(row.b, row.n)} {fast.render_word(row.word)}) toString
  emit ("result:" ++ toString answer)
'''
        expected = row.expected
    else:
        left, right = decision.V(0), decision.V(1)
        for _ in range(depth):
            left, right = decision.P(left, decision.BOT), decision.P(right, decision.BOT)
        body = f'''  let G : Input 2 := []
  let s : Expr 2 := {decision.render_expr(left, 2)}
  let t : Expr 2 := {decision.render_expr(right, 2)}
  let C ← timed "normalization" (fun _ => normalized G s t) (fun c => toString c.length)
  emit ("input:controls:" ++ toString (naming G s t).total)
  let a := (naming G s t).ref s
  let b := (naming G s t).ref t
  let paths ← timed "candidate_paths" (fun _ => EntailmentFast.candidatePaths G s t)
    (fun paths => toString (paths.map List.length))
  let positive ← timed "positive" (fun _ => EntailmentFast.positiveCheck C a b) toString
  if positive then
    emit "result:true"
    return
  let cache ← prepareTrace (systemOf C)
  let sat ← timed "satisfiability" (fun _ => CanonicalReachabilityFast.satCheck C cache) toString
  if !sat then
    emit "result:true"
    return
  let separated ← separateTrace C cache a b paths
  if separated then
    emit "result:false"
    return
  let answer ← timed "fallback" (fun _ => TerminalDecisionLazy.rawNormalizedEntailsCheckLazy C a b) toString
  emit ("result:" ++ toString answer)
'''
        expected = False
    body = body.replace("prepareTrace (systemOf C)",
                        "prepareTrace (systemOf C) " + str(primitive_tables).lower())
    return PRELUDE + "\ndef main : IO Unit := do\n" + body, expected


def parse_trace(output: str, completed: bool, expected: bool) -> dict:
    phases, active, values, results = [], None, {}, []
    inputs = {}
    error = None
    for line in output.splitlines():
        if not line.startswith(PREFIX):
            continue
        fields = line[len(PREFIX):].split(":", 2)
        if fields[0] == "begin" and len(fields) == 2:
            if active is not None:
                error = "overlapping_phase_markers"
            active = fields[1]
        elif fields[0] == "value" and len(fields) == 3:
            if fields[1] != active or active in values:
                error = "invalid_value_marker"
            values[fields[1]] = fields[2]
        elif fields[0] == "end" and len(fields) == 3:
            if fields[1] != active or active not in values or not fields[2].isdigit():
                error = "invalid_end_marker"
            else:
                phases.append({"phase": active, "milliseconds": int(fields[2]), "value": values[active]})
            active = None
        elif fields[0] == "result" and len(fields) == 2:
            results.append(fields[1])
        elif fields[0] == "input" and len(fields) == 3:
            inputs[fields[1]] = fields[2]
        else:
            error = "malformed_marker"
    parsed = {"phases": phases, "unfinished_phase": active, "inputs": inputs}
    if not completed:
        return dict(parsed, status="UNKNOWN", reason="interrupted_or_resource_limit", protocol_error=error)
    if error:
        return dict(parsed, status="FAIL", reason=error)
    if active is not None or results not in (["true"], ["false"]):
        return dict(parsed, status="FAIL", reason="missing_or_ambiguous_result")
    actual = results[0] == "true"
    return dict(parsed, status="PASS" if actual == expected else "FAIL", actual=actual,
                reason="expected_answer" if actual == expected else "wrong_answer")


def run(path: Path, timeout: float, expected: bool) -> dict:
    env = os.environ.copy()
    env.update(LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="32768")

    def limits():
        import resource
        if sys.platform.startswith("linux"):
            resource.setrlimit(resource.RLIMIT_AS, (16 * 1024**3, 16 * 1024**3))
        seconds = max(1, math.ceil(timeout))
        resource.setrlimit(resource.RLIMIT_CPU, (seconds, seconds))

    # --run exposes IO output immediately. #eval captures it inside Lean's
    # command diagnostics and can lose every phase marker when evaluation dies.
    command = ["lake", "env", "lean", "--run", str(path.resolve())]
    # GNU time reports per-run peak RSS on normal completion. A killed group
    # may not write it; report None in that case rather than infer a peak.
    memory_file = path.with_suffix(".rss")
    memory_file.unlink(missing_ok=True)
    if sys.platform.startswith("linux") and Path("/usr/bin/time").is_file():
        command = ["/usr/bin/time", "-f", "%M", "-o", str(memory_file.resolve()), *command]
    start = time.monotonic()
    timed_out = False
    with tempfile.TemporaryFile() as capture:
        proc = subprocess.Popen(command, cwd=ROOT / "lean", env=env, stdout=capture,
                                stderr=subprocess.STDOUT, start_new_session=True,
                                preexec_fn=limits if os.name == "posix" else None)
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
        capture.seek(0)
        output = capture.read(65536).decode("utf-8", errors="replace")
    parsed = parse_trace(output, proc.returncode == 0 and not timed_out, expected)
    if (proc.returncode != 0 and not timed_out and ": error:" in output
            and not any(word in output.lower() for word in fast.RESOURCE_WORDS)):
        parsed.update(status="FAIL", reason="lean_compilation_error")
    rss = memory_file.read_text().strip().splitlines() if memory_file.is_file() else []
    parsed.update(wall_seconds=round(time.monotonic() - start, 3), returncode=proc.returncode,
                  peak_rss_kib=int(rss[-1]) if rss and rss[-1].isdigit() else None,
                  output_tail=output[-3000:])
    return parsed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case", action="append", choices=CASES)
    ap.add_argument("--timeout", type=float, default=20)
    ap.add_argument("--primitive-tables", action="store_true", help="ablate primitive lookup cost in cache construction only")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--scratch", type=Path, required=True)
    args = ap.parse_args()
    if args.timeout <= 0:
        ap.error("timeout must be positive")
    args.scratch = args.scratch.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)
    receipt = {"revision": fast.git_revision(), "system": platform.platform(),
               "variant": "primitive_tables" if args.primitive_tables else "baseline",
               "source_hashes": fast.source_hashes(),
               "profiler_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "caps": {"wall_seconds": args.timeout, "cpu_seconds": math.ceil(args.timeout),
                        "memory_gib": 16, "threads": 1, "stack_kib": 32768},
               "execution": "lake env lean --run; diagnostic trace only; matched E055 still uses its original #eval command",
               "timing_boundary": "phase tracing includes forced summaries and output; not uninstrumented end-to-end timing",
               "cases": []}
    for name in args.case or CASES:
        code, expected = source(name, args.primitive_tables)
        path = args.scratch / (name + ".lean")
        path.write_text(code)
        measured = run(path, args.timeout, expected)
        receipt["cases"].append({"name": name, "expected": expected,
                                 "generated_source_sha256": hashlib.sha256(code.encode()).hexdigest(), **measured})
        print(name, measured["status"], measured.get("unfinished_phase"), flush=True)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    return int(any(row["status"] == "FAIL" for row in receipt["cases"]))


if __name__ == "__main__":
    raise SystemExit(main())
