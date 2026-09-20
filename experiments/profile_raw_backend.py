#!/usr/bin/env python3
"""Profile the complete raw two-branch decision; interrupted runs stay UNKNOWN."""
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

PREFIX = "SUBTAIL_RAW_PROFILE:"
PHASES = {"summary", "cycle_candidates", "infinite_prefix_search", "terminalize",
          "empty_witness", "safe_references", "promotion", "terminal_scan",
          "initial_safety", "infinite_stream"}

PRELUDE = r'''import Subtail.TerminalDecisionLazy
open Subtail Subtail.TreeSemantics Subtail.StackSummary Subtail.CanonicalReachability
open Subtail.ExpressionNormalization
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def emit (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn ("SUBTAIL_RAW_PROFILE:" ++ text)
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
'''

def source(fixture: decision.Fixture, variant: str = "baseline") -> str:
    if fixture.kind != "raw":
        raise ValueError("Only raw fixtures belong in this experiment")
    code = PRELUDE + f"""
open Subtail.SummaryAutomaton Subtail.InfiniteDecision Subtail.AbsorbingTerminal
open Subtail.TerminalDecisionLazy Subtail.RankQuery Subtail.RankQueryDecision
open Subtail.RankQueryEnumeration

def anyExact (xs : List α) : Nat → (List α → Bool) → Bool
  | 0, test => test []
  | n+1, test => xs.any (fun x => anyExact xs n (fun w => test (x :: w)))

def infiniteStream (I : Instance k) : Bool :=
  (List.finRange k).any fun q =>
    I.final.get q && (List.finRange k).all (fun p => !((I.flags.get p).get q)) &&
      (List.range (k+1)).any (fun len => anyExact [false,true] len (fun c =>
        cycleCheck I q c && prefixCheck I q c))

def main : IO Unit := do
  let C := {decision.render_constraints(fixture)}
  emit "input:controls:{fixture.n}"
  let I ← timed "summary" (fun _ => summaryInstance C {decision.fin(fixture.a, fixture.n)} {decision.fin(fixture.b, fixture.n)})
    (fun i => toString i.final.size)
  let cycles ← timed "cycle_candidates" (fun _ => candidates I) (fun cs => toString cs.length)
  let infinite ← timed "infinite_prefix_search" (fun _ => cycles.any (fun qc => prefixCheck I qc.1 qc.2)) toString
  if infinite then
    emit "result:false"
    return
  let T ← timed "terminalize" (fun _ => terminalize I) (fun i => toString i.final.size)
  let empty ← timed "empty_witness" (fun _ => witnessCheck T []) toString
  if empty then
    emit "result:false"
    return
  let safe ← timed "safe_references" (fun _ => safeOneLetterExists T) toString
  if !safe then
    emit "result:true"
    return
  let phi ← timed "promotion" (fun _ => promote (preimage T RankQueryCoverage.budget) (finishQuery T) ((states {fixture.n}).length - 2))
    (fun p => toString p.length)
  let terminal ← timed "terminal_scan" (fun _ => terminalCandidateScan T phi) toString
  emit ("result:" ++ toString (!terminal))
"""
    if variant != "baseline":
        eager = '''  let cycles ← timed "cycle_candidates" (fun _ => candidates I) (fun cs => toString cs.length)
  let infinite ← timed "infinite_prefix_search" (fun _ => cycles.any (fun qc => prefixCheck I qc.1 qc.2)) toString'''
        stream = '''  let infinite ← timed "infinite_stream" (fun _ => infiniteStream I) toString'''
        if variant == "gated":
            stream = '''  let initialSafe ← timed "initial_safety" (fun _ => safeState I I.initial) toString
  let infinite ← if initialSafe then
    timed "infinite_stream" (fun _ => infiniteStream I) toString
    else pure false'''
        code = code.replace(eager, stream)
    return code


def parse_trace(output: str, completed: bool, expected: bool) -> dict:
    phases, active, values, results = [], None, {}, []
    inputs = {}
    error = None
    for line in output.splitlines():
        if not line.startswith(PREFIX):
            continue
        fields = line[len(PREFIX):].split(":", 2)
        if results:
            error = "marker_after_result"
        if fields[0] == "begin" and len(fields) == 2:
            if active is not None:
                error = "overlapping_phase_markers"
            if fields[1] not in PHASES:
                error = "unknown_phase"
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
            if fields[1] != "controls" or fields[1] in inputs or not fields[2].isdigit():
                error = "invalid_input_marker"
            inputs[fields[1]] = fields[2]
        else:
            error = "malformed_marker"
    parsed = {"phases": phases, "unfinished_phase": active, "inputs": inputs}
    if not completed:
        return dict(parsed, status="UNKNOWN", reason="interrupted_or_resource_limit", protocol_error=error)
    if error:
        return dict(parsed, status="FAIL", reason=error)
    if not phases or not inputs or active is not None or results not in (["true"], ["false"]):
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
        try:
            proc = subprocess.Popen(command, cwd=ROOT / "lean", env=env, stdout=capture,
                                    stderr=subprocess.STDOUT, start_new_session=True,
                                    preexec_fn=limits if os.name == "posix" else None)
        except OSError as error:
            return {"status": "UNKNOWN", "reason": "launch_error", "error": str(error),
                    "phases": [], "unfinished_phase": None, "inputs": {},
                    "wall_seconds": round(time.monotonic() - start, 3), "peak_rss_kib": None}
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
        output_bytes = capture.seek(0, os.SEEK_END)
        capture.seek(0)
        output = capture.read(65536).decode("utf-8", errors="replace")
        capture.seek(max(0, output_bytes - 3000))
        tail = capture.read().decode("utf-8", errors="replace")
    parsed = parse_trace(output, proc.returncode == 0 and not timed_out, expected)
    if output_bytes > 65536 and proc.returncode == 0 and not timed_out:
        parsed.pop("actual", None)
        parsed.update(status="FAIL", reason="trace_output_truncated")
    diagnostics = output + tail
    if (proc.returncode != 0 and not timed_out and ": error:" in diagnostics
            and not any(word in diagnostics.lower() for word in fast.RESOURCE_WORDS)):
        parsed.update(status="FAIL", reason="lean_compilation_error")
    rss = memory_file.read_text().strip().splitlines() if memory_file.is_file() else []
    parsed.update(wall_seconds=round(time.monotonic() - start, 3), returncode=proc.returncode,
                  peak_rss_kib=int(rss[-1]) if rss and rss[-1].isdigit() else None,
                  output_tail=tail, output_bytes=output_bytes, trace_truncated=output_bytes > 65536)
    return parsed

def main() -> int:
    fixtures = [f for f in decision.corpus() if f.kind == "raw"]
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case", action="append", choices=[f.name for f in fixtures])
    ap.add_argument("--variant", choices=("baseline", "stream", "gated"), default="baseline")
    ap.add_argument("--timeout", type=float, default=20)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--scratch", type=Path, required=True)
    args = ap.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        ap.error("timeout must be positive and finite")
    args.scratch = args.scratch.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)
    receipt = {"revision": fast.git_revision(), "variant": args.variant, "system": platform.platform(),
               "source_hashes": fast.source_hashes(),
               "profiler_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "caps": {"wall_seconds": args.timeout, "cpu_seconds": math.ceil(args.timeout),
                        "address_space_gib_linux": 16, "address_space_enforced": sys.platform.startswith("linux"),
                        "cpu_enforced": os.name == "posix", "threads": 1, "stack_kib": 32768},
               "execution": "lake env lean --run; diagnostic only, original matched benchmark uses #eval",
               "timing_boundary": "phases include forcing/output overhead; not uninstrumented timings",
               "cases": []}
    for fixture in fixtures:
        if args.case and fixture.name not in args.case:
            continue
        code = source(fixture, args.variant)
        path = args.scratch / (fixture.name + ".lean")
        path.write_text(code)
        measured = run(path, args.timeout, fixture.expected)
        receipt["cases"].append({"name": fixture.name, "expected": fixture.expected, "kind": "raw",
                                 "true_means": "entailment", "justification": fixture.justification,
                                 "generated_source_sha256": hashlib.sha256(code.encode()).hexdigest(), **measured})
        print(fixture.name, measured["status"], measured.get("unfinished_phase"), flush=True)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    return int(any(row["status"] == "FAIL" for row in receipt["cases"]))

if __name__ == "__main__":
    raise SystemExit(main())
