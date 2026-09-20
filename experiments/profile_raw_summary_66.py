#!/usr/bin/env python3
"""Issue 66 diagnostics; no optimized constructor or new performance claim.

Default: emit sources without running Lean. --run requires a full pinned
checkout. Every native process retains the 20-second cap. Diagnostic probes
have separate prerequisites and cannot be added into an endpoint timing.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = "19b06d4fed9da635d9b911f0e908d04e4fc4b099"
MODES = ("phased", "enumeration", "decode", "lookup", "successors", "encode", "flags", "baseline")
PHASES = {"prepare", "sat", "danger", "state_table", "initial", "transitions", "bad", "final", "flags", "enumeration", "decode_scan", "lookup_scan", "successors", "encode_successors", "terminal"}
EXPECTED_BLOBS = {
    "lean/Subtail/SummaryAutomaton.lean": "c1a6bb0ff71a3053c7b795b35d08220685ed990f",
    "lean/Subtail/SummaryInstanceCached.lean": "bc687f57879bac64455544ab99d5dcb45301a762",
    "lean/Subtail/EntailmentPrepared.lean": "2c0d5a0877de67d888f8a21f0e0624b838e5aedf",
    "experiments/profile_raw_backend.py": "5634f283eeb54d97441d446ee4461ef6719e981e",
}
PRELUDE = r'''import Subtail.EntailmentPrepared
open Subtail Subtail.TreeSemantics Subtail.StackSummary Subtail.CanonicalReachability
open Subtail.SummaryAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def N : Nat := @N@
abbrev K : Nat := (states N).length
def C : List (Constraint N) := []
def emit (s : String) : IO Unit := do
  let out @BIND@ IO.getStdout
  out.putStrLn ("SUBTAIL_RAW_PROFILE:" ++ s)
  out.flush
@[noinline] def timed (name : String) (work : Unit -> a) (force : a -> String) : IO a := do
  emit ("begin:" ++ name)
  let start @BIND@ IO.monoMsNow
  let value := work ()
  emit ("value:" ++ name ++ ":" ++ force value)
  let stop @BIND@ IO.monoMsNow
  emit ("end:" ++ name ++ ":" ++ toString (stop - start))
  return value

def bit (b : Bool) : Nat := if b then 1 else 0
def pairScore (s : Summary N) : Nat :=
  s.1.foldl (fun r q => r + q.val + 1) 0 + s.2.foldl (fun r q => r + q.val + 1) 0
def score (v : Vector a k) (f : a -> Nat) : Nat :=
  (List.finRange k).foldl (fun r q => r + f (v.get q)) 0
def forceVec (v : Vector a k) (f : a -> Nat) : String := toString (score v f)
def forceP (P : EntailmentPrepared.Prepared N) : String := toString
  (score P.cache.forward (fun row => score row bit) +
   score P.cache.backward (fun row => score row bit) +
   score P.cache.paths (fun row => score row bit))
def successorTable (P : EntailmentPrepared.Prepared N) :
    Vector (Prod {s : Summary N // s @MEM@ states N} {s : Summary N // s @MEM@ states N}) K :=
  let d := SummaryInstanceCached.stateTable N
  Vector.ofFn fun q =>
    (@PAIR@SummaryInstanceCached.advancePair P.machine P.cache (d.get q) false,
       SummaryInstanceCached.advancePair_mem P.machine P.cache (d.get q) false@ENDPAIR@,
     @PAIR@SummaryInstanceCached.advancePair P.machine P.cache (d.get q) true,
       SummaryInstanceCached.advancePair_mem P.machine P.cache (d.get q) true@ENDPAIR@)
'''
PREPARE = '  let P @BIND@ timed "prepare" (fun _ => EntailmentPrepared.prepare (systemOf C)) forceP\n'
TABLE = '  let d @BIND@ timed "state_table" (fun _ => SummaryInstanceCached.stateTable N) (fun v => forceVec v pairScore)\n'
FLAG_WORK = 'Vector.ofFn fun p => Vector.ofFn fun q => (d.get p).1.any fun m => decide (m @MEM@ (d.get q).2)'
FLAG_FORCE = '(fun v => forceVec v (fun row => score row bit))'
PHASED = PREPARE + r'''  let sat @BIND@ timed "sat" (fun _ => SummaryInstanceCached.satCheck C P.machine P.cache) toString
  let danger @BIND@ timed "danger" (fun _ => Vector.ofFn (SummaryInstanceCached.dangerCheck C P.machine P.cache)) (fun v => forceVec v bit)
''' + TABLE + r'''  let initial @BIND@ timed "initial" (fun _ => SummaryInstanceCached.initial P.machine P.cache (@PAIR@0, by decide@ENDPAIR@ : Fin N) (@PAIR@1, by decide@ENDPAIR@ : Fin N)) (fun q => toString q.val)
  let transitions @BIND@ timed "transitions" (fun _ => (Vector.ofFn fun q =>
    (some (SummaryInstanceCached.advance P.machine P.cache q false),
     some (SummaryInstanceCached.advance P.machine P.cache q true))))
    (fun v => forceVec v (fun row => row.1.elim 0 (fun q => q.val + 1) + row.2.elim 0 (fun q => q.val + 1)))
  let bad @BIND@ timed "bad" (fun _ => Vector.ofFn fun q => !sat || (d.get q).1.any (fun m => danger.get m)) (fun v => forceVec v bit)
  let final @BIND@ timed "final" (fun _ => Vector.ofFn fun q => !((d.get q).2.any fun f => decide (@EXISTS@ l r, Constraint.lower l r f @MEM@ C))) (fun v => forceVec v bit)
''' + '  let flags @BIND@ timed "flags" (fun _ => ' + FLAG_WORK + ') ' + FLAG_FORCE + r'''
  let I : Instance K := { initial := initial, transitions := transitions, bad := bad, final := final, flags := flags }
  let infinite @BIND@ timed "infinite_stream" (fun _ => InfiniteDecisionLazy.infiniteWitnessCheckLazy I) toString
  if infinite then
    emit "result:false"
  else
    let terminal @BIND@ timed "terminal" (fun _ => TerminalDecisionLazy.terminalWitnessCheckLazy (AbsorbingTerminal.terminalize I)) toString
    emit ("result:" ++ toString (!terminal))
'''


def source(n: int, mode: str) -> str:
    if n not in (3, 4, 5, 6) or mode not in MODES:
        raise ValueError("only the frozen empty n=3..6 probes are supported")
    if mode == "baseline":
        return f'''import Subtail.EntailmentPrepared
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def main : IO Unit := do
  let actual := Subtail.EntailmentPrepared.rawNormalizedEntailsCheck
    ([] : List (Subtail.TreeSemantics.Constraint {n}))
    (@PAIR@0, by decide@ENDPAIR@ : Fin {n}) (@PAIR@1, by decide@ENDPAIR@ : Fin {n})
  IO.println ("RAW66_BASELINE:n{n}:" ++ (if actual then "true" else "false"))
#eval main
'''.replace("@PAIR@", chr(0x27e8)).replace("@ENDPAIR@", chr(0x27e9))
    if mode == "phased":
        body = PHASED
    elif mode == "enumeration":
        body = '  let _ @BIND@ timed "enumeration" (fun _ => states N) (fun xs => toString (xs.foldl (fun r s => r + pairScore s) 0))\n'
    elif mode == "decode":
        body = '  let _ @BIND@ timed "decode_scan" (fun _ => (Vector.ofFn fun (q : Fin K) => decode q)) (fun v => forceVec v pairScore)\n'
    elif mode == "lookup":
        body = TABLE + '  let _ @BIND@ timed "lookup_scan" (fun _ => Vector.ofFn fun (q : Fin K) => d.get q) (fun v => forceVec v pairScore)\n'
    elif mode == "successors":
        body = PREPARE + '  let _ @BIND@ timed "successors" (fun _ => successorTable P) (fun v => forceVec v (fun row => pairScore row.1.val + pairScore row.2.val))\n'
    elif mode == "encode":
        body = PREPARE + r'''  let succs @BIND@ timed "successors" (fun _ => successorTable P) (fun v => forceVec v (fun row => pairScore row.1.val + pairScore row.2.val))
  let _ @BIND@ timed "encode_successors" (fun _ => Vector.ofFn fun (q : Fin K) =>
    (encode (succs.get q).1.val (succs.get q).1.property,
     encode (succs.get q).2.val (succs.get q).2.property))
    (fun v => forceVec v (fun row => row.1.val + row.2.val))
'''
    else:
        body = TABLE + '  let _ @BIND@ timed "flags" (fun _ => ' + FLAG_WORK + ') ' + FLAG_FORCE + '\n'
    if mode != "phased":
        body += '  emit "result:true" -- Completion token only; NOT an entailment answer.\n'
    text = PRELUDE + '\ndef main : IO Unit := do\n  emit "input:controls:@N@"\n' + body
    for old, new in {"@N@": str(n), "@BIND@": chr(0x2190), "@PAIR@": chr(0x27e8), "@ENDPAIR@": chr(0x27e9), "@MEM@": chr(0x2208), "@EXISTS@": chr(0x2203)}.items():
        text = text.replace(old, new)
    return text


def check_baseline(run: dict, marker: str) -> dict:
    """Never turn a partial/failed process marker into a Boolean answer."""
    result = dict(run)
    if result.get("status") != "PASS":
        result.pop("actual", None)
        return result
    if result.get("marker") != marker + "false":
        result.pop("actual", None)
        result.update(status="FAIL", reason="missing_ambiguous_or_wrong_expected_answer")
    else:
        result["actual"] = False
    return result


def self_test() -> dict:
    rendered = 0
    for n in (3, 4, 5, 6):
        for mode in MODES:
            code = source(n, mode)
            assert "@" not in code.replace("@[noinline]", "")
            assert ("#eval main" in code) == (mode == "baseline")
            assert "rawNormalizedEntailsCheckLazy" not in code
            assert ("Completion token only" in code) == (mode not in ("phased", "baseline"))
            rendered += 1
    marker = "X:"
    for status in ("UNKNOWN", "FAIL", "NOT_READY"):
        checked = check_baseline({"status": status, "marker": marker + "false", "actual": False}, marker)
        assert "actual" not in checked and checked["status"] == status
    for bad in (None, "", marker + "true", marker + "false\n" + marker + "false"):
        assert check_baseline({"status": "PASS", "marker": bad}, marker)["status"] == "FAIL"
    assert check_baseline({"status": "PASS", "marker": marker + "false"}, marker)["actual"] is False
    pairs = 0
    for n in range(5):
        subsets = [()]
        for x in reversed(range(n)):
            subsets += [(x,) + ys for ys in subsets]
        states = [(b, a) for b in subsets for a in subsets]
        m = len(subsets)
        assert m == 2**n and len(states) == m*m
        rows = [[bool(set(b).intersection(a)) for _, a in states] for b in subsets]
        for p, (b, a) in enumerate(states):
            assert b == subsets[p // m] and a == subsets[p % m]
            for q, (_, other) in enumerate(states):
                assert rows[p // m][q] == any(x in other for x in b)
                pairs += 1
    return {"status": "PASS", "rendered_sources": rendered, "baseline_marker_checks": 8,
            "ordinary_row_identity_cells_n0_through_n4": pairs,
            "lean_compilation": "NOT_RUN", "native_performance": "NOT_RUN",
            "scope": "Python/source-template checks only; not the 83 full-field Lean comparisons or independent review"}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--n", type=int, choices=(3, 4, 5, 6), action="append")
    ap.add_argument("--mode", choices=MODES, action="append")
    ap.add_argument("--run", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--scratch", type=Path, default=ROOT / "tmp/raw-summary-66")
    ap.add_argument("--output", type=Path, default=ROOT / "tmp/raw-summary-66.json")
    args = ap.parse_args()
    if args.self_test:
        result = self_test()
    else:
        args.scratch = args.scratch.resolve()
        args.scratch.mkdir(parents=True, exist_ok=True)
        result = {"status": "NOT_RUN", "base": BASE, "host": platform.node(), "platform": platform.platform(),
                  "python": platform.python_version(), "modes": [], "caps": {"wall_seconds": 20, "cpu_seconds": 20,
                  "address_space_gib_linux": 16, "lean_threads": 1, "lean_stack_kib": 32768},
                  "limitations": ["Diagnostic forces include digest/traversal overhead; no matched speedup inferred.",
                  "Isolated probes have separate prerequisites and caps; their times are not additive.",
                  "Microprobe result:true is only a completion token, never an entailment answer.",
                  "Legacy GNU-time peak RSS can be absent on a killed group; null is not zero.",
                  "No optimization, new checked theorem, independent review, or n=6 completion is claimed."]}
        paths = list((ROOT / "lean/Subtail").glob("*.lean"))
        paths += [Path(__file__).resolve(), ROOT / "scripts/subtail.py", ROOT / "experiments/profile_raw_backend.py", ROOT / "experiments/check_fast_summary.py", ROOT / "experiments/check_entailment_decision.py"]
        result["source_sha256"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths if p.is_file()}
        missing = [name for name in EXPECTED_BLOBS if not (ROOT / name).is_file()]
        blobs = {}
        for name in EXPECTED_BLOBS:
            if (ROOT / name).is_file():
                data = (ROOT / name).read_bytes()
                blobs[name] = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        result["critical_git_blob_sha1"] = blobs
        result["critical_source_mismatch"] = [name for name, sha in blobs.items() if sha != EXPECTED_BLOBS[name]]
        native = args.run and not missing and not result["critical_source_mismatch"] and shutil.which("lake") is not None
        result["missing_sources"] = missing
        result["lake_available"] = shutil.which("lake") is not None
        if args.run and not native:
            result["status"] = "NOT_READY"
        if native:
            version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT / "lean", text=True).strip()
            result["lean_version"] = version
            if "version 4.33.1," not in version:
                raise RuntimeError("Pinned Lean 4.33.1 required")
            result["checked_revision"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            sys.path.insert(0, str(ROOT / "experiments"))
            import profile_raw_backend as legacy
            import check_fast_summary as fast
            legacy.PHASES.update(PHASES)
            result["status"] = "PASS"
        for n in args.n or [6]:
            for mode in args.mode or MODES:
                code = source(n, mode)
                path = args.scratch / f"n{n}-{mode}.lean"
                path.write_text(code)
                row = {"n": n, "mode": mode, "source": str(path), "generated_source_sha256": hashlib.sha256(code.encode()).hexdigest(), "status": "NOT_RUN"}
                if native:
                    if mode == "baseline":
                        marker = f"RAW66_BASELINE:n{n}:"
                        row.update(check_baseline(fast.run_generated_source(path, marker, 20.0, 1), marker))
                        row["meaning"] = "Complete current cached raw entailment endpoint, uninstrumented #eval; independently expected false"
                    else:
                        row.update(legacy.run(path, 20.0, mode != "phased"))
                        row["meaning"] = "Instrumented complete raw query" if mode == "phased" else "Isolated diagnostic completion, NOT entailment"
                        if mode != "phased":
                            row["probe_completed"] = row.pop("actual", None)
                    if row["status"] == "FAIL":
                        result["status"] = "FAIL"
                    elif row["status"] == "UNKNOWN" and result["status"] != "FAIL":
                        result["status"] = "UNKNOWN"
                result["modes"].append(row)
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "output": str(args.output)}))
    return 1 if result["status"] == "FAIL" else 2 if result["status"] in ("NOT_READY", "UNKNOWN") else 0

if __name__ == "__main__":
    raise SystemExit(main())
