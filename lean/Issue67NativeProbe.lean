import Subtail.EntailmentPrepared
import Subtail.RankQueryDecision
import Subtail.TerminalDecisionLazy

/-!
Issue #67 diagnostics only. Every solver/graph/compiler below is imported
unchanged. Phase readback is separate from direct endpoint calls; it is not
an assertion that a reference was automatically selected by the solver.
-/
open Subtail
open Subtail.RankQuery Subtail.RankQueryDecision Subtail.RankQueryEnumeration
open Subtail.TerminalDecisionLazy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Issue67NativeProbe

def emit (key value : String) : IO Unit := do
  let out <- IO.getStdout
  out.putStrLn ("ISSUE67:" ++ key ++ "=" ++ value)
  out.flush

def chain (n : Nat) (flags : List (Prod Nat Nat)) (bad : List Nat)
    (hasFinal : Bool := true) : Instance (n + 1) where
  initial := 0
  transitions := Vector.ofFn fun q =>
    (if h : q.val + 1 < n + 1 then some (Fin.mk (q.val + 1) h) else none, none)
  final := Vector.ofFn fun q => hasFinal && q.val == n
  bad := Vector.ofFn fun q => bad.contains q.val
  flags := Vector.ofFn fun q => Vector.ofFn fun r => flags.contains (q.val, r.val)

def reference (n m : Nat) : Reference (n + 1) where
  word := List.replicate m false
  label := fun j => Fin.mk (n - j) (Nat.lt_succ_of_le (Nat.sub_le n j))

def runChain (action : String) (n : Nat) (variant : String) : IO Unit := do
  let flags := match variant with
    | "ordered" => [(0, 1)]
    | "reversed" => [(1, 0)]
    | "diagonal" => [(1, 1)]
    | "empty-suffix" => [(0, n)]
    | "empty-diagonal" => [(0, 0)]
    | _ => []
  let bad := if variant == "bad" then [0] else []
  let I := chain n flags bad (variant != "no-final")
  emit "action" action
  emit "states" (toString (n + 1))
  emit "variant" variant
  if action == "direct" then
    emit "begin" "RankQueryDecision.terminalWitnessCheck"
    let answer := terminalWitnessCheck I
    emit "result" (toString answer)
  else if action == "lazy" then
    emit "begin" "TerminalDecisionLazy.terminalWitnessCheckLazy"
    let answer := terminalWitnessCheckLazy I
    emit "result" (toString answer)
  else if action == "inspect" then
    emit "witness" (toString (witnessCheck I (List.replicate n false)))
    emit "empty_witness" (toString (witnessCheck I []))
    emit "safe_one_letter" (toString (safeOneLetterExists I))
    let f := finishQuery I
    emit "finish_clauses" (toString f.length)
    for c in f do
      emit "budget" (reprStr (Subtail.RankQueryCoverage.budget c))
    for m in List.range n do
      let B := reference n (m + 1)
      let safe := safeReferenceCheck I B
      emit ("safe_at_" ++ toString (m + 1)) (toString safe)
      if safe then
        emit ("finish_at_" ++ toString (m + 1))
          (toString (satCheck (prefixGraph I B) f))
    emit "inspection_complete" "true"
  else if action == "phases" then
    emit "safe_one_letter" (toString (safeOneLetterExists I))
    let mut phi := finishQuery I
    emit "finish_clauses" (toString phi.length)
    for h in List.range (n - 1) do
      emit "begin_preimage" (toString (h + 1))
      let pulled := preimage I Subtail.RankQueryCoverage.budget phi
      emit "preimage_clauses" (toString pulled.length)
      phi := phi ++ pulled
      emit "completed_promotion" (toString (h + 1))
    emit "begin" "terminalCandidateScan"
    emit "result" (toString (terminalCandidateScan I phi))
  else
    throw (IO.userError "unknown chain action")

open Subtail.ExpressionNormalization

def leftSpine : Nat -> Expr 0
  | 0 => .bot
  | n + 1 => .prod (leftSpine n) .bot

/-- Exact ground expressions: their constructor-address sets are finite unary
prefixes. Guard readback is diagnostic, then the real public endpoint runs. -/
def runFrontend (variant : String) : IO Unit := do
  let G : Input 0 := []
  let s := leftSpine (if variant == "positive" then 3 else 4)
  let t := leftSpine (if variant == "positive" then 4 else 3)
  let C := normalized G s t
  let a := (naming G s t).ref s
  let b := (naming G s t).ref t
  emit "frontend_guard_readback" "begin"
  let pos := Subtail.EntailmentFast.positiveCheck C a b
  emit "positive_guard" (toString pos)
  if pos then
    emit "frontend_branch" "positive_guard"
  else
    let P := Subtail.EntailmentPrepared.prepare (Subtail.CanonicalReachability.systemOf C)
    let sat := Subtail.EntailmentPrepared.satCheck C P
    emit "premises_satisfiable" (toString sat)
    if !sat then
      emit "frontend_branch" "inconsistent_premises"
    else
      let paths := Subtail.EntailmentFast.candidatePaths G s t
      let sep := paths.any (Subtail.EntailmentPrepared.separationCheck C P a b)
      emit "candidate_separation" (toString sep)
      emit "frontend_branch" (if sep then "candidate_path" else "raw_backend")
  emit "begin" "EntailmentPrepared.entailsCheck"
  emit "result" (toString (Subtail.EntailmentPrepared.entailsCheck G s t))

end Issue67NativeProbe

def main (args : List String) : IO Unit := do
  match args with
  | ["frontend", variant] => Issue67NativeProbe.runFrontend variant
  | [action, length, variant] =>
    match length.toNat? with
    | some n => Issue67NativeProbe.runChain action n variant
    | none => throw (IO.userError "invalid chain length")
  | _ => throw (IO.userError "usage: action length variant | frontend variant")
