import Lean
import Subtail.PopAcyclic
import Subtail.FiniteTreeDecision
#print axioms Subtail.PopAcyclic.pop_length_lt_of_no_nonempty_loop
#print axioms Subtail.FiniteTreeDecision.growthCheck
#print axioms Subtail.FiniteTreeDecision.growthCheck_correct
#print axioms Subtail.FiniteTreeDecision.growthCheck_false_no_loop
#print axioms Subtail.FiniteTreeDecision.growthCheck_false_bound
#print axioms Subtail.FiniteTreeDecision.push_target_forced
#print axioms Subtail.FiniteTreeDecision.growthCheck_true_noFiniteModel
#print axioms Subtail.FiniteTreeDecision.run
#print axioms Subtail.FiniteTreeDecision.entailsCheck
#print axioms Subtail.FiniteTreeDecision.run_growth_noFiniteModel
#print axioms Subtail.FiniteTreeDecision.run_growth_noFiniteExprModel
#print axioms Subtail.FiniteTreeDecision.entailsCheck_correct
open Lean Elab Command in
run_cmd do
  let names := (← getEnv).constants.toList.filterMap fun (n, _) =>
    if privateToUserName? n == some `Subtail.PopAcyclic.pop_trace then some n else none
  unless names.length == 1 do throwError "Missing or ambiguous private declaration"
  for n in names do
    let axioms ← collectAxioms n
    logInfo m!"'Subtail.PopAcyclic.pop_trace' depends on axioms: {axioms}"
