import Subtail.CanonicalReachability
import Subtail.CanonicalModelAudit

/-!
Small kernel-evaluated regressions of the executable definitions. No native_decide
or unproved oracle is used. The quantified correctness theorems are separate.
-/
namespace Subtail
namespace StackSummaryAudit
open StackSummary StackReachability TreeSemantics CanonicalReachability

set_option maxRecDepth 10000

def matching : System 2 where
  eps _ _ := false
  push a p q := !a && decide (p = 0 ∧ q = 1)
  pop a p q := !a && decide (p = 1 ∧ q = 1)

def mismatched : System 2 where
  eps _ _ := false
  push a p q := !a && decide (p = 0 ∧ q = 1)
  pop a p q := a && decide (p = 1 ∧ q = 1)

def popping : System 1 where
  eps _ _ := false
  push _ _ _ := false
  pop a _ _ := !a

theorem matching_balanced : balancedCheck matching 0 1 = true := by decide
theorem mismatched_not_balanced : balancedCheck mismatched 0 1 = false := by decide
theorem matching_empty_reachable : Reaches matching (0,[]) (1,[]) := by
  exact (reachesCheck_correct _ _ _ _ _).mp (by decide)
theorem mismatched_empty_unreachable : ¬ Reaches mismatched (0,[]) (1,[]) := by
  intro h
  have hh := (reachesCheck_correct _ _ _ _ _).mpr h
  have hf : reachesCheck mismatched 0 [] 1 [] = false := by decide
  rw [hf] at hh
  cases hh
theorem mismatched_control_reachable : controlReachCheck mismatched 0 [] 1 = true := by decide
theorem matching_common_tail : reachesCheck matching 0 [true,false] 1 [true,false] = true := by decide
theorem common_tail_not_rewritten : reachesCheck matching 0 [true] 1 [false] = false := by decide
theorem pop_at_empty_fails : reachesCheck popping 0 [] 0 [false] = false := by decide
theorem pop_consumes_untouched : reachesCheck popping 0 [false,false] 0 [] = true := by decide
theorem wrong_pop_symbol_fails : reachesCheck popping 0 [true] 0 [] = false := by decide

theorem empty_system_satisfiable : satCheck ([] : List (Constraint 0)) = true := by decide
theorem infinite_spine_satisfiable : satCheck CanonicalModelAudit.spineConstraints = true := by decide
theorem forced_denial_inconsistent : satCheck CanonicalModelAudit.contradictory = false := by decide
theorem spine_empty_separator : separationCheck CanonicalModelAudit.spineConstraints 0 1 [] = true := by decide
theorem spine_nonempty_separator : separationCheck CanonicalModelAudit.spineConstraints 0 1 [false,false] = true := by decide
theorem reflexive_query_has_no_separator : separationCheck CanonicalModelAudit.spineConstraints 0 0 [] = false := by decide
theorem inconsistent_has_no_separator : separationCheck CanonicalModelAudit.contradictory 0 1 [] = false := by decide

end StackSummaryAudit
end Subtail
