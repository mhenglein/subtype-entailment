import Subtail

-- Audit runtime definitions separately from their correctness proofs.
-- Propositional extensionality in erased library proofs is permitted;
-- classical choice must not supply data to an executable algorithm.
#print axioms Subtail.witnessCheck
#print axioms Subtail.lrs
#print axioms Subtail.finiteBudgetDecision

-- These statements remain subject to their printed, explicit hypotheses.
#print axioms Subtail.witnessCheck_correct
#print axioms Subtail.incomingLe_iff_flags
#print axioms Subtail.lrs_spec
#print axioms Subtail.profile_truncation
#print axioms Subtail.visited_profile_truncation
#print axioms Subtail.suffix_trace_truncation
#print axioms Subtail.finiteBudgetDecision_correct
