import Subtail

-- Audit runtime definitions separately from their correctness proofs.
-- Propositional extensionality in erased library proofs is permitted;
-- classical choice must not supply data to an executable algorithm.
#print axioms Subtail.witnessCheck
#print axioms Subtail.lrs
#print axioms Subtail.finiteBudgetDecision
#print axioms Subtail.boundaryCheck
#print axioms Subtail.admissibleCheck
#print axioms Subtail.necessaryCheck
#print axioms Subtail.suffixBoundCheck
#print axioms Subtail.sufficientCheck
#print axioms Subtail.twoStateWitnessCheck

-- These statements remain subject to their printed, explicit hypotheses.
#print axioms Subtail.witnessCheck_correct
#print axioms Subtail.incomingLe_iff_flags
#print axioms Subtail.lrs_spec
#print axioms Subtail.profile_truncation
#print axioms Subtail.visited_profile_truncation
#print axioms Subtail.suffix_trace_truncation
#print axioms Subtail.finiteBudgetDecision_correct
#print axioms Subtail.boundaryCheck_correct
#print axioms Subtail.witness_iff_finalSlice_proper
#print axioms Subtail.necessary_zero_iff_boundary
#print axioms Subtail.boundary_witness_of_length_le_one
#print axioms Subtail.admissibleCheck_correct
#print axioms Subtail.necessaryCheck_correct
#print axioms Subtail.suffixBoundCheck_correct
#print axioms Subtail.sufficientCheck_correct
#print axioms Subtail.suffixBound_iff_reverseSuffixBound
#print axioms Subtail.witness_implies_necessary
#print axioms Subtail.sufficient_implies_witness
#print axioms Subtail.witness_implies_sufficient_lrs
#print axioms Subtail.exists_short_witness_two_states
#print axioms Subtail.twoStateWitnessCheck_correct
