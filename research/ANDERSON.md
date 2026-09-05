# Source-border continuation: C039-C040 / E027

Base checkpoint: `af6cde5`. **Unrestricted Problem 1.7 remains open.**

- **C039:** for a deterministic `n`-state terminal automaton, if a set of
  border-cut states `T` is forward closed among live nonfinal states, existence
  of a `T`-unbordered accepted word implies one of length at most `6n+1`.
  This is a written adaptation of Anderson et al. Theorem 58.
- **C040:** applying C039 to the outgoing flags of one source state gives a
  sound all-state impossibility/pruning certificate. States proved impossible
  can be added to Bad before rerunning C037. The source-only forward-closed
  class is decided exactly.
- **E027:** `python3 experiments/check_terminal_anderson.py` validates the
  implementation and guards. It proves all 16 negative cases among C037's 288
  four-state cyclic leftovers, with zero false certificates against the C034
  oracle; 272 positives remain UNKNOWN. A 700-instance seeded soundness run
  includes 315,840 direct word checks.

[Proof and limitations](../notes/2026-09-05-source-border-anderson.md).

Next target: target sets that are not forward closed. A border chain moves
strictly toward the terminal end and has at most `k` distinct target states by
C036. Try an induction on the number of flag/nonflag region changes along such
chains; forward-closed targets are the rank-zero case.
