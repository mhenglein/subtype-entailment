# Original terminal witness bound F: F-only investigation

Date: 2026-09-20. Actor: f-only-astra-20260920. Workstreams A017/A018; issue #69; coordination #37.
Base: 19b06d4fed9da635d9b911f0e908d04e4fc4b099.
Status: EXPLORATORY OUTLINE. No new theorem status, counterexample, independent mathematical review or Lean check is claimed at this checkpoint.

## Exact recorded target

The numerical part of C080 reads:

> Consequently every positive instance has a witness of length at most the explicit computable bound `F(1)=0, F(k)=2(k+1)*prod_{j=1..k-2}(T_j+2)` with `T_0=k+10` and `T_(j+1)=64k*T_j^(2T_j+2)`.

The preceding quantifier is every finite binary terminal instance with k states. The product formula is for k>=2, with the empty product giving F(2)=6. The recorded text does not assign F(0); Instance 0 has no initial state and is uninhabited. Do not add a zero-state mathematical obligation by silently changing this domain.

Precisely, for every k>=1 and I : Subtail.Instance k satisfying Subtail.TerminalRank.TerminalFinals I, prove

    (exists w, Witness I w) iff
    (exists w, Witness I w and length(w) <= F(k)).

The reverse implication is immediate. Only the forward existence of SOME short witness needs proof. Instance consists of a partial deterministic binary transition table, one initial state, arbitrary final and Bad sets, and an arbitrary ordered flag relation. TerminalFinals says every final has no outgoing transition. Witness is exactly Basic.lean: every run prefix, including the initial cut, is defined and not Bad; the endpoint is final; for every 0<=i<=j<=length(w), if suffix j is a prefix of suffix i, the ordered state pair at i,j is unflagged. Diagonal comparisons, the empty suffix and the empty word are included.

A refutation must supply a terminal instance, an actual witness, and a valid all-words proof that no witness of length <=F(k) exists. A long emitted clause, long arbitrary witness, or word resistant to selected deletions is insufficient. Bounded failed search is UNKNOWN, not NO.

## Scope and established dependencies

The old universal concrete compiler weight U is refuted; C082 supplies the larger Uhat_k(T)=64*k*T^(6*T^2+2) and Fhat. Neither alone settles original F. This investigation changes no compiler and does not claim the separate smaller existential compiler question. Core definitions, shared ledgers, imports, toolchain, CI and paper remain read-only.

Use C082 only with its exact generic shared-interval reconstruction contract. It bounds a single jointly generated extension, not independent per-atom words. Current source endpoints include RankQueryLengthBound.compile_bounded, promoted_finish_bounded and terminal_witness_bound_iff. Historical validation is not a fresh run here.

## Proposed route and named obligations

1. Suffix inheritance: when a witness returns to its initial state at positive cut i, its suffix after i is a shorter witness. All comparisons lift by adding i, without a new concatenation seam. Consequently a shortest nonempty witness never revisits its initial state.
2. Proper suffix rank: proper suffixes of such a shortest witness avoid the initial state, so their border-state injection uses at most k-1 states. Their positive border count is at most k-2. This is not yet a statement about a smaller instance or a smaller compiler.
3. OPEN: modify only the finishing query used in the argument so that a first reference return at the final initial-state cut is permitted, but no earlier return is. The existing finish observer forbids every endpoint visit, so merely lowering its promotion count is unjustified. Define the new finite observer, prove exact trace reconstruction including all new comparisons, and bound it with at most k controls and the original seed k+10.
4. OPEN: use proper-prefix milestones and that final-return finishing query to obtain a satisfying one-letter base after at most k-3 promotion preimages for k>=3. Prove coverage and reconstruction separately. Include overlapping returns, coincident cuts, diagonal/empty boundaries and recurrent paths.
5. OPEN: generalize the already checked bounded reconstruction argument to this finishing query, without changing the concrete preimage compiler. This would give length+1 <=2*(k+1)*product_(j=1..k-3)(That_j+2), where That uses C082's larger recurrence.
6. Arithmetic route: prove the one-stage-lag inequality 6*That_j^2 <= T_(j+1), then compare products. This is a candidate elementary induction, not yet checked. A saved promotion would absorb the larger per-stage recurrence and yield the EXACT original F.
7. Handle k=1 and k=2 directly, and the empty witness independently. Finish with the trivial reverse implication.

The weakest sufficient new semantic statement is the one-fewer-promotion existence theorem for this particular finishing query. It does not need small output clauses for all possible queries, preservation of arbitrary witness profiles, or a universal local shortening rule.

## Falsification and preserved failures

Before new searches, read the recorded initial-loop/new-border, overlapping deletion, recurrent-residual and compiler-weight failures. Candidate tests must use an independent literal Witness predicate. Prefer shortest witnesses, certified by exhaustive increasing-length enumeration up to their found length; no assertion of no witness at all follows from a cap. Specifically test a reference returning at the ultimate initial-state cut, overlapping occurrences and nonprimitive loops. Record any failure of the strengthened finishing route separately from F.

## Review and execution boundary

GitHub connector read/write is available. Container has no Lean/Lake; direct git access fails DNS. No full checkout or local full-suite run is claimed. Use isolated partial source copies only when execution is required. No independent reviewer has been launched. Request review of the concrete argument/artifact; a posted request is not an obtained review. Critical intended Lean targets are suffix inheritance/no-initial-return, the sharpened rank count, final-return safety and the recurrence comparison, only after the semantic route survives falsification.

This outline will retain failed attempts and be updated with actual commands, seeds, limits, evidence, remaining obligations and an explicit scope release. No main integration or shared claim promotion is authorized by this investigation.
