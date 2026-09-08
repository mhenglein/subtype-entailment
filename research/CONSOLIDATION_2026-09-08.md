# Research consolidation — 2026-09-08

This is the supplemental canonical ledger for the controlled integration of reviewed PRs #6–#14. Earlier C001–C045/E001–E028 records remain authoritative in their original ledgers.

**Evidence rule.** `WRITTEN PROOF + REPRO` does not mean Lean-checked or independently refereed. Unrestricted Problem 1.7 remains open. Parallel research branches reused provisional IDs; the collision-free IDs below are canonical after consolidation.

## Canonical claims

<a id="c046"></a>
### C046 — Exact modular synchronization and terminal budget lower family

**Statement.** For periods `p_1,...,p_r`, an explicit flat binary terminal instance has witness language exactly `(1^N0)^r` for positive multiples `N` of `lcm(p_i)`, exact budget `(r-1)(lcm(p_i)+1)`, and unique shortest witness `(1^P0)^r`. The eight-state `(2,3)` instance has budget 7, refuting Q002 and Q003 at `k-2=6`. Periods `1,...,m` give `2^(Omega(sqrt(k)))` terminal budgets.

**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted decision or undecidability result.

**Record.** [Proof](../notes/2026-09-05-modular-synchronization.md), [checker](../experiments/check_modular_sync.py).

<a id="c047"></a>
### C047 — No constant simultaneous-loop-deletion bound

**Statement.** An explicit terminal family can require edits in all `r` blocks before reaching the exhibited shorter profile-dominated word; no state-independent constant number of simultaneous equal-state loop deletions suffices.

**Status / scope.** `WRITTEN PROOF + REPRO`; no claim against a computable state-dependent bound.

**Record.** [Proof](../notes/2026-09-05-modular-synchronization.md).

<a id="c048"></a>
### C048 — Direct binary whole-word synchronization

**Statement.** A supplied tuple of binary DFAs can be compiled in polynomial size to a binary terminal BorderAvoid instance whose witnesses are exactly repeated encodings of one common word accepted by every DFA. Product reachability exactly decides this constructed subclass.

**Status / scope.** `WRITTEN PROOF + REPRO`; construction-specific, not an arbitrary-instance decomposition theorem.

**Record.** [Implementation](../experiments/word_sync.py), [checker](../experiments/check_word_sync.py).

<a id="c049"></a>
### C049 — Fragment-specific PSPACE hardness

**Statement.** DFA intersection nonemptiness reduces through C048 and the recorded terminal realization C030 to non-entailment over the top-free bottom/product subtype fragment; complement closure gives entailment hardness.

**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted PSPACE upper bound follows.

**Record.** [Proof/implementation](../notes/2026-09-05-word-synchronization.md).

<a id="c050"></a>
### C050 — Fixed-word skeleton and concatenation-description lower bound

**Statement.** A polynomial-size DFA family has singleton intersection equal to a counting word with exponentially many distinct factors, forcing superpolynomial body size for the stated fixed-word power skeletons and ordinary concatenation descriptions.

**Status / scope.** `WRITTEN PROOF + REPRO`; richer shared-word/regular-constraint representations are not excluded.

**Record.** [Counting construction](../experiments/counter_intersection.py).

<a id="c051"></a>
### C051 — Every finite Necessary budget can miss a fixed NO instance

**Statement.** A five-state flat terminal instance has empty witness language, yet every finite `Necessary(L,D)` language is nonempty; `1^n 0 1^(n+1) 0` has exactly one violation with suffix length `n+1` and gap `n+2`.

**Status / scope.** `WRITTEN PROOF + REPRO`; refutes completeness of that negative semiprocedure, not soundness of an individual Necessary certificate.

**Record.** [Proof](../notes/2026-09-06-delimited-convolution.md).

<a id="c052"></a>
### C052 — Exact arbitrary-flag bounded delimited schemas

**Statement.** Witness existence for a supplied finite delimited-block schema with arbitrary logical flags is exactly decidable by reverse padded convolution and is PSPACE-complete.

**Status / scope.** `WRITTEN PROOF + REPRO`; not a finite cover theorem for arbitrary raw instances.

**Record.** [Solver](../experiments/delimited_blocks.py), [checker](../experiments/check_delimited_blocks.py).

<a id="c053"></a>
### C053 — Exact bounded-marker raw-input certificate

**Statement.** The verified paired/unary raw marker-format class with aligned annotations and no productive marker cycle admits a finite complete schema cover and exact decision.

**Status / scope.** `WRITTEN PROOF + REPRO`; unsupported formats/cycles/caps remain `UNKNOWN`.

**Record.** [Certificate](../experiments/marker_certificate.py).

<a id="c054"></a>
### C054 — Fixed-reference target-free prefix normalization

**Statement.** Relative to one actual target-containing reference suffix, earlier target-free blocks can be pumped by a finite `(macro state, pending-context)` monitor while preserving witnesshood.

**Status / scope.** `WRITTEN PROOF + REPRO`; G-specific witness preservation, not unconditional profile descent.

**Record.** [Proof](../notes/2026-09-06-target-frontier.md).

<a id="c055"></a>
### C055 — Common-reference powerset/convolution solver

**Statement.** Unknown reference words can be chosen consistently by one reverse convolution while a powerset tracks all earlier-block observations relative to that same tuple, giving an exact supplied-schema decision.

**Status / scope.** `WRITTEN PROOF + REPRO`; not unrestricted BorderAvoid.

**Record.** [Implementation](../experiments/target_frontier.py).

<a id="c056"></a>
### C056 — Exact target-frontier class with unbounded early marker cycles

**Statement.** In the verified marker formats, arbitrarily many productive marker cycles may occur before relevant targets. If no productive marker cycle is reachable from a relevant target, a finite first-target reference cover plus C055 decides the raw slice exactly.

**Status / scope.** `WRITTEN PROOF + REPRO`; target-reachable marker cycles remain outside this certificate.

**Record.** [Checker](../experiments/check_target_frontier.py).

<a id="c057"></a>
### C057 — Universal terminal maximal-run normalization

**Statement.** Every defined binary word ending at a terminal accepting state has a no-longer word with the same maximal-run letters, run-boundary states, visited-state set, and complete suffix-agreement profile, with run magnitudes bounded effectively once the run count is supplied.

**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted bound on the number of runs is proved.

**Record.** [Proof](../notes/2026-09-06-run-normalization.md), [normalizer](../experiments/run_normalization.py).

<a id="c058"></a>
### C058 — Supplied maximal-run witness existence is NP-complete

**Statement.** With maximal-run bound `R` supplied in unary, terminal witness existence is NP-complete. Executable bounded negatives are `NO_WITHIN_RUN_BOUND`, never unrestricted NO.

**Status / scope.** `WRITTEN PROOF + REPRO`; the missing unrestricted run-count bound remains explicit.

**Record.** [Solver](../experiments/run_bound_decision.py).

<a id="c059"></a>
### C059 — Target-local finite pending-context pump

**Statement.** When every effective target has finite marker distance to final, protecting that final block suffix and pumping repeated pending-context memories yields an existential marker bound and exact decision for the certified class.

**Status / scope.** `WRITTEN PROOF + REPRO`; missing format, target-reachable marker cycles, and caps remain `UNKNOWN`.

**Record.** [Proof](../notes/2026-09-06-target-local-pumping.md).

<a id="c060"></a>
### C060 — Uniform bounded-data binary normal form

**Statement.** The uniform code `0 -> 00`, `1 -> 10` gives an exact 2k-state witness-preserving reduction in which every nonempty accepted output ends in 0 and has data runs of length at most one. Flags and Bad annotations remain on original-state boundaries.

**Status / scope.** `WRITTEN PROOF + REPRO`; this is an exact reduction, not a general solver.

**Record.** [Proof](../notes/2026-09-06-run-profile-normalization.md), [checker](../experiments/check_run_profiles.py).

<a id="c061"></a>
### C061 — Full-profile final-letter run contraction

**Statement.** For every accepted binary word, including nonterminal accepting states, an effective contraction of the data-run lengths between occurrences of the word's final letter preserves endpoint, visited states, and the complete state-pair suffix-agreement profile. The repaired implementation accepts lists, tuples, and single-pass iterables consistently.

**Status / scope.** `WRITTEN PROOF + REPRO`; no computable bound on the number of final-letter occurrences is proved.

**Record.** [Proof](../notes/2026-09-06-run-profile-normalization.md), [implementation](../experiments/run_profiles.py), [review regression](../experiments/check_consolidation_regressions.py).

<a id="c062"></a>
### C062 — Supplied regular-family universal verification is PSPACE-complete

**Statement.** Given an annotated binary instance and an unannotated regular domain, deciding whether every domain member is a witness is PSPACE-complete. The lower-bound construction uses a single forbidden ordered pair and explicitly forces equality of all successive blocks.

**Status / scope.** `WRITTEN PROOF + REPRO`; this is universal verification of a supplied family, not existential mixed-family witness synthesis.

**Record.** [Corrected proof](../notes/2026-09-07-regular-family-complexity.md), [backend](../experiments/regular_family_orbits.py), [deterministic evidence wrapper](../experiments/check_regular_family_orbits_canonical.py).

<a id="c063"></a>
### C063 — Shared-lasso Presburger arithmetic

**Statement.** Witness parameter vectors of any supplied shared-lasso skeleton are effectively Presburger-definable. On the explicitly **boundary-safe** bad subdomain, the relation `mu(w) > H` for minimum proper violation length is also Presburger-definable, so the corresponding threshold set is effectively semilinear.

**Status / scope.** `WRITTEN PROOF`; independent review pending. The minimum-violation equivalence is not asserted for merely admissible words with diagonal, Bad, nonfinal, or empty-suffix failures.

**Record.** [Corrected proof](../notes/2026-09-08-shared-lasso-presburger.md).

<a id="c064"></a>
### C064 — One flag separates last-aligned growth from global minimum growth

**Statement.** A four-state terminal instance with one forbidden pair has unbounded realizable last-aligned violation lengths, while **every bad accepted word** has minimum proper violation length exactly one.

**Status / scope.** `WRITTEN PROOF + REPRO`; no C021 nonterminal shortest-word lower bound is transferred to the terminal one-flag class.

**Record.** [Corrected proof](../notes/2026-09-08-oneflag-minimum-gap.md), [review regression](../experiments/check_consolidation_regressions.py).

## Canonical experiments

<a id="e029"></a>
### E029 — Alternative terminal-copy synchronization regression
**Command.** `python3 experiments/check_terminal_copy.py`

<a id="e031"></a>
### E031 — Modular synchronization regression
**Command.** `python3 experiments/check_modular_sync.py`

<a id="e032"></a>
### E032 — Whole-word synchronization and counting regression
**Command.** `python3 experiments/check_word_sync.py`

<a id="e033"></a>
### E033 — Delimited convolution and Necessary-hierarchy regression
**Command.** `python3 experiments/check_delimited_blocks.py`

<a id="e034"></a>
### E034 — Raw marker-certificate regression
**Command.** `python3 experiments/check_marker_certificate.py`

<a id="e035"></a>
### E035 — Target-frontier regression
**Command.** `python3 experiments/check_target_frontier.py`

<a id="e036"></a>
### E036 — Target-local pending-context regression
**Command.** `python3 experiments/check_target_tail.py`

<a id="e037"></a>
### E037 — Terminal maximal-run normalization regression
**Command.** `python3 experiments/check_run_normalization.py`

<a id="e038"></a>
### E038 — Arbitrary-acceptance run-profile contraction regression
**Command.** `python3 experiments/check_run_profiles.py`

**Evidence / scope.** Exact symbolic/direct profile comparisons, bounded-data encoding, last-symbol slicing, recurrent-target fixtures, and huge symbolic counts. The join-runs iterable regression is also run in E041.

<a id="e039"></a>
### E039 — Supplied regular-family orbit verification
**Command.** `python3 experiments/check_regular_family_orbits_canonical.py`

**Evidence / scope.** 43,069 exact backend agreements, 23,781 independently checked counterexamples, complete finite-family oracles, and finite lower-bound construction checks. The wrapper writes deterministic committed evidence.

<a id="e040"></a>
### E040 — One-flag minimum-gap family
**Command.** `python3 experiments/check_oneflag_minimum_gap.py`

**Evidence / scope.** Checks the explicit all-parameter construction over a large finite range and both witness predicates. The strengthened all-bad-word finite regression is E041.

<a id="e041"></a>
### E041 — Consolidation review regressions
**Command.** `python3 experiments/check_consolidation_regressions.py`

**Evidence / scope.** Guards the PR #12 single-pass iterable bug and exhausts all binary words through length 16 for the strengthened C064 whole-bad-language characterization. Finite testing supports but does not replace the all-length proofs.

## Logical shortcut audit

[The two-ended MSO audit](../notes/2026-09-08-two-ended-mso-audit.md) now records only the established orientation/definability gap in the naive Rabin/S2S shortcut. It withdraws the earlier untraceable enriched-MSO undecidability claim and makes no undecidability inference for Subtail.

## Frontier

PR #12 and PR #14 are no longer held back: the concrete review defects have been repaired and their checks are wired into the combined integration gate. Their claims remain at the evidence levels stated above.

Large arithmetic exponents are manageable once a finite synchronization schema is known. The remaining general obligation is effective, existence-preserving control of arbitrary nonflat recurrent structure: a computable essential-run/schema bound, a finite symbolic cover, another terminating exact procedure, or a genuine undecidability reduction for the normalized subtype fragment.
