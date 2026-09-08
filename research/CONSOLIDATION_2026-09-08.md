# Research consolidation — 2026-09-08

This is the supplemental canonical ledger for the controlled integration of reviewed PRs #6–#14 onto main.

**Evidence rule.** Entries below preserve their stated evidence levels. `WRITTEN PROOF + REPRO` does not mean Lean-checked or independently refereed. Unrestricted Problem 1.7 remains open.

Current main remains authoritative for earlier C001–C045/E001–E028 records and approach history. Historical branch notes sometimes used provisional IDs that collided across branches; the IDs below are canonical after consolidation.

## Canonical claims

<a id="c046"></a>
### C046 — Exact modular synchronization and terminal budget lower family
**Statement.** Explicit flat binary terminal instances force equal modular block lengths. The eight-state `(2,3)` instance has exact budget 7 at `k=8`, refuting Q002/Q003; periods `1,...,m` give `2^(Omega(sqrt(k)))` terminal budget growth.
**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted decision result.
**Record.** [Proof](../notes/2026-09-05-modular-synchronization.md), [checker](../experiments/check_modular_sync.py).

<a id="c047"></a>
### C047 — No constant simultaneous-loop-deletion bound
**Statement.** A terminal family can require edits in all `r` synchronized unary blocks to obtain the exhibited shorter profile-dominated word.
**Status / scope.** `WRITTEN PROOF + REPRO`; no claim against state-dependent bounds.
**Record.** [Proof](../notes/2026-09-05-modular-synchronization.md).

<a id="c048"></a>
### C048 — Direct binary whole-word synchronization
**Statement.** Supplied binary DFAs compile in polynomial size to a terminal BorderAvoid instance whose witnesses are repeated encodings of one common word accepted by every DFA.
**Status / scope.** `WRITTEN PROOF + REPRO`; construction-specific.
**Record.** [Implementation](../experiments/word_sync.py), [checker](../experiments/check_word_sync.py).

<a id="c049"></a>
### C049 — Fragment-specific PSPACE hardness
**Statement.** DFA intersection reduces through C048 and C030 to top-free bottom/product non-entailment; complement closure gives entailment hardness.
**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted PSPACE upper bound.
**Record.** [Word-sync checker](../experiments/check_word_sync.py).

<a id="c050"></a>
### C050 — Fixed-word skeleton and concatenation-description lower bound
**Statement.** A polynomial-size DFA family has a singleton counting-word intersection forcing superpolynomial body size in the stated fixed-word skeletons and ordinary concatenation SLPs.
**Status / scope.** `WRITTEN PROOF + REPRO`; richer representations are not excluded.
**Record.** [Counting construction](../experiments/counter_intersection.py).

<a id="c051"></a>
### C051 — Every finite Necessary budget can miss a fixed NO instance
**Statement.** A five-state flat terminal instance has empty witness language but nonempty `Necessary(L,D)` for every finite `L,D`.
**Status / scope.** `WRITTEN PROOF + REPRO`; refutes one negative semiprocedure, not individual certificate soundness.
**Record.** [Proof](../notes/2026-09-06-delimited-convolution.md).

<a id="c052"></a>
### C052 — Exact arbitrary-flag bounded delimited schemas
**Statement.** Supplied finite delimited schemas with arbitrary logical flags/Bad annotations are exactly decidable by reverse padded convolution; the supplied-schema problem is PSPACE-complete.
**Status / scope.** `WRITTEN PROOF + REPRO`; not a cover theorem for arbitrary raw inputs.
**Record.** [Solver](../experiments/delimited_blocks.py).

<a id="c053"></a>
### C053 — Exact bounded-marker raw-input certificate
**Statement.** Verified paired/unary raw marker formats with no productive marker cycle admit an effective finite complete schema cover and exact decision.
**Status / scope.** `WRITTEN PROOF + REPRO`; unsupported inputs/caps remain `UNKNOWN`.
**Record.** [Certificate](../experiments/marker_certificate.py).

<a id="c054"></a>
### C054 — Fixed-reference target-free prefix normalization
**Statement.** Relative to a fixed target-containing reference suffix, a finite pending-context monitor pumps earlier target-free blocks while preserving witnesshood.
**Status / scope.** `WRITTEN PROOF + REPRO`; G-specific preservation.
**Record.** [Proof](../notes/2026-09-06-target-frontier.md).

<a id="c055"></a>
### C055 — Common-reference powerset/convolution solver
**Statement.** One reverse convolution chooses reference words consistently while a powerset tracks all possible earlier-block observations relative to that same tuple.
**Status / scope.** `WRITTEN PROOF + REPRO`; exact for supplied target-frontier schemas.
**Record.** [Implementation](../experiments/target_frontier.py).

<a id="c056"></a>
### C056 — Exact target-frontier class with unbounded early marker cycles
**Statement.** In verified marker formats, arbitrarily many early productive marker cycles are permitted if no productive marker cycle is reachable from a relevant target.
**Status / scope.** `WRITTEN PROOF + REPRO`; target-reachable marker cycles remain outside the certificate.
**Record.** [Checker](../experiments/check_target_frontier.py).

<a id="c057"></a>
### C057 — Universal terminal maximal-run normalization
**Statement.** Every defined binary word ending at a terminal final has a no-longer word with the same maximal-run letters, run-boundary states, visited-state set and complete suffix-agreement profile, with run magnitudes bounded from state count and supplied run count.
**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted run-count bound.
**Record.** [Integrated proof](../notes/2026-09-06-run-normalization.md).

<a id="c058"></a>
### C058 — Supplied maximal-run witness existence is NP-complete
**Statement.** With `R` supplied in unary, terminal witness existence with at most `R` maximal runs is NP-complete; fixed `R` admits exact finite enumeration.
**Status / scope.** `WRITTEN PROOF + REPRO`; bounded negatives are not unrestricted NO.
**Record.** [Solver](../experiments/run_bound_decision.py).

<a id="c059"></a>
### C059 — Target-local finite pending-context pump
**Statement.** When effective targets have finite marker distance `h` to final, protecting the final `h` blocks and pumping repeated `(macro state,pending-context)` memories gives an existential marker bound and exact decision for the certified class.
**Status / scope.** `WRITTEN PROOF + REPRO`.
**Record.** [Integrated proof](../notes/2026-09-06-target-local-pumping.md).

<a id="c060"></a>
### C060 — Uniform bounded-data binary normal form
**Statement.** The uniform code `0->00, 1->10` gives an exact `2k`-state witness-preserving binary reduction whose nonempty outputs end in `0` and have data runs of length at most one.
**Status / scope.** `WRITTEN PROOF + REPRO`; exact reduction, not a decision theorem.
**Record.** [Integrated proof](../notes/2026-09-06-run-profile-normalization.md), [implementation](../experiments/run_profiles.py).

<a id="c061"></a>
### C061 — Full-profile final-letter contraction without terminality
**Statement.** For every accepted binary word, including nonterminal acceptance, an effective contraction of lengths between occurrences of the final letter preserves endpoint, visited states and the complete state-pair agreement profile.
**Status / scope.** `WRITTEN PROOF + REPRO`; no computable bound on the number of final-letter occurrences is proved.
**Record.** [Integrated proof](../notes/2026-09-06-run-profile-normalization.md), [checker](../experiments/check_run_profiles.py).

<a id="c062"></a>
### C062 — Supplied regular-family verification is PSPACE-complete
**Statement.** Given an annotated binary instance and an unannotated regular domain, deciding whether every domain member is a witness is PSPACE-complete; the lower-bound construction uses one forbidden ordered pair.
**Status / scope.** `WRITTEN PROOF + REPRO`; universal family verification, not existential witness synthesis.
**Record.** [Corrected proof](../notes/2026-09-07-regular-family-complexity.md), [backend](../experiments/regular_family_orbits.py).

<a id="c063"></a>
### C063 — Shared-lasso Presburger arithmetic
**Statement.** Witness parameter vectors of every supplied shared-lasso skeleton are effectively Presburger-definable. On the explicitly boundary-safe bad subdomain, the relation `mu(w)>H` for minimum proper violation length is also Presburger-definable.
**Status / scope.** `WRITTEN PROOF`; independent review pending. The minimum-violation equivalence is not asserted for merely admissible words with boundary failures.
**Record.** [Corrected proof](../notes/2026-09-08-shared-lasso-presburger.md).

<a id="c064"></a>
### C064 — One-flag last-aligned/minimum separation
**Statement.** A four-state terminal one-flag instance has unbounded realizable last-aligned violation lengths, while every bad accepted word has minimum proper violation length exactly one.
**Status / scope.** `WRITTEN PROOF + REPRO`; no C021 nonterminal lower bound is transferred to the terminal class.
**Record.** [Corrected proof](../notes/2026-09-08-oneflag-minimum-gap.md), [checker](../experiments/check_oneflag_minimum_gap.py).

## Canonical experiments

<a id="e029"></a>
### E029 — Alternative terminal-copy synchronization regression
**Command.** `python3 experiments/check_terminal_copy.py`
**Scope.** Differential implementation evidence for C046/C048.

<a id="e031"></a>
### E031 — Modular synchronization regression
**Command.** `python3 experiments/check_modular_sync.py`

<a id="e032"></a>
### E032 — Whole-word synchronization/counting regression
**Command.** `python3 experiments/check_word_sync.py`

<a id="e033"></a>
### E033 — Delimited convolution/Necessary regression
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
### E038 — Nonterminal final-letter profile-contraction regression
**Command.** `python3 experiments/check_run_profiles.py`
**Scope.** Small exact profiles, long contractions, large encoded counts, coding/slicing and complete finite oracles.

<a id="e039"></a>
### E039 — Supplied regular-family verification regression
**Command.** `python3 experiments/check_regular_family_orbits_canonical.py`
**Scope.** Replays 43,069 exact backend agreements and writes deterministic committed evidence.

<a id="e040"></a>
### E040 — One-flag minimum-gap regression
**Command.** `python3 experiments/check_oneflag_minimum_gap.py`
**Scope.** Explicit family and bounded-language checks supporting C064.

<a id="e041"></a>
### E041 — Review-repair integration regression
**Command.** `python3 experiments/check_consolidation_regressions.py`
**Scope.** One-shot-iterator parity for C060/C061 code and all-bad-word minimum-one verification through length 16 for C064.

## Frontier

Large arithmetic exponents are manageable once a finite synchronization schema is known. C060-C064 strengthen the supplied-schema/normalization toolkit but do not produce a finite cover of arbitrary nonflat productive components. The remaining general obligation is an effective, existence-preserving control of arbitrary recurrent structure: a computable essential-run/schema bound, a finite symbolic cover, another terminating exact procedure, or a genuine undecidability reduction for the normalized subtype fragment.
