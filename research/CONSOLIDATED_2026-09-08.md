# Consolidated continuation records — 2026-09-08

Base: current `main` at `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status:** canonical pending-review records for reusable results from PRs #6–#14. These IDs extend the repository vocabulary without promoting any result to `AUDIT` or `LEAN`. Problem 1.7 remains open.

Older PR descriptions and notes may use provisional C/E numbers that collided across branches. C046–C064 below are canonical after consolidation.

## Summary map

| ID | Canonical statement | Primary source |
|---|---|---|
| C046 | Modular terminal synchronization refutes Q002/Q003 and gives superpolynomial terminal budgets | `../notes/2026-09-05-modular-synchronization.md` |
| C047 | No universal constant simultaneous-loop-deletion bound | same note |
| C048 | Direct binary whole-word synchronization | `../notes/2026-09-05-word-synchronization.md` |
| C049 | Top-free bottom/product entailment and non-entailment are PSPACE-hard via C048+C030 | same note |
| C050 | Fixed-word skeleton / ordinary SLP description lower bounds | same note |
| C051 | Five-state failure of finite Necessary-budget completeness | `../notes/2026-09-06-delimited-convolution.md` |
| C052 | Supplied delimited-schema witness existence is PSPACE-complete | same note |
| C053 | Exact raw marker certificate for the bounded-marker class | same note |
| C054 | Fixed-reference target-free-prefix pending pump | `../notes/2026-09-06-target-frontier.md` |
| C055 | Common-reference convolution for certified target schemas | same note |
| C056 | Exact target-frontier class with no target-reachable marker cycle | same note |
| C057 | Universal terminal maximal-run profile normalization given run count | `../notes/2026-09-06-run-normalization.md` |
| C058 | Supplied unary maximal-run bound problem is NP-complete | same note |
| C059 | Target-local bounded-marker-tail pump and exact class | `../notes/2026-09-06-target-local-pumping.md` |
| C060 | Uniform 2k bounded-data-run binary normal form | `../notes/2026-09-06-run-profile-normalization.md` |
| C061 | Full-profile final-letter run contraction without terminality | same note |
| C062 | Supplied regular-family universal verification is PSPACE-complete | `../notes/2026-09-07-regular-family-complexity.md` |
| C063 | Shared-lasso witness arithmetic and boundary-safe minimum-violation thresholds are Presburger-definable | `../notes/2026-09-08-shared-lasso-presburger.md` |
| C064 | Four-state one-flag language has unbounded last-aligned spectrum but global bad-word minimum exactly one | `../notes/2026-09-08-oneflag-minimum-gap.md` |

## Canonical records

<a id="c046"></a>
### C046 — Modular terminal synchronization
**Claim.** The modular terminal family has exact equal-block witness language; the `(2,3)` eight-state instance has shortest witness length 14 and exact budget 7, refuting Q002/Q003. Period families give superpolynomial terminal budgets.
**Status.** `WRITTEN PROOF + REPRO + COUNTEREXAMPLE`; independent review pending.
**Evidence.** [Proof](../notes/2026-09-05-modular-synchronization.md); [result](../results/modular-synchronization.json).

<a id="c047"></a>
### C047 — Simultaneous deletion lower bound
**Claim.** A terminal family requires an unbounded number of simultaneous equal-state loop deletions to obtain the exhibited shorter profile-dominated word, ruling out a universal constant deletion count.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Modular synchronization note](../notes/2026-09-05-modular-synchronization.md).

<a id="c048"></a>
### C048 — Direct whole-word synchronization
**Claim.** A polynomial binary terminal BorderAvoid construction has witnesses exactly equal coded copies of a word accepted by every supplied DFA.
**Status.** `WRITTEN PROOF + REPRO`; PR #7 retained as independent implementation evidence.
**Evidence.** [Proof](../notes/2026-09-05-word-synchronization.md); [result](../results/word-synchronization.json).

<a id="c049"></a>
### C049 — Fragment-specific PSPACE hardness
**Claim.** Through C048 and the recorded C030 realization, top-free bottom/product non-entailment is PSPACE-hard on always-satisfiable normalized inputs; complement closure gives entailment hardness.
**Status.** `WRITTEN PROOF`; inherits C030's evidence boundary.
**Evidence.** [Word synchronization note](../notes/2026-09-05-word-synchronization.md).

<a id="c050"></a>
### C050 — Skeleton description lower bound
**Claim.** An explicit polynomial-size DFA-intersection family has a unique counting witness requiring superpolynomial body size in fixed-word power skeletons and ordinary concatenation SLPs.
**Status.** `WRITTEN PROOF + REPRO`; no claim about every compressed representation.
**Evidence.** [Word synchronization note](../notes/2026-09-05-word-synchronization.md).

<a id="c051"></a>
### C051 — Necessary-budget incompleteness
**Claim.** A fixed five-state terminal NO instance has nonempty `Necessary(L,D)` language for every finite `L,D`, although its witness language is empty.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Delimited-convolution note](../notes/2026-09-06-delimited-convolution.md).

<a id="c052"></a>
### C052 — Supplied delimited-schema decision
**Claim.** Witness existence in a supplied finite delimited-block schema with arbitrary logical boundary flags is PSPACE-complete and exactly decidable by reverse padded convolution.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Delimited-convolution note](../notes/2026-09-06-delimited-convolution.md); [result](../results/delimited-blocks.json).

<a id="c053"></a>
### C053 — Raw bounded-marker certificate
**Claim.** The paired/unary raw marker-format class with no productive marker cycle admits an effective finite complete schema cover and exact decision.
**Status.** `WRITTEN PROOF + REPRO`; outside the certificate the result is `UNKNOWN`.
**Evidence.** [Delimited-convolution note](../notes/2026-09-06-delimited-convolution.md); [result](../results/marker-certificate.json).

<a id="c054"></a>
### C054 — Fixed-reference prefix pump
**Claim.** Given a target-containing reference suffix, a target-free prefix can be shortened by repeating `(macro state, pending obligations)` memories while preserving witnesshood relative to that same suffix.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Target-frontier note](../notes/2026-09-06-target-frontier.md).

<a id="c055"></a>
### C055 — Common-reference schema solver
**Claim.** A finite reverse convolution chooses all reference words consistently while a powerset tracks every possible earlier-block observation, yielding an exact decision for each supplied target-frontier schema.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Target-frontier note](../notes/2026-09-06-target-frontier.md); [result](../results/target-frontier.json).

<a id="c056"></a>
### C056 — Target-frontier certified raw class
**Claim.** In the verified marker formats, if no productive marker cycle is reachable from an effective flag target, the raw instance is exactly decidable by a finite target-frontier cover.
**Status.** `WRITTEN PROOF + REPRO`; recurrent target-marker cycles remain outside this theorem.
**Evidence.** [Target-frontier note](../notes/2026-09-06-target-frontier.md).

<a id="c057"></a>
### C057 — Terminal maximal-run profile normalization
**Claim.** Every accepted terminal binary word can be replaced by a no-longer word with the same maximal-run letters, run-boundary states, visited states, and full agreement profile, with run lengths effectively bounded as a function of state count and supplied run count.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Run-normalization note](../notes/2026-09-06-run-normalization.md); [result](../results/run-normalization.json).

<a id="c058"></a>
### C058 — Bounded-run complexity
**Claim.** Terminal witness existence with a supplied maximal-run bound `R` encoded in unary is NP-complete; the executable bounded search returns `NO_WITHIN_RUN_BOUND`, never unrestricted NO.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Run-normalization note](../notes/2026-09-06-run-normalization.md).

<a id="c059"></a>
### C059 — Target-local marker-tail pump
**Claim.** In the marker format, if every effective target has bounded remaining marker height, a finite pending-context pump gives an existential marker bound and exact decision for that certified class.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Target-local note](../notes/2026-09-06-target-local-pumping.md); [result](../results/target-tail.json).

<a id="c060"></a>
### C060 — Uniform bounded-data binary normal form
**Claim.** The uniform code `0->00, 1->10` gives a 2k-state witness-preserving reduction in which nonempty outputs have data runs of length at most one.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Run-profile note](../notes/2026-09-06-run-profile-normalization.md).

<a id="c061"></a>
### C061 — Global final-letter profile contraction
**Claim.** For every accepted binary word, including nonterminal acceptance, an effective contraction of the lengths between occurrences of the final letter preserves endpoint, visited states, and the full state-pair agreement profile.
**Status.** `WRITTEN PROOF + REPRO`; no computable bound on the number of final-letter occurrences is proved.
**Evidence.** [Run-profile note](../notes/2026-09-06-run-profile-normalization.md); [result](../results/run-profiles.json).

<a id="c062"></a>
### C062 — Supplied regular-family verification
**Claim.** Given an annotated binary instance and an unannotated regular domain, deciding whether every domain member is a witness is PSPACE-complete; the lower-bound construction uses one forbidden ordered pair.
**Status.** `WRITTEN PROOF + REPRO`; this is universal verification, not existential witness synthesis.
**Evidence.** [Corrected proof](../notes/2026-09-07-regular-family-complexity.md); [result](../results/regular-family-orbits.json).

<a id="c063"></a>
### C063 — Shared-lasso Presburger arithmetic
**Claim.** Witness parameter vectors of every supplied shared-lasso skeleton are effectively Presburger-definable. On the explicitly boundary-safe bad subdomain, the relation `mu(w)>H` for minimum proper violation length is also Presburger-definable.
**Status.** `WRITTEN PROOF`; independent review pending.
**Evidence.** [Corrected note](../notes/2026-09-08-shared-lasso-presburger.md).
**Limit.** The minimum-violation equivalence is not asserted for merely admissible words with diagonal, Bad, nonfinal, or empty-suffix failures.

<a id="c064"></a>
### C064 — One-flag last-aligned/minimum separation
**Claim.** A four-state terminal one-flag instance has unbounded realizable last-aligned violation lengths, while every bad accepted word has minimum proper violation length exactly one.
**Status.** `WRITTEN PROOF + REPRO`.
**Evidence.** [Corrected note](../notes/2026-09-08-oneflag-minimum-gap.md); [integration regression](../results/consolidation-regressions.json).
**Limit.** No C021 nonterminal shortest-word lower bound is transferred to the terminal one-flag class.

## Alternative implementations retained

PR #7's `terminal_copy.py` is independent implementation evidence for C046/C048. PR #11's `target_tail.py` is a separate target-local implementation and differential check; C057 uses PR #13's active-period terminal normalizer.

## Explicit non-results

None of C046–C064 decides unrestricted Problem 1.7. Exact supplied-schema/family solvers do not provide a finite cover of arbitrary nonflat productive components; run-length contractions do not bound the number of essential runs; and the two-ended MSO audit makes no undecidability claim.
