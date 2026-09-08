# Consolidated continuation records — 2026-09-08

Base: current `main` at `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status:** integration map for written proofs and reproduced experiments from PRs #6–#14. These IDs extend the repository's stable vocabulary without promoting the records to `AUDIT` or `LEAN`. Problem 1.7 remains open.

This file resolves the branch-local claim-number collisions. Older PR descriptions and notes may use a different provisional C/E number; the IDs below are canonical for the consolidated continuation.

| ID | Canonical statement | Primary source | Status |
|---|---|---|---|
| C046 | Modular terminal synchronization has exact witness language `(1^N0)^r` at common period; the 8-state `(2,3)` instance refutes Q002/Q003 and the family gives superpolynomial terminal budgets | `notes/2026-09-05-modular-synchronization.md`, PR #6 | WRITTEN PROOF + REPRO; pending independent review |
| C047 | No universal constant number of simultaneous equal-state loop deletions suffices for profile descent | same note, PR #6 | WRITTEN PROOF + REPRO |
| C048 | Direct binary whole-word synchronization compiles supplied DFA intersection into terminal BorderAvoid | `notes/2026-09-05-word-synchronization.md`, PR #8; PR #7 retained as independent implementation evidence | WRITTEN PROOF + REPRO |
| C049 | Through C048 and C030, the always-satisfiable top-free bottom/product fragment is PSPACE-hard for both entailment and non-entailment | same note | WRITTEN PROOF; dependency on recorded C030 status |
| C050 | Fixed-word power skeletons and ordinary concatenation SLPs can require superpolynomial descriptions on the counting intersection family | same note | WRITTEN PROOF + REPRO |
| C051 | A fixed 5-state terminal NO instance defeats every finite Necessary budget while having empty witness language | `notes/2026-09-06-delimited-convolution.md`, PR #9 | WRITTEN PROOF + REPRO |
| C052 | Witness existence for a supplied finite delimited-block schema with arbitrary boundary flags is PSPACE-complete | same note | WRITTEN PROOF + REPRO |
| C053 | A checkable raw marker-format class with no productive marker cycle has an exact finite schema cover | same note | WRITTEN PROOF + REPRO |
| C054 | For a fixed target-containing reference suffix, target-free prefix blocks admit a finite pending-context pump | `notes/2026-09-06-target-frontier.md`, PR #10 | WRITTEN PROOF + REPRO |
| C055 | A common-reference reverse convolution chooses reference words consistently and decides each certified target-frontier schema | same note | WRITTEN PROOF + REPRO |
| C056 | If no productive marker cycle is reachable from an effective flag target, the raw formatted instance is exactly decidable | same note | WRITTEN PROOF + REPRO |
| C057 | Every accepted terminal binary word has a no-longer word with the same maximal-run letters, run-boundary states, visited states and full agreement profile, with run lengths effectively bounded given the run count | `notes/2026-09-06-run-normalization.md`, PR #13 | WRITTEN PROOF + REPRO |
| C058 | Terminal witness existence with a supplied maximal-run bound `R` in unary is NP-complete; bounded negative verdicts are not unrestricted NO | same note | WRITTEN PROOF + REPRO |
| C059 | In the marker format, bounded marker-tail height from every flag target gives a finite pending-context pump and exact decision for that target-local class | `notes/2026-09-06-target-local-pumping.md`, PR #11 | WRITTEN PROOF + REPRO |
| C060 | Uniform coding `0->00, 1->10` embeds every binary instance into a 2k-state form whose data runs have length at most one while preserving witnesses | `notes/2026-09-06-run-profile-normalization.md`, PR #12 | WRITTEN PROOF + REPRO |
| C061 | For any accepted binary word, contraction of final-letter-separated data-run lengths preserves the entire state-pair agreement profile, visited states and endpoint, without terminality | same note | WRITTEN PROOF + REPRO; no global marker-count bound |
| C062 | Universal verification of a supplied regular candidate family is PSPACE-complete, already with one forbidden pair in the lower-bound construction | `notes/2026-09-07-regular-family-complexity.md`, PR #14 corrected | WRITTEN PROOF + REPRO |
| C063 | Witness vectors of any supplied shared-lasso schema are Presburger-definable; on the **boundary-safe** bad subdomain, threshold growth of the minimum proper violation is Presburger-definable too | `notes/2026-09-08-shared-lasso-presburger.md`, PR #14 corrected | WRITTEN PROOF; pending independent review |
| C064 | A 4-state terminal one-flag instance has an unbounded last-aligned violation spectrum while **every** bad accepted word has minimum proper violation length one | `notes/2026-09-08-oneflag-minimum-gap.md`, PR #14 corrected | WRITTEN PROOF + REPRO |

## Alternative implementations retained

PR #7's `terminal_copy.py` is retained as independent implementation evidence for the modular/copy synchronization line, not as a competing set of canonical claims. PR #11's `target_tail.py` is retained as a separate target-local implementation and differential evidence; PR #13 supplies the canonical terminal maximal-run normalizer.

## Explicit non-results

None of C046–C064 decides unrestricted Problem 1.7. In particular:

- large exponents and exact run-length contraction do not bound the **number** of essential runs/markers;
- exact supplied-schema and supplied-family solvers do not provide a complete cover of arbitrary nonflat productive components;
- C063 requires boundary safety for its minimum-violation equivalence;
- C064 does not import C021's nonterminal `3k-3` lower bound into the terminal one-flag class;
- `notes/2026-09-08-two-ended-mso-audit.md` only identifies a missing relation in the naive Rabin/S2S shortcut and makes no undecidability claim.

## Integration regressions

The combined CI must run the retained checkers from PRs #6–#14 plus `experiments/check_consolidation_regressions.py`. Resource-capped algorithms preserve `UNKNOWN`; bounded-run negatives remain `NO_WITHIN_RUN_BOUND`.
