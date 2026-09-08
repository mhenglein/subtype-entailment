# Research consolidation — 2026-09-08

This record documents the controlled integration of the reviewed research PR stack #6–#14 onto main `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status:** integration/provenance record. The imported mathematical arguments remain at their recorded evidence levels: written proofs plus reproducible experiments unless a pre-existing Lean result is explicitly cited. This consolidation does not independently formalize them and does not solve unrestricted Problem 1.7.

## Integration policy

Current `main` is authoritative for shared navigation and historical state. Old branch copies of `STATE.md`, `research/claims.md`, approach registries, generated trackers, and conjecture indexes were not replayed wholesale. This prevents later main-branch work from being overwritten and avoids collisions where different branches reused the same provisional C/E identifiers.

Only non-conflicting proof notes, implementations, and independent checkers were imported. Q002 and Q003 are updated separately because the integrated modular counterexample refutes them outright.

## Canonical result map

The following identifiers are the consolidation names for discussion and future ledger promotion. Branch-local identifiers in old notes are historical aliases and must not be assumed globally unique.

| Canonical | Origin | Result |
|---|---|---|
| C046 | PR #6 | Exact modular synchronization family; Q002/Q003 counterexample and superpolynomial terminal budget lower family. |
| C047 | PR #6 | No universal constant bound on simultaneous equal-state loop deletions. |
| C048 | PR #8 | Direct binary whole-word synchronization for supplied DFA intersections. |
| C049 | PR #8 | PSPACE-hardness transfer for the recorded top-free subtype fragment. |
| C050 | PR #8 | Fixed-word skeleton / concatenation-description lower bound from the counting intersection. |
| C051 | PR #9 | Five-state NO instance defeating every finite Necessary(L,D) emptiness search. |
| C052 | PR #9 | Exact PSPACE-complete decision for supplied bounded delimited schemas with arbitrary logical flags. |
| C053 | PR #9 | Automatic exact decision for the certified bounded-marker raw-input class. |
| C054 | PR #10 | Witness-preserving normalization of target-free prefixes relative to a fixed reference suffix. |
| C055 | PR #10 | Common-reference powerset/convolution solver for unknown reference words. |
| C056 | PR #10 | Exact target-frontier class with unbounded early marker cycles and no productive marker cycle reachable from a relevant target. |
| C057 | PR #13 | Universal terminal maximal-run normalization preserving the complete agreement profile and visited states. |
| C058 | PR #13 | NP-completeness of witness existence with a supplied unary maximal-run bound; fixed-run exact search. |
| C059 | PR #11 | Target-local finite pending-context pump and exact decision when flag targets have bounded marker tails. |

These names reserve a collision-free sequence for subsequent promotion into `research/claims.md`; this file itself does not upgrade review status.

## Retained implementations and regressions

The consolidation imports and CI-runs:

- `check_modular_sync.py` / `modular_sync_family.py`;
- the alternative `terminal_copy.py` / `check_terminal_copy.py` implementation from PR #7 as differential evidence, not a second canonical numbering;
- `word_sync.py`, `counter_intersection.py`, `check_word_sync.py`;
- `delimited_blocks.py`, `marker_certificate.py`, and their checkers;
- `target_frontier.py` and `check_target_frontier.py`;
- `target_tail.py` and `check_target_tail.py`;
- `run_normalization.py`, `run_bound_decision.py`, and `check_run_normalization.py`.

The consolidated CI job executes all of them together, which is stronger integration evidence than the old branch-local runs because it checks dependency compatibility on one tree.

## Held back after review

### PR #12 — run-profile normalization

Scientifically distinct and potentially valuable, but not included in this first merge. `run_profiles.join_runs` consumes a one-shot iterable during validation and then silently returns the empty word on a second pass. The central theorem's internal tuple callers are not falsified by that helper bug, but the reviewed head is not merged with a known API defect. Repair, add generator/list/tuple parity regressions, reconcile its marker-count notation with the later minimum-violation `mu`, then re-review.

### PR #14 — regular-family verification / shared-lasso continuation

The shared-orbit backend reproduces its reported 43,069 backend agreements, but the reviewed head is held back because:

1. the shared-lasso minimum-violation theorem needs an explicit boundary-safe hypothesis (or a revised total violation convention);
2. the one-flag note imported C021 as a terminal lower bound even though C021 is nonterminal;
3. its original global-minimum conclusion needed an all-bad-word argument, not merely the displayed subfamily;
4. the committed result JSON was not byte-for-byte the checker's output and the new checkers were not wired into CI;
5. the MSO obstruction note lacked a traceable primary citation.

The PR review contains a repair for item 3 for the displayed four-state instance. None of these issues imply that the orbit implementation is unsound or that unrestricted Problem 1.7 is decided.

## Scientific frontier after consolidation

The strongest positive normalization now controls run **lengths given their number**, and the target-frontier/target-tail solvers decide broader certified recurrent classes. The strongest negative evidence shows that neither the sharp `k-2` budget, strict profile descent, fixed necessary-budget emptiness, nor a constant number of loop deletions can close the problem.

The remaining general obligation is still a computable, existence-preserving control of arbitrary nonflat recurrent structure—equivalently a complete finite symbolic cover or another terminating exact procedure. Large arithmetic exponents are not themselves the obstruction; uncontrolled essential repeated structure is.
