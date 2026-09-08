# Consolidated continuation experiments — 2026-09-08

The open research PRs were developed in parallel and reused provisional E IDs. This file preserves those historical references while assigning unique canonical IDs to the retained executable checks. E001–E028 in `README.md` are unchanged.

## Historical provisional aliases

These records exist so older imported notes resolve honestly. Do not cite a colliding alias as a unique experiment; use the canonical ID below.

<a id="e029"></a>
### E029 — Legacy alias: terminal-copy synchronization
Historical PR #7 label. Canonical executable record: **E038**.

<a id="e031"></a>
### E031 — Legacy alias: modular synchronization
Historical PR #6 label. Canonical executable record: **E037**.

<a id="e032"></a>
### E032 — Legacy alias: word synchronization
Historical PR #8 label. Canonical executable record: **E039**.

<a id="e033"></a>
### E033 — Legacy alias: delimited convolution
Historical PR #9 label. Canonical executable record: **E040**.

<a id="e034"></a>
### E034 — Legacy alias: raw marker certificate
Historical PR #9 label. Canonical executable record: **E041**.

<a id="e035"></a>
### E035 — Legacy collision
This provisional ID was independently used for **target-frontier saturation** (now E042) and **terminal maximal-run normalization** (now E045). It is intentionally not a scientific experiment identifier after consolidation.

<a id="e036"></a>
### E036 — Legacy collision
This provisional ID was independently used for **target-local marker-tail pumping** (now E043) and **nonterminal final-letter run-profile contraction** (now E044). It is intentionally not a scientific experiment identifier after consolidation.

## Canonical retained experiments

<a id="e037"></a>
### E037 — Modular synchronization and Q002/Q003 counterexample
**Command.** `python3 experiments/check_modular_sync.py`

**Scope.** Replays the explicit modular family, the eight-state exact-budget counterexample, subtype bridge checks, and simultaneous-deletion fixtures.

**Recorded result.** [modular-synchronization.json](../results/modular-synchronization.json).

**Claims informed.** C046, C047.

<a id="e038"></a>
### E038 — Independent terminal-copy synchronization implementation
**Command.** `python3 experiments/check_terminal_copy.py`

**Scope.** Independent implementation evidence for the modular/copy constructions, including product decisions and encoded subtype checks. It is retained as differential evidence, not a competing canonical claim set.

**Recorded result.** [terminal-copy.json](../results/terminal-copy.json).

**Claims informed.** C046, C048, C049.

<a id="e039"></a>
### E039 — Direct binary whole-word synchronization
**Command.** `python3 experiments/check_word_sync.py`

**Scope.** Tests the direct binary compiler/product solver and counting-word description lower-bound fixtures.

**Recorded result.** [word-synchronization.json](../results/word-synchronization.json).

**Claims informed.** C048–C050.

<a id="e040"></a>
### E040 — Delimited reverse convolution
**Command.** `python3 experiments/check_delimited_blocks.py`

**Scope.** Tests exact supplied-schema convolution, whole-block context guards, finite/cyclic oracles, and the five-state Necessary-budget obstruction.

**Recorded result.** [delimited-blocks.json](../results/delimited-blocks.json).

**Claims informed.** C051, C052.

<a id="e041"></a>
### E041 — Raw marker certificate
**Command.** `python3 experiments/check_marker_certificate.py`

**Scope.** Tests the exact raw paired/unary bounded-marker certificate; unsupported formats/cycles and caps remain `UNKNOWN`.

**Recorded result.** [marker-certificate.json](../results/marker-certificate.json).

**Claims informed.** C053.

<a id="e042"></a>
### E042 — Common-reference target frontier
**Command.** `python3 experiments/check_target_frontier.py`

**Scope.** Tests the common-reference powerset construction, early marker cycles, finite source-observation sets, exact YES/NO fixtures, and cap guards.

**Recorded result.** [target-frontier.json](../results/target-frontier.json).

**Claims informed.** C054–C056.

<a id="e043"></a>
### E043 — Target-local marker-tail pumping
**Command.** `python3 experiments/check_target_tail.py`

**Scope.** Independent target-local implementation and pumping evidence when target-to-final marker height is bounded.

**Recorded result.** [target-tail.json](../results/target-tail.json).

**Claims informed.** C059.

<a id="e044"></a>
### E044 — Arbitrary-acceptance run-profile contraction
**Command.** `python3 experiments/check_run_profiles.py`

**Scope.** Tests the bounded-data encoding, last-symbol slicing, exact full-profile numeric contraction including recurrent targets, and wrapper oracles.

**Recorded result.** [run-profiles.json](../results/run-profiles.json).

**Claims informed.** C060, C061.

<a id="e045"></a>
### E045 — Terminal maximal-run normalization and bounded-run decision
**Command.** `python3 experiments/check_run_normalization.py`

**Scope.** Tests exact maximal-run profile normalization, huge symbolic counts, the partial-final-run inequality, bounded-run oracles, and unary-intersection hardness fixtures.

**Recorded result.** [run-normalization.json](../results/run-normalization.json).

**Claims informed.** C057, C058.

<a id="e046"></a>
### E046 — Supplied regular-family orbit verification
**Command.** `python3 experiments/check_regular_family_orbits_canonical.py`

**Scope.** Runs the full orbit regression and writes deterministic evidence: 43,069 backend agreements, 23,781 independently checked counterexamples, complete finite-family oracles, and finite lower-bound construction checks.

**Recorded result.** [regular-family-orbits.json](../results/regular-family-orbits.json).

**Claims informed.** C062.

<a id="e047"></a>
### E047 — One-flag minimum-gap family
**Command.** `python3 experiments/check_oneflag_minimum_gap.py`

**Scope.** Checks the explicit square family and forward/reversed predicates through the recorded bounded range. The all-word strengthening is additionally guarded by E048.

**Recorded result.** [oneflag-minimum-gap.json](../results/oneflag-minimum-gap.json).

**Claims informed.** C064.

<a id="e048"></a>
### E048 — Consolidation review regressions
**Command.** `python3 experiments/check_consolidation_regressions.py`

**Scope.** Guards the single-pass `join_runs` bug found in PR #12 review and exhausts all binary words through length 16 for the strengthened one-flag bad-language characterization.

**Recorded result.** [consolidation-regressions.json](../results/consolidation-regressions.json).

**Claims informed.** C061 implementation interface, C064.

All continuation commands are replayed together by the `consolidated-continuation` GitHub Actions job. Passing finite regressions do not promote the associated written proofs to `AUDIT` or `LEAN`.
