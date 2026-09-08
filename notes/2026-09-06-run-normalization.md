# Integrated terminal maximal-run normalization

Date: 2026-09-08 integration of PR #13. Canonical claims: C057-C058. Canonical experiment: E037.

**Status: written proof + reproduced finite checks; independent review pending; not Lean-checked. Problem 1.7 remains open.**

The complete branch proof is preserved verbatim at [the archived PR #13 proof](archive/2026-09-06-run-normalization-branch.txt). Its provisional labels `C054-C055` and `E035` were branch-local and are superseded by the canonical identifiers above.

## C057 — exact normalization with a supplied run count

For every defined binary word ending at a terminal accepting state, write the word as `r` maximal homogeneous runs. There is a no-longer accepted word with the same run letters, the same states at all run boundaries, the same visited-state set, and the **same complete suffix-agreement profile**. Therefore every flag relation and Bad annotation is preserved simultaneously.

The construction compresses gaps between sorted distinct run counts rather than truncating counts independently. With `H=(k+1)^2` and the applicable unary cycle period `P`, each new run length is bounded by `r(H+P)` and the total length by `r^2(H+P)`. The period may be restricted to cycles reached from the actual run starts because those starts are preserved inductively.

The final, potentially partial match in the profile decomposition uses an inequality, not an equality. Terminality also bounds the last homogeneous run. These details are part of the archived proof and regression.

**Limit:** C057 bounds run magnitudes **given `r`**. It proves no computable unrestricted bound on the number of runs needed by some witness.

## C058 — supplied maximal-run decision

Given a terminal binary BorderAvoid instance and a maximal-run bound `R` in unary, witness existence with at most `R` maximal homogeneous runs is NP-complete. Membership uses C057 plus the symbolic profile verifier on binary-encoded counts. Hardness is by positive unary-DFA intersection with equality-of-length flags.

For each fixed `R`, finite enumeration is polynomial with degree depending on `R`. The executable solver returns `YES`, `NO_WITHIN_RUN_BOUND`, or `UNKNOWN`; a bounded negative is never unrestricted `NO`.

## E037 — reproduction

Run:

    python3 experiments/check_run_normalization.py

The checker compares symbolic and direct/reversed profiles, exhausts small terminal tables, exercises large encoded counts, validates the explicit independent-truncation counterexample, checks bounded-run queries against complete finite-language oracles, and tests the unary-intersection compiler. The all-input statements above rest on the written proof, not on those finite samples.

[Normalizer](../experiments/run_normalization.py), [bounded-run solver](../experiments/run_bound_decision.py), [checker](../experiments/check_run_normalization.py).
