# Integrated binary normal forms and final-letter profile contraction

Date: 2026-09-08 integration of repaired PR #12. Canonical claims: C060-C061. Canonical experiment: E038.

**Status: written proof + reproduced finite checks; independent review pending; not Lean-checked. Problem 1.7 remains open.**

The complete original branch proof is preserved verbatim at [the archived PR #12 proof](archive/2026-09-06-run-profile-normalization-branch.txt). Its provisional claim/experiment numbers were branch-local and are superseded by the canonical identifiers above.

## C060 — uniform bounded-data binary normal form

For any binary BorderAvoid instance with `k` states, replace every original transition by a two-bit path under the uniform injective code

    0 -> 00
    1 -> 10.

Original states remain at even code boundaries; one unannotated helper is used for each original state. Flags, Bad states, starts and finals stay on the original boundary copies. The result has exactly `2k` states, and its accepted language is exactly the code image of the original language.

Because every flagged endpoint is a code boundary and the code has fixed length, a flagged suffix-prefix agreement exists after coding exactly when the corresponding original agreement existed before coding. Hence witnesshood is preserved exactly. Every nonempty coded word ends in `0` and has no consecutive `1`s, so the whole binary problem embeds in a class whose data runs between occurrences of the final bit have length zero or one.

This is not the unsound operation of appending a fresh delimiter; every symbol in both compared occurrences is recoded.

## C061 — full-profile final-letter contraction without terminality

For any nonempty accepted binary word, let `b` be its final letter and `a` the other letter. Write the unique decomposition

    a^n_0 b a^n_1 b ... a^n_(r-1) b,

with `n_i >= 0`. No marker is inserted: `b` is already part of the word.

Complete the unary `a` transition by an absorbing sink. The state reached after a long exponent and every aligned equal-tail state-pair set depend only on finite transient information, small exact differences, and residues modulo the finite cycle-period LCM. Contract the sorted distinct large `n_i` values by shrinking only sufficiently large adjacent gaps while preserving:

- equality and weak order of all run lengths;
- all small pairwise differences exactly;
- all large differences modulo the unary period;
- the endpoint and visited-state set of each unary run;
- every later-block equality guard in the full suffix-agreement decomposition.

The resulting accepted word is no longer than the original and has exactly the same endpoint, visited-state set, run-start states, and **complete ordered state-pair agreement profile**. Therefore it preserves witnesshood simultaneously for every flag relation and Bad set on that DFA. Accepting states need not be terminal.

With `d` distinct data-run lengths, the contracted total length is effectively bounded by a polynomial in the number `r` of occurrences of the final letter, with an explicit finite unary-period factor depending on the automaton. This controls magnitudes for a supplied occurrence count; it does **not** give a computable unrestricted bound on how many occurrences are needed by some witness.

The repaired implementation materializes iterable inputs to `join_runs` once before validation, so list, tuple and one-shot-generator forms now have identical semantics.

## E038 — reproduction

Run:

    python3 experiments/check_run_profiles.py
    python3 experiments/check_consolidation_regressions.py

The first checker covers small unary orbit tables, exact tail-pair profiles, defined small words, long contractions, arbitrary flags/Bad annotations, large encoded integers, final-bit slicing, the uniform coding reduction, and complete acyclic wrapper oracles. The second checker contains the review regression that `join_runs([1,2])`, `join_runs((1,2))`, and `join_runs(iter([1,2]))` produce the same word.

[Implementation](../experiments/run_profiles.py), [main checker](../experiments/check_run_profiles.py), [integration regression](../experiments/check_consolidation_regressions.py).
