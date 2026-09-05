# September 5 terminal continuation

Extends [C021-C029 and E016-E020](CONTINUATION.md). The base checkpoint is
`7edc9f7`. **Unrestricted Problem 1.7 is not settled.** This continuation
establishes an exact terminal converse, a nonregular actual separating
language, an arithmetic decision for flat terminal graphs, and a complete
four-state terminal census. New proofs are not Lean-checked.

## Claims and evidence

| ID | Exact statement | Evidence and scope |
|---|---|---|
| C030 | Every k-state binary terminal-final BorderAvoid instance has an always-satisfiable normalized subtype realization on 2k+1 variables, with exactly the same witness words and budgets. | [Construction and proof](../notes/2026-09-05-terminal-realization.md), E021. Arbitrary flags and Bad; all accepting states must be terminal. |
| C031 | Terminal-final BorderAvoid and normalized Problem 1.7 have equivalent decidability through C030, C029, and the audited forward bridge. | Same proof. Not a complexity equivalence or a full arbitrary-BorderAvoid converse. |
| C032 | A nine-variable normalized system has exactly the terminal separating paths 0^m 1 0^(n+1) 1 with n>=m>=0; this language is nonregular. | Same proof, E022. Refutes a finite automaton for all such witnesses, not a decision procedure for their existence. |
| C033 | Fixed word skeletons with unbounded nonnegative exponents have an exact Presburger translation. Flat terminal candidate graphs have a finite complete skeleton cover and hence a decision procedure. | [Arithmetic proof](../notes/2026-09-05-terminal-arithmetic.md), E023. Implements/audits the memo's fixed-skeleton claim. Practical solver caps retain UNKNOWN. |
| C034 | All normalized binary terminal-final instances with at most four states are decided by the exhaustive census: successful budget at most two and witness length at most four, both sharp. | [Normalization and census](../notes/2026-09-05-four-state-terminal.md), E024. Exhaustive finite-case evidence using audited Python graph emptiness; not Lean-checked. No larger-state bound follows. |

## Reproducible experiments

| ID | Command | Recorded coverage |
|---|---|---|
| E021 | `python3 experiments/check_terminal_realization.py` | [Result](../results/terminal-realization.json): 166 instances, 10,458 word comparisons, 83,664 budget-predicate comparisons, 2,985 exact canonical-model checks. |
| E022 | `python3 experiments/check_terminal_nonregular.py` | [Result](../results/terminal-nonregular.json): 2,047 words, 266 exact canonical models, 441 exponent pairs, 465 distinguishability pairs. |
| E023 | `python3 experiments/check_terminal_arithmetic.py` | [Result](../results/terminal-arithmetic.json): 164 fixed-exponent formulas, 8,188 schema-language comparisons, guarded unbounded solver fixtures. Optional Z3 shared library; tested 4.13.3.0. |
| E024 | `python3 experiments/check_four_state_terminal.py` | [Result](../results/four-state-terminal.json): all 65,536 normalized cases; 45,430 YES, 20,106 NO, zero unresolved cases. |

Run all standard-library checks with

```sh
python3 experiments/run_terminal_continuation.py
```

Add `--with-smt` to run E023 as well. The optional arithmetic backend is
separate from the standard-library core. The previous `qe` tactic prototype
failed an independent positive-model check; it is excluded, with the exact
case retained as a regression. Positive arithmetic answers are validated by
both word predicates. Negative answers require agreement from two solver
entry points, not a claim of proof-assistant certification.

## What this changes

The previous suggestion to exploit shared B/A/D structure on the terminal
branch has a precise limit: **every abstract terminal-final instance is
realizable**. Such structure cannot by itself eliminate difficult terminal
flag patterns. Conversely, a theorem for terminal-final automata suffices
for the original normalized subtype problem when combined with C029.

Flat terminal graphs, including several successive unbounded loops and
nonregular witness languages, are now handled arithmetically. What remains
in this route is a complete argument for **nonflat productive recurrent
components**, where a path can alternate different cycles in one component.
A finite complete family of fixed skeletons, or a computable terminal witness
bound, would finish this route. Neither is established here. Merely deleting
loops, merging states, or testing a finite exponent range is insufficient.

The four-state census is a new exact test oracle for further searches and
formalization. It does not turn the terminal budget candidate B<=k-2 into a
general theorem. The main research priority is now A017-style bounded
skeletons for terminal instances, with A012-style complete nonexistence
certificates as an alternative. Preserve the distinction between a finite
representation deciding existence and a finite automaton recognizing every
witness: C032 rules out the latter in general.
