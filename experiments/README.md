# Experiment index

This index gives stable IDs for executable checks. Each entry records the
exact command, its scope and limits, the claims it informs, and the JSON keys
that carry its result.

`run_experiments.py` is the original bundled runner, not the whole experiment
index. Run that core check from the repository root with:

```text
python3 experiments/run_experiments.py
```

The command writes [results/independent-checks.json](../results/independent-checks.json)
and prints the same JSON. The implementation uses only the Python standard
library. See [border_lab.py](border_lab.py) for the executable predicates and
the finite reverse-reading automaton.

The current GitHub Actions workflow covers the pre-continuation E001-E015
commands, including the separate checks listed below E008. It does not run
E016-E028 or the additional unnumbered checks at the end of this index. Run
each later command separately when its record says the executable and result
are present.

## Result rules

- `YES` includes a returned witness.
- `NO` means the finite state graph was exhausted for that fixed budget and
  state cap.
- `UNKNOWN` means a resource cap stopped the search. It never means `NO`.
- A passing assertion is bounded regression evidence. It is not a formal proof
  of the whole implementation or of an all-length claim.
- The memo's original `analysis-2026` scripts were unavailable. None of these
  entries reproduces the memo's full source census.

## Executed experiments

<a id="e001"></a>

### E001 — Forward suffix predicates versus reversed borders

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [run_experiments.py](run_experiments.py) calls
`witness` and `border_witness`, implemented in
[border_lab.py](border_lab.py).

**Scope and limits.** Seed `17082026`; 80 generated partial binary DFAs with
`2 <= |K| <= 5`; every binary word of length `0..6` (127 words per instance).
This is 10,160 word comparisons. The check is finite and generator-specific.

**Result keys.** `seed`, `random_instances`, `max_word_length`,
`checks.words_checked`, `failures`.

**Observed result.** `checks.words_checked=10160` and `failures=0`.

**Claims informed.** [C004](../research/claims.md#c004),
[C010](../research/claims.md#c010).

<a id="e002"></a>

### E002 — Direct N/S predicates versus Sandwich automata

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [run_experiments.py](run_experiments.py) compares the
direct predicates with `Sandwich` for
`(L,D) in [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]`.

**Scope and limits.** The same 80 instances and words as E001. It performs
121,920 direct-versus-automaton comparisons and the same number of implication
checks. It also runs the first three budgets with both ordinary and strong
searches, for 480 finite-state searches, each with `max_states=30000`.

**Result keys.** `checks.automaton_comparisons`,
`checks.sandwich_implications`, `checks.finite_state_searches`,
`search_statuses`, `failures`.

**Observed result.** 121,920 comparisons and 121,920 implication checks passed.
The 480 searches returned 282 `YES`, 198 `NO`, and 0 `UNKNOWN`.

**Claims informed.** [C010](../research/claims.md#c010).

<a id="e003"></a>

### E003 — Original, suffix-trace, and profile truncation cuts

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [run_experiments.py](run_experiments.py) checks every
proper prefix of each bounded witness. It tests both
`use_profiles=False` and `use_profiles=True`, then tests the memo's original
first-occurrence truncation hypothesis.

**Scope and limits.** Only the witnesses among E001's 80 generated instances
and words of length at most 6 are examined. Counts include only hypotheses that
apply. They do not measure all possible abstract instances or all witness
lengths.

**Result keys.** `checks.truncations_checked`,
`checks.suffix_trace_cuts`, `checks.profile_dominance_cuts`,
`checks.cuts_on_rigid_words`, `failures`.

**Observed result.** 2,142 original truncation cases, 3,504 equal-state
suffix-trace cuts, 4,755 profile-dominance cuts, and 789 equal-state cuts on
words rigid by the memo's definition. Every asserted output was a witness;
the run ended with `failures=0`.

**Claims informed.** [C008](../research/claims.md#c008),
[C009](../research/claims.md#c009).

<a id="e004"></a>

### E004 — Two-state rigid family and shortest collapse

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [border_lab.py](border_lab.py) defines the family.
[run_experiments.py](run_experiments.py) checks
`n in (1,2,3,10,100,500)` and searches for the shortest strong witness at
`(L,D)=(0,0)`.

**Scope and limits.** The algebraic family is defined for every `n >= 1`; the
JSON records six sample lengths. The shortest search uses the default
`max_states=200000`. The sample is evidence for the explicit construction,
not a search over all two-state DFAs.

**Result keys.** `rigid_family`, `rigid_family_shortest`.

**Observed result.** Every sampled `0^n` row is rigid with `lrs=n-1`; the
strong search returns `YES` with word `0`.

**Claims informed.** [C006](../research/claims.md#c006),
[C007](../research/claims.md#c007), [C008](../research/claims.md#c008).

<a id="e005"></a>

### E005 — Singleton accepted-word budget family

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [border_lab.py](border_lab.py) constructs the
`(n+1)`-state instance. [run_experiments.py](run_experiments.py)
uses `n in (1,2,3,5,8,12)` and exhausts every budget `0..n-1` and every split
`L+D=budget`. Each search uses the default `max_states=200000`.

**Scope and limits.** The exact `n-1` formula is proved for this explicit
family in the review. The executable run checks selected values and all lower
budgets for those values. It does not establish a general upper bound.

**Result keys.** `singleton_budget_family`, including each row's `n`,
`states`, `exact_instance_budget`, `emptiness_tests`, and `max_search_states`.

**Observed result.** The recorded exact budgets are `0,1,2,4,7,11` for the
listed values of `n`; all lower-budget searches satisfy their assertions.

**Claims informed.** [C011](../research/claims.md#c011).

<a id="e006"></a>

### E006 — Encoded checks of memo Examples 8.13(i) and (ii)

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [run_experiments.py](run_experiments.py) uses the two
instances returned by `memo_examples()` and searches at `(L,D)=(0,1)` and
`(1,0)`. The encoded instances are in
[border_lab.py](border_lab.py).

**Scope and limits.** This checks only the two hard-coded examples and their
named budgets. It does not verify that the encoding matches an unavailable
original script or reproduce any broader memo census.

**Result keys.** `memo_no_examples`, with each row's `example`, `L`, `D`,
`status`, and `states`.

**Observed result.** Both rows return `status=NO`, with 7 and 12 explored
states respectively, under complete graph exhaustion.

**Claims informed.** [C010](../research/claims.md#c010).

<a id="e007"></a>

### E007 — Theorem 3.2 closed-form language check

**Command.**

```text
python3 experiments/run_experiments.py
```

**Code.** [run_experiments.py](run_experiments.py) compares the
push-only propagation predicate with the periodic characterization and records
the two-`1` examples.

**Scope and limits.** Every binary word of length at most 11 is checked,
including the empty word, for 4,095 total words. This confirms the finite
characterization and disagreement count only within that length limit.

**Result keys.** `theorem_3_2.words_checked`,
`theorem_3_2.formula_disagreements`, `theorem_3_2.two_ones_language`,
`failures`.

**Observed result.** `words_checked=4095`,
`formula_disagreements=4017`, and the recorded language begins
`11`, `0101`, `001001`, `00010001`, `0000100001`.

**Claims informed.** [C005](../research/claims.md#c005).

<a id="e008"></a>

### E008 — Lean proofs, axiom audit, and Python agreement

**Command.** With the pinned Lean 4.33.1 toolchain installed:

```sh
python3 scripts/check_lean.py
```

**Code.** [Check script](../scripts/check_lean.py) and the
[Lean core](../lean/README.md). The script builds the project, runs the bundled
`leanchecker`, inspects the named dependency closures, and generates native
evaluation comparisons in ignored `tmp/`.

**Scope and limits.** Seed `20260904`; 80 generated partial binary DFAs with
1–5 states and all words of length 0–6. Both Python witness formulations must
agree before each comparison with Lean. All 511 binary words of length 0–8
also compare `lrs`. The named theorem proofs apply beyond these finite cases,
under exactly their compiled hypotheses; their alphabet is binary.

**Result.** [lean-checks.json](../results/lean-checks.json) records the toolchain,
kernel replay, axiom lists, 10,160 witness comparisons, 511 `lrs` comparisons,
and zero failures. It now also checks 10,160 boundary cases, 60,960 necessary
and 60,960 sufficient cases at six budget pairs, and 33 one/two-state
decisions. Runtime definitions do not depend on classical choice. Some list
and truncation proofs use standard classical axioms in erased proofs.

**Claims informed.** [C008](../research/claims.md#c008),
[C009](../research/claims.md#c009), [C013](../research/claims.md#c013),
[C014](../research/claims.md#c014), [C016](../research/claims.md#c016),
[C018](../research/claims.md#c018). No concrete global bound or fixed-budget
automaton is supplied by the conditional theorem.

<a id="e009"></a>

### E009 — Normalized constraints to regular countermodel checks

**Command.**

```sh
python3 experiments/check_topfree_bridge.py
```

**Code.** [Bridge checker](check_topfree_bridge.py) and
[topfree_bridge.py](topfree_bridge.py).

**Scope and limits.** The deterministic fixtures cover the four normalized
constraint forms. There are 3,577 NFA-membership comparisons on words of
length at most 8 against a direct closure capped at intermediate stack height
16. That finite oracle is diagnostic only; the implemented saturation and
regular-language checks themselves have no depth cutoff.

**Result.** [topfree-bridge.json](../results/topfree-bridge.json) records PASS
for those comparisons, the C0 infinite countermodel, forced-root denial,
quotient and epsilon constraints, mixed hashable state IDs, empty-stack pop,
and push/pop cases. The supplied-path status contract is
`YES / UNSAT / REJECTED_PATH`. A rejected path is not an entailment verdict.

**Claims informed.** [C015](../research/claims.md#c015). The implementation has
an independent audit, not a Lean correctness proof or complete search over
all separating paths.

<a id="e010"></a>

### E010 — Context-restricted truncation and strict examples

**Command.**

```sh
python3 experiments/check_context_cuts.py
```

**Code.** [Context-cut checks](check_context_cuts.py) implement a direct
forward witness predicate and compare it with `border_lab.border_witness`.

**Scope and limits.** Exhaust all 81 two-state binary transition tables,
all 4 `Bad` sets, all 4 `Fin` sets, and all 16 flag relations, with initial
state 0. Check all 127 words of length 0–6 for each of the 20,736 instances.
The script also checks 120 seeded random instances with 2–5 states and every
word of length 0–8, using seed `20260904`.

**Result.** [context-cuts.json](../results/context-cuts.json) records
2,633,472 independent/reference comparisons and zero failures. It records
217,635 visited-state, 217,730 earlier-position, and 217,809 exact-occurrence
implication checks across both parts. These counts overlap; they are not
counts of distinct witnesses. The strict examples include `0010 -> 00` and
`1011 -> 101`, plus an empty-prefix case.

**Claims informed.** [C013](../research/claims.md#c013). The all-length claim
comes from the written proof and, for the binary visited-state version, the
Lean theorem. Enumeration establishes only the recorded finite cases and
minimal example lengths within its explicit search.

<a id="e011"></a>

### E011 — Bounded adversarial budget search

**Command.**

```sh
python3 experiments/search_budgets.py --instances 1200 --max-budget 8 --max-word-length 12 --state-cap 50000
python3 experiments/search_budgets.py --replay-stored
```

**Code.** [Budget search](search_budgets.py), seed `2026090409`.

**Scope and limits.** 1,200 generated abstract binary instances with 2–8
states. Search strong budgets `L+D<=8`, with a cap of 50,000 explored states
per split. An independent direct scan checks words of length at most 12.
The six singleton calibrations separately allow their known budgets through
11 and word lengths through 12. The input descriptions and generator limits
are recorded in the output.

**Result.** [budget-search.json](../results/budget-search.json) records 741
exact random flagged budgets, 414 `NO_THROUGH` rows, and 45 `UNKNOWN` rows.
The largest exact random budget is 1. Five rows have exact budget 1 versus
0 with all flags removed. No certified random example has `B>|K|`.
Calibration reproduces `B=n-1` through `n=12`.

The second command independently replays the five retained exact/growth
examples and adds a separate diagnostic. Three `+1` increases remain after
diagonal flags are encoded as Bad states and start-to-final flags as final
state exclusions. The other two increases are explained by those exclusions.
CI reruns this small replay; it does not rerun the full random census.
E012 later completes the boundary normalization: all five increases disappear
when flags from every visited state into each fixed final state are included.

**Interpretation.** `EXACT` requires exhaustive NO results for every lower
split and a checked sufficient witness at the reported split. `NO_THROUGH`
means only that all budgets in the specified range were exhausted.
`UNKNOWN` means a split hit the state cap. Neither latter status establishes
that no witness exists. See the [attempt note](../notes/2026-09-04-budget-search.md)
for retained examples and the next generator design.

**Claims informed.** [C010](../research/claims.md#c010),
[C011](../research/claims.md#c011), and the investigation in A009. This run
does not establish a stronger growth family or a general bound. These are
abstract instances; no SEP realizability claim is made.

<a id="e012"></a>

### E012 — Boundary slices and exact restricted decisions

**Command.**

```sh
python3 experiments/check_boundary_slices.py
```

**Code.** [Boundary slices](boundary_slices.py) and
[checker](check_boundary_slices.py).

**Scope.** All 20,736 binary two-state instances, all words through length
four; 100 seeded instances with words through length seven, seed `20260905`.
The combined 668,316 comparisons test boundary slices against `N''(0,0)`
and verify exact witness-language equality where the regularity certificate
applies. The script also replays all five earlier growth rows against their
complete boundary slices.

**Result.** [boundary-slices.json](../results/boundary-slices.json) records
2,682 nonempty and 18,054 empty two-state instances. All nonempty instances
have a witness of length at most one and budget zero. Across both input sets,
the regularity certificate returns 2,627 YES, 18,105 NO, and 104 UNKNOWN.
No earlier E011 increase survives full boundary normalization.

**Claims informed.** [C016](../research/claims.md#c016). The general restricted
decision follows from the written graph proof; the binary two-state decision
also has a Lean proof in E008. The general problem remains open.

<a id="e013"></a>

### E013 — Actual subtype summaries and independent pushdown audit

**Commands.**

```sh
python3 experiments/check_summary_bridge.py
python3 experiments/check_summary_bridge_audit.py
```

**Code.** [Summary bridge](summary_bridge.py),
[targeted checks](check_summary_bridge.py), and
[independent audit](check_summary_bridge_audit.py).

**Scope.** The targeted run compares 762 words over six satisfiable systems,
through length six. The independent run uses seeds `20260904` for 300 Pop
trials and 400 denial-monitor trials, and `222` for 400 summary trials.
Its direct stack/depth/state caps are recorded in the output; capped absence
is UNKNOWN. The summary/canonical comparison itself uses exact finite
automata for each supplied word, through length six.

**Result.** [summary-bridge.json](../results/summary-bridge.json) and
[summary-bridge-audit.json](../results/summary-bridge-audit.json) record the
targeted regressions and 28,956 summary/canonical comparisons over 228
satisfiable systems. Independent direct checks cover 68,839 known Pop cases
and 10,675 known denial cases; another 29,214 and 1,725 respectively remain
UNKNOWN under their caps. No known comparison disagrees.

The audit found and fixed generator consumption and a missing satisfiability
guard. Regressions include both, absent query variables, empty-stack pops,
and denial reachability with residual stacks.

**Claims informed.** [C017](../research/claims.md#c017). This is a reduction
component and bounded implementation evidence, not a complete entailment
solver or a formal proof of all-input saturation.

<a id="e014"></a>

### E014 — Shortest witnesses and flags that preserve a target word

**Commands.**

```sh
python3 experiments/shortest_witnesses.py
python3 experiments/check_minimal_structure.py
```

**Code.** [Shortest-witness search](shortest_witnesses.py) and
[independent three-state example](check_minimal_structure.py).

**Scope.** The first command covers all 20,736 two-state instances, using
the exact zero-budget necessary graph to certify emptiness after testing
words of length at most one. It also makes 120 targeted attempts with 3–8
states, seed `8008`, at most 16 flag additions per attempt, and words through
length 12. It retains the six best rows by its stated score, then certifies
their shortest words and exact instance budgets with a 200,000-state cap.
Unresolved fixed-budget searches remain UNKNOWN.

**Result.** [shortest-witnesses.json](../results/shortest-witnesses.json)
records the two-state census and six retained targeted rows. Their exact
budgets are `5,4,3,2,2,2`; the largest shortest length is 12. Raw state
counts are 7 or 8. Removing irrelevant states from the first row produces
the stronger six-state result in E015. The second command verifies that
`001` is shortest in a three-state example and deleting its final-state
loop creates the forbidden word `00`.

**Claims informed.** [C016](../research/claims.md#c016),
[C019](../research/claims.md#c019), and [C020](../research/claims.md#c020).
The targeted generator is selective. It is not a census of larger instances
and proves no general bound. Per-word budget and exact instance budget are
recorded separately.

<a id="e015"></a>

### E015 — Six-state counterexample to the regular-subclass bound

**Command.**

```sh
python3 experiments/trim_budget_example.py
```

**Code.** [Restriction and replay](trim_budget_example.py) retains only the
six states visited by E014 attempt 3's sufficient witness.

**Result.** [trimmed-budget.json](../results/trimmed-budget.json) records exact
`B=5`, shortest word `001011010101`, length 12, and full-boundary `B=1`.
All 15 splits below budget five are exhausted, as are five splits at budget
five before `(5,0)` succeeds. Each search allows 200,000 states; none hits
the cap. All 8,191 binary words through length 12 are also checked against
both direct witness predicates.

**Claims informed.** [C020](../research/claims.md#c020), with the
[restriction proof and exact limits](../notes/2026-09-04-trimmed-budget.md).
This refutes the universal extension of `B<=max(0,|K|-2)`. It establishes no
asymptotic lower bound, subtype realization, or general impossibility result.

## Continuation and terminal checks

These entries extend E001-E015. They keep the continuation's written proofs,
bounded replays, and missing artifacts distinct. The detailed research records
remain the source for the mathematical arguments; this index is the command
and evidence map for agents.

<a id="e016"></a>

### E016 — Exact budget-growth family

| Field | Record |
|---|---|
| Command | `python3 experiments/check_budget_growth_family.py` |
| Detail | [Budget-growth proof and limits](../notes/2026-09-04-budget-growth-family.md); [continuation record](../research/CONTINUATION.md) |
| Evidence | [Imported checkpoint](../results/continuation-import.json), keys `E016`: 28 parameter pairs, every lower sufficient split exhausted, 70,680 direct shortest-word comparisons, cap 200,000, zero unknown results. |
| Artifact status | The executable is present. The per-run `results/budget-growth-family.json` is absent in this checkout; the linked checkpoint is the saved evidence. |

The all-parameter `B=2k-4` result is supported by the written proof, not by
extrapolating the finite replay. The instances are abstract BorderAvoid
instances; no subtype realization is claimed.

<a id="e017"></a>

### E017 — Exact three-state decision

| Field | Record |
|---|---|
| Command | `python3 experiments/three_state_decision.py` |
| Detail | [Three-state proof and limits](../notes/2026-09-04-three-state.md); [continuation record](../research/CONTINUATION.md) |
| Evidence | [Imported checkpoint](../results/continuation-import.json), keys `E017`: all 65,536 normalized binary instances, 36,640 YES and 28,896 NO, maximum negative graph size 65, maximum constructed length 6. |
| Artifact status | The executable is present. The per-run `results/three-state-exhaustive.json` is absent in this checkout; the linked checkpoint is the saved evidence. |

The exact theorem is limited to at most three abstract states. Larger inputs
are not decided by a six-letter cutoff.

<a id="e018"></a>

### E018 — Summary absorption and denial-free decision

| Field | Record |
|---|---|
| Command | `python3 experiments/check_summary_absorption.py` |
| Detail | [Summary absorption proof and limits](../notes/2026-09-04-summary-absorption.md); [continuation record](../research/CONTINUATION.md) |
| Evidence | [Imported checkpoint](../results/continuation-import.json), keys `E018`: seed `2026090421`, 400 systems, 281 YES and 119 NO, maximum eight summary classes, zero invariant violations. |
| Artifact status | The executable is present. The per-run `results/summary-absorption.json` is absent in this checkout; the linked checkpoint is the saved evidence. |

This is an independent denial-free normalized implementation. It is not a
rerun of the complete subtype bridge, and no unrestricted decision follows.

<a id="e019"></a>

### E019 — Denial-aware safe continuations

| Field | Record |
|---|---|
| Command | `python3 experiments/check_unrestricted_continuation.py` |
| Detail | [Denial-aware continuation proof](../notes/2026-09-04-denials-and-continuations.md); [continuation record](../research/CONTINUATION.md) |
| Evidence | [Saved result](../results/unrestricted-continuation.json): 500 generated systems, 24,129 full/reduced/canonical comparisons, 45,615 periodic predictions, and the actual terminal obstruction. |
| Status | Reproducible standard-library check; written proof, not Lean-checked. |

`NO_EXTENSION` and `NO_INFINITE_EXTENSION` are local results. They do not
classify terminal witnesses or solve unrestricted Problem 1.7.

<a id="e020"></a>

### E020 — Infinite-safe-continuation monitor

| Field | Record |
|---|---|
| Command | `python3 experiments/check_infinite_extensions.py` |
| Detail | [Infinite-extension proof and limits](../notes/2026-09-04-denials-and-continuations.md); [continuation record](../research/CONTINUATION.md) |
| Evidence | [Saved result](../results/infinite-extensions.json): 1,500 abstract instances, 400 additional subtype systems, 305,010 monitor comparisons, and 502 exact small-state checks. |
| Status | Reproducible standard-library check; written proof, not Lean-checked. |

The theorem covers witnesses with an infinite safe continuation. A negative
monitor result does not exclude a witness with only a finite continuation.

<a id="e021"></a>

### E021 — Terminal automaton realization

| Field | Record |
|---|---|
| Command | `python3 experiments/check_terminal_realization.py` |
| Detail | [Terminal continuation](../research/TERMINAL.md); [realization proof](../notes/2026-09-05-terminal-realization.md) |
| Evidence | [Saved result](../results/terminal-realization.json): 166 instances, 10,458 word comparisons, 83,664 budget-predicate comparisons, 2,416 summary identities, and 2,985 exact canonical-model checks. |
| Status | Reproducible check for the written terminal realization; not Lean-checked. |

The construction covers binary terminal-final abstract automata with arbitrary
flags and Bad states. It preserves words and budgets through `2*k+1`
variables under the recorded construction.

<a id="e022"></a>

### E022 — Nonregular terminal separating language

| Field | Record |
|---|---|
| Command | `python3 experiments/check_terminal_nonregular.py` |
| Detail | [Terminal continuation](../research/TERMINAL.md); [realization and nonregularity proof](../notes/2026-09-05-terminal-realization.md) |
| Evidence | [Saved result](../results/terminal-nonregular.json): 2,047 words through length 10, 266 exact canonical models, 441 exponent pairs, and 465 distinguishability pairs. |
| Status | Reproducible bounded check plus written all-length nonregularity proof; not Lean-checked. |

The result rules out a finite automaton for the displayed witness language. It
does not rule out a finite decision procedure for whether a witness exists.

<a id="e023"></a>

### E023 — Presburger arithmetic for flat terminal skeletons

| Field | Record |
|---|---|
| Command | `python3 experiments/check_terminal_arithmetic.py` |
| Detail | [Terminal continuation](../research/TERMINAL.md); [arithmetic proof and limits](../notes/2026-09-05-terminal-arithmetic.md) |
| Evidence | [Saved result](../results/terminal-arithmetic.json): 164 fixed-exponent formula cases, 8,188 flat-language comparisons, and guarded unbounded solver fixtures using Z3 4.13.3.0. |
| Environment | The optional Z3 shared library is required for the recorded arithmetic run. Missing backends or resource caps must remain `UNKNOWN`. |

The proof supplies a complete cover only for flat terminal candidate graphs.
The executable check has no Lean or solver proof certificate.

<a id="e024"></a>

### E024 — Complete four-state terminal census

| Field | Record |
|---|---|
| Command | `python3 experiments/check_four_state_terminal.py` |
| Detail | [Terminal continuation](../research/TERMINAL.md); [four-state census proof and limits](../notes/2026-09-05-four-state-terminal.md) |
| Evidence | [Saved result](../results/four-state-terminal.json): all 65,536 normalized cases, 45,430 YES, 20,106 NO, zero unresolved cases, and maximum witness length four. |
| Status | Complete finite census under the audited Python graph certificates; not Lean-checked. |

This exact result is limited to normalized binary terminal-final instances with
at most four states. It does not establish the terminal budget candidate in
general.

<a id="e025"></a>

### E025 — Nonflat overlap certificate

| Field | Record |
|---|---|
| Command | `python3 experiments/check_nonflat_overlap.py` |
| Detail | [Nonflat continuation](../research/NONFLAT.md); [proof and failed flat-cover route](../notes/2026-09-05-nonflat-overlap.md) |
| Evidence | [Saved result](../results/nonflat-overlap.json): 65,536 four-state cases (45,158 YES, 20,090 NO, 288 UNKNOWN), 600 seeded instances, 62,220 predicate comparisons, 8,191 obstruction words, 521 canonical models, and all 128 edge restrictions. |
| Status | Reproducible standard-library check for the acyclic last-flag certificate; cyclic residuals remain `UNKNOWN`. |

The new certificate cross-checks cases already decided by E024. It does not
provide a general terminal bound. The optional arithmetic backend is imported
by helper code but is not invoked by this experiment.

<a id="e026"></a>

### E026 — Bounded exponent of terminal suffix violations

| Field | Record |
|---|---|
| Command | `python3 experiments/check_terminal_period_bound.py` |
| Detail | [Period-bound proof and limits](../notes/2026-09-05-terminal-period-bound.md) |
| Evidence | [Saved result](../results/terminal-period-bound.json): 2,000 random terminal automata, 11,631 accepted words, 11,918 flagged agreements, maximum observed full-period count 6, and the sharp unary family for `k=2..8`. |
| Status | Finite supporting evidence for a written all-input lemma; not Lean-checked. |

The lemma bounds the number of aligned copies for a fixed gap. It does not
bound the gap, witness length, or successful budget.

<a id="e027"></a>

### E027 — Forward-closed source-border certificate

| Field | Record |
|---|---|
| Command | `PYTHONPATH=experiments python3 experiments/check_terminal_anderson.py` |
| Detail | [Source-border continuation](../research/ANDERSON.md); [proof and limitations](../notes/2026-09-05-source-border-anderson.md) |
| Evidence | [Saved result](../results/terminal-anderson.json): all 288 E025 cyclic leftovers, 16 certified negative and 272 positive cases left `UNKNOWN`; 700 seeded soundness instances and 315,840 direct short-word checks with zero false impossibility certificates. |
| Status | Reproducible soundness/pruning check for the forward-closed source class; not Lean-checked. |

The `6n+1` adaptation is a conditional certificate. A cyclic residual or a
non-forward-closed target set remains unresolved.

<a id="e028"></a>

### E028 — Terminal budget-candidate falsification search

| Field | Record |
|---|---|
| Command | No committed executable command is recorded. |
| Detail | [Terminal budget geometry](../notes/2026-09-05-terminal-budget-geometry.md) |
| Evidence | The note records deterministic standard-library runs for `k=5` (20,000 instances), `k=6` (15,000), and `k=7` (4,000), with no searched-range counterexample. |
| Artifact status | The executable and result JSON are absent in this checkout. Do not treat the note-only counts as current `REPRO` output, and do not read an empty searched budget range as a `NO` classification. |

E028 is useful falsification evidence, but it is not currently reproducible
from a committed command. Add an executable and compact result artifact before
reusing it as a fresh run.

## Additional checks without E IDs

These existing scripts are indexed for discovery without assigning new
experiment IDs. Their status follows the saved artifact and the detailed
record; no new `REPRO` claim is inferred from the command alone.

### C045 — Unbordered-gap normalization

| Field | Record |
|---|---|
| Command | `python3 experiments/check_unbordered_gap.py` |
| Detail | [Unbordered-gap proof and limits](../notes/2026-09-05-unbordered-gap-normalization.md) |
| Evidence | [Saved result](../results/unbordered-gap.json): seed `202609051817`, 20,000 random tables per `k=3..7`, 160 pure unbordered strings, and the earliest-copy failure regression. |
| Status | Existing bounded C045 check; no E ID is assigned here. |

The saved result supports the implementation only. C045 rests on its written
proof and its stated terminal-uniqueness hypothesis.

### Q003 — Strict agreement-profile descent

| Field | Record |
|---|---|
| Command | `python3 experiments/check_profile_descent.py` |
| Detail | [Q003 record](../research/conjectures/Q003.md); [profile-descent derivation](../notes/2026-09-05-unbordered-gap-normalization.md) |
| Evidence | The script is present and would write `results/profile-descent.json`, but that result file is absent in this checkout. The Q003 note reports prior bounded evidence; this index does not assign an E ID or current `REPRO` status. |
| Status | Open conjecture with bounded falsification evidence only; no all-length result. |

Do not infer a current run from the script's presence or from the note-only
counts. Preserve Q003 as an open hypothesis.

### Shift form, single-source period form, and flag census

| Field | Record |
|---|---|
| Command | `python3 experiments/check_period_state_form.py` |
| Detail | [Strategy review and period form](../notes/2026-09-08-strategy-review-and-period-state-form.md) |
| Evidence | [Saved result](../results/period-state-form.json): seed `2026090801`; 76,500 word comparisons between a Z-array implementation of Proposition 8.2 and the recorded predicates; 102,000 single-source period-form comparisons; 18 exponent regressions; the complete four-state census with one flag (13,800 instances) and two flags (34,500 instances) at cap 12; 900 random five/six-state samples at cap 14. |
| Status | Regression and bounded census only; caps are UNKNOWN; no E ID is assigned and no claim changes status. |

The census maxima are lower bounds from finite searches. C034 already decides
every four-state case; this check does not add a small-state result.

### Single-source census

| Field | Record |
|---|---|
| Command | `python3 experiments/single_source_census.py 4` and `python3 experiments/single_source_census.py 5` |
| Detail | [Shape-lemma note, Section 7](../notes/2026-09-08-single-source-shape-lemmas.md) |
| Evidence | [Saved result](../results/single-source-census.json): every valid single-source table up to relabelling (414 for four states, 10,109 for five) with every nonempty target set; 1,242 and 70,763 instances; breadth-first shortest witnesses up to length 20; NO certified only by an exhausted Necessary automaton with `L, D <= 3`; zero UNKNOWN. Longest shortest witness: 4 (four states), 6 (five states). |
| Status | Exact finite census for the single-source subclass; no E ID assigned; no all-state bound follows. |

### Lean rank-query statement differential

| Field | Record |
|---|---|
| Command | `python3 experiments/check_lean_rank_query.py --lean --output /tmp/lean-rank-query.json && cmp results/lean-rank-query.json /tmp/lean-rank-query.json` (Lean 4.33.1 required; without `--lean` only the Python fixtures are built) |
| Detail | [Statement readback](../notes/2026-09-18-lean-rank-query-statement.md); [module](../lean/Subtail/RankQuery.lean) |
| Evidence | [Saved result](../results/lean-rank-query.json): seed `2026091801`; 16 literal prefix graphs, 16 finishing queries and 64 query unions (88 clauses) evaluated natively in Lean agree with `literal_graph`, `rank_preimage_core.model`, `explicit_query_truth` and `finish_queries`. |
| Status | Translation/semantics regression for the pinned stage-4a definitions; no E ID; the Closure Lemma itself is untouched. |

### Adversarial Closure Lemma fixtures

| Field | Record |
|---|---|
| Command | `python3 experiments/check_closure_fixtures.py --quick --output /tmp/closure-fixtures.json && cmp results/closure-fixtures.json /tmp/closure-fixtures.json` (about 137 s; `--full` removes the work caps and is not byte-comparable) |
| Detail | [Fixture note](../notes/2026-09-18-closure-fixtures.md); [referee brief, points 1-2](../notes/2026-09-18-closure-lemma-referee-brief.md) |
| Evidence | [Saved result](../results/closure-fixtures.json): seed `2026091832`, work cap 1,500,000; an independent evaluator, literal safety predicate and first-return extension enumerator judge the imported compiler: 149 brute-force extensions, 54 of 54 forward certificates, 59 sound reconstructions, one exhausted two-atom union (5,256 clauses), 16 work-capped unions, 297,083 compiled clauses within `U_k(T)`, 12 separately-satisfiable/jointly-unsatisfiable pairs with no satisfiable enumerated joint clause, oracle YES/NO 10/24 consistent with brute force; no discrepancy. |
| Status | Bounded adversarial regression against `rank_preimage.py`; caps are UNKNOWN, never NO; no E ID; C080 remains a candidate. |

### Stage-6 semantic bridge: transfer contracts and finite propagation differential

| Field | Record |
|---|---|
| Command | `python3 experiments/check_semantic_bridge_audit.py --output /tmp/semantic-bridge-audit.json && cmp results/semantic-bridge-audit.json /tmp/semantic-bridge-audit.json`; `python3 experiments/check_stack_summary.py --lean --output /tmp/finite-propagation.json && cmp results/finite-propagation.json /tmp/finite-propagation.json` (Lean 4.33.1) |
| Detail | [Bridge audit contracts](../notes/2026-09-18-semantic-bridge-audit.md); [canonical model](../notes/2026-09-18-canonical-model-formalization.md); [finite propagation](../notes/2026-09-18-finite-propagation-formalization.md) |
| Evidence | [semantic-bridge-audit.json](../results/semantic-bridge-audit.json): restricted-input integration oracles and guards for the C029/C031 composition. [finite-propagation.json](../results/finite-propagation.json): seed `2026091831`; 68 systems, 14,256 reachability, 1,488 control-reachability and 176 balanced comparisons against an independent saturation oracle, 8,050 complete monotone cross-checks, 32 `satCheck` and 896 supplied-address `separationCheck` comparisons of the compiled Lean Booleans. |
| Status | Regressions for kernel-checked executable definitions; entailment itself is not decided (the separating address remains an explicit existential); no E ID; C080 unchanged. |

### Lean diagram compiler differential (stage 4c)

| Field | Record |
|---|---|
| Command | `python3 experiments/check_lean_rank_compiler.py --lean --output /tmp/lean-rank-compiler.json && cmp results/lean-rank-compiler.json /tmp/lean-rank-compiler.json` (Lean 4.33.1 required) |
| Detail | [Compiler module](../lean/Subtail/RankQueryCompiler.lean); issue #29 |
| Evidence | [Saved result](../results/lean-rank-compiler.json): seed `2026091841`; 37 certificate diagrams extracted from brute-force first-return extensions on the toy and two random terminal instances, plus 100 mutated variants; 733 comparisons of `compileDiagram` (validity and `satCheck` on several bases) against `rank_preimage.compile_diagram`/`model`, no mismatch (326 rejections, 218 satisfiable, 189 unsatisfiable agree). |
| Status | Translation regression for the executable Lean compiler; the reverse Closure direction is NOT proved by this check; no E ID; C080 unchanged. |

## Not yet reproducible or not yet run

These items have no executed experiment ID. Do not assign them `REPRO` status
until a committed command and compact output exist.

- **Original memo census.** The `analysis-2026` directory and its scripts are
  still unavailable. There is no honest command or JSON key for reproducing
  its reported census.
- **Original exhaustive audit replay.** E010 now supplies a reproducible
  exhaustive two-state check at the same word-length limit. It uses the new
  context criteria and two witness predicates; it does not recreate every
  historical assertion in the earlier border-audit note.
- **Universal terminal bound.** E016 supplies an abstract `2k-4` family;
  E024 is complete only through four states, and E028 has no committed
  reproducer. No general terminal budget bound or Q002/Q003 proof is
  established.
- **General subtype decision.** E018-E020 cover restricted summary branches,
  while E021 shows the terminal branch can realize arbitrary abstract flags.
  No executable experiment establishes a complete decision procedure for all
  normalized subtype inputs.

## Adding an experiment

Use the next available ID. Record the exact command, code location, commit or
input generator, seed, word/state/resource limits, output JSON paths, and the
claim IDs that the run can support. Keep `UNKNOWN` separate from `NO`, and add
a new result key rather than silently changing the meaning of an existing key.

## Recovered flag-inference experiments

<!-- saved-research-recovery-2026-09-09 -->
The two September 8 scoped attempts allocate no new global IDs. [Recovery and integrity manifest](../research/SAVED_RESEARCH_RECOVERY.md) links their exact seeds, finite coverage, written proofs, and limits.

Run `python3 scripts/check_recovered_research.py --replay` to rerun both new checkers, the unchanged core checker, and the previous last-flag checker. This verifies 17 source/proof files and the canonical hashes of both saved result objects. Stored results are compact JSON; canonical pretty-printing recovers the original blobs.

## Overlap-deletion audit

<!-- overlap-deletion-audit-2026-09-09 -->
Run `python3 experiments/check_overlap_deletion.py`. [Scope and all-length arguments](../notes/2026-09-09-overlap-deletion-audit.md) distinguish selected equality/acceptance preservation from witness preservation. [Result](../results/overlap-deletion-audit.json), seed 2026090901. This scoped audit allocates no new global claim/experiment IDs.

## Guarded-order chains and trailing-copy boundary

<!-- guarded-order-route-2026-09-09 -->
Run `python3 experiments/check_guarded_order_chains.py` and `python3 experiments/check_trailing_copy_barrier.py`. [Proof and complete scopes](../notes/2026-09-09-guarded-order-and-terminal-anchor.md) and [route outline](../research/ORDER_COVER_ROUTE.md) distinguish the complete restricted backend from both unproved end-to-end transfers. Results: [guarded order](../results/guarded-order-chains.json) and [trailing copy](../results/trailing-copy-barrier.json). No new global IDs are allocated.

## Source-capture continuation (2026-09-09)

<a id="e043"></a>

### E043 — Terminal source-capture reduction and adversarial boundaries

**Command.** `python3 experiments/check_source_capture.py`.
Optional: `python3 experiments/check_source_capture.py --with-smt`.

**Coverage.** Seed 2026090917. All 256 terminal three-state binary tables,
every Bad subset and initial state, words through length 6: 8,568 actual
capture/target comparisons. Another 1,800 recurrent paths on 300 generated
3--9-state automata add 10,848 comparisons, maximum word length 88. A separate
240-instance sample checks 122,640 words through length 8 against both existing
witness predicates, with seven strict one-source normalizations. Source
segments are reconstructed on 635 accepted words from 200 multi-source samples.
Fixed regressions show failure without terminality and failure of naive
source-by-source loop deletion, with a nonvacuous second flag.

**Evidence.** [Code](check_source_capture.py), [formula compiler](source_capture.py),
[deterministic result](../results/source-capture.json),
[proof and scope](../notes/2026-09-09-source-capture-word-equations.md), C067/C068.
The local native Z3 4.13.3.0 optional run returned 34 SAT and 17 UNSAT on 51
probes, no UNKNOWN; every SAT word passed both original witness predicates.
[Optional local result](../results/source-capture-smt.json) is not a byte-exact
CI oracle: backend versions and model choices can differ. UNSAT remains
backend-trusted, and timeout/unknown is not NO. Finite checks do not prove the
quantified theorem or completeness of the optional solver.


## Terminal decision and finishing checks (2026-09-19)

No new E ID; validation of A018/C080's exact terminal decision subclaim.

| Check | Reproduction and scope |
|---|---|
| All new dependency closures | `python3 scripts/check_rank_decision.py` audits 88 finishing, witness, semantic-unwind and decision declarations, including runtime definitions. |
| Whole decision for k≤2 | `python3 experiments/check_terminal_decision.py` exhausts all 12,820 binary terminal inputs with one or two states, including all partial transitions, Bad/flag/final sets and initial states. 341 YES and 12,479 NO agree with a literal predicate and native small-state check. Its finite oracle is complete by the existing TwoState theorem. |
| Fixed-reference finishing | `python3 experiments/check_finishing_trace.py --lean` compares 180 cases with an independent all-length set-of-matches oracle: 92 YES and original witnesses, 88 fixed-reference no-return NO results. |

[Decision results](../results/terminal-decision-regressions.json),
[preserved finishing results](../results/finishing-trace-semantics.json),
[proof and readback](../notes/2026-09-19-terminal-rank-decision.md).
The all-k decision rests on the Lean theorem, not these finite comparisons.
Native evaluation of the whole promoted query for k≥3 was NOT RUN.
The original memo archive remains unavailable and is not an assigned task.


## Exact subtype summary checks (2026-09-19)

Validation of A010/A018 and the semantic-bridge subclaim of C080; no new E ID.

- `python3 scripts/check_subtype_summary.py` audits all named public declarations
  in the new bridge modules, including runtime dependency closures. Executable
  definitions must not depend on Classical.choice.
- `python3 experiments/check_subtype_summary.py` compares actual native summary
  tables, Witness and separationCheck with independent P-automaton predecessor
  saturation and the literal original word predicate. Seed 2026091931; 42
  constraint systems, 1803 query-word pairs, 528 states and 10752 ordered flags.
  Word lengths are at most three, or two in the three-control proper-prefix
  fixture. No finite search failure is extrapolated to a general NO.

[Recorded native result](../results/subtype-summary-bridge.json),
[ordinary readback and remaining obligations](../notes/2026-09-19-subtype-summary-bridge.md).
The all-word correctness result is the Lean theorem; neither this corpus nor
the existence-preserving bridge alone decides Problem 1.7.


## Absorbing safe-cycle/terminal split checks (2026-09-19)

`python3 experiments/check_absorbing_terminal.py` enumerates every absorbing
binary one/two-state instance, including all initial states, partial
transitions, Bad/final sets and ordered flag sets. The independent Python
oracle uses the literal original word predicate and exact finite safe-cycle
reachability. Its length-at-most-one existence check is complete for this
scope by the existing TwoState theorem, applied also after restricting finals
to states that reach a safe cycle. It is not a search bound for larger inputs.

The native check compares the complete terminalize tables and the existing
exact original/terminal decision functions. Named adversarial fixtures retain
the need for strong absorption, pruning before sink selection, rejecting
nonfinal sinks and rejecting unsafe empty witnesses. Finite oracle validation
is separate from the all-k `AbsorbingTerminal.c031` theorem. This does not
implement or prove the general C029 infinite-witness decision.


Recorded [absorbing-terminal result](../results/absorbing-terminal.json):
15914 cases (26 with one state, 15888 with two), 1396 original YES,
515 terminal YES, 885 infinite-branch YES, zero failures. The two YES branches
may overlap. Both new checks run in the existing consolidated Lean workflow;
its trigger includes the new dependency-audit script, and the default Lean
import graph includes all four new modules.
