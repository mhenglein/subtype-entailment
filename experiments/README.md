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

The original experiment workflow covers the pre-continuation core. The
consolidated [Lean workflow](../.github/workflows/lean.yml) also runs the newer
kernel, dependency and native regression checks named in its steps, including
normalization and full entailment. This index is larger than CI; a registered
command is not automatically run by a workflow. Check the exact trigger and
step before claiming automatic coverage.

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
| Status | Original Python monitor evidence preserved; the later C029 total Lean decision and native checks are recorded below. |

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
| Status | Regressions for kernel-checked executable definitions; this earlier layer leaves the separating address existential; C081 later composes it into full entailment; no E ID; C080 unchanged. |

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


## C029 bounded-cycle and reverse periodic monitor (2026-09-19)

`python3 experiments/check_infinite_cycle_monitor.py` checks the new cycle-only
algorithm against a direct infinite-suffix predicate. It covers every supplied
prefix/period in its recorded finite corpus, including nonprimitive periods;
all 15914 absorbing one/two-state instances use an independent complete
small-state existence oracle. Larger random instances compare against the
preserved old C029 implementation. Nine guards test phase aliases, ordered
flags, reverse mismatch persistence, a necessary pre-final loop, terminal-only
branch exits, invalid absorption and UNKNOWN caps. Every returned word passes
two literal witness predicates. This is Python evidence; no native Lean C029
Boolean decision is claimed. [Saved results](../results/infinite-cycle-monitor.json).

`python3 scripts/check_infinite_witness.py` audits every named declaration in
PeriodicTail, InfiniteCycle and InfiniteWitness after the pinned build. Those
modules check cycle normalization, stream equality and finite extraction;
they do not prove the monitor's language invariant or finite search complete.
[Ordinary proof, exact checked boundary and next task](../notes/2026-09-19-c029-cycle-monitor.md).
Both checks run in the consolidated Lean workflow and the three modules are
included in the default Lean import graph.


## C029 complete native decision and monitor checks (2026-09-19, E020)

`python3 experiments/check_infinite_decision.py --output results/infinite-decision.json`
executes the actual `InfiniteDecision.infiniteWitnessCheck`, not a Python
reimplementation. [Saved evidence](../results/infinite-decision.json) records:

- All 15914 absorbing binary one/two-state encodings, with 885 YES, checked by
  literal Witness on empty/one-letter words (complete by TwoState) and an
  independent safe-cycle closure.
- All 512 three-vertex graphs, 1536 seeds and 4608 reachability comparisons for
  each of 3 fuel variants, against simple-path enumeration. A `2^256` fuel fixed-point
  check covers both accepting and rejecting outcomes without counting down.
- 29760 exact supplied-prefix/period checks against the direct infinite-suffix
  predicate, with 22788 accepts. Seed 2026091929 selects 32 varied 2-6-state tables;
  every prefix of length 0-4 and nonempty period of length 1-4 is tested,
  including nonprimitive periods. Absorption and cycle validity are not assumed
  for this separate monitor-language check.
- Seven larger existence guards with independently checked positive witnesses
  and explicit forced-tail or terminal-only negative arguments. This is not
  an exhaustive larger-state existence census or a performance claim.

`python3 scripts/check_infinite_witness.py` now audits all named declarations
in the three earlier C029 modules plus FiniteSearch, PeriodicRun,
PeriodicRotation, PeriodicGood, PeriodicMonitor, PeriodicMonitorComplete and
InfiniteDecision. Every module is in the default Lean import/kernel graph.
The consolidated Lean workflow runs the full audit and both old Python and
new native checks, comparing deterministic outputs with the saved records.
[Exact theorem, review and validation](../notes/2026-09-19-c029-completion.md).

The preceding dated component-only entry is historical. Its open monitor,
finite-search and concrete-trace obligations are discharged by this result;
its original evidence is unchanged. Terminal witnesses remain a separate
branch; the full expression-level entailment checker is not claimed here.

## Full-input normalization checks (2026-09-19, A010/A018/C081)

The two implementations and their evidence remain distinct:

```sh
(cd lean && lake env lean --run Subtail/ExpressionNormalizationAudit.lean) > /tmp/normalization-native.jsonl
python3 experiments/check_expression_normalization_lean.py --lean-output /tmp/normalization-native.jsonl
python3 experiments/check_expression_normalization.py --output /tmp/normalization-reference.json
python3 scripts/check_entailment_decision.py
```

The Lean normalizer's 372 actual outputs agree with an independent literal
syntax/finite-tree checker. Its semantic corpus covers 567340 extended finite
valuations, 7624 original valuations and 10479 exact query comparisons, plus
mutation guards. [Source](check_expression_normalization_lean.py),
[saved evidence](../results/expression-normalization-lean.json).

The distinct Python reference uses a different allocation order. Its saved
seeded/exhaustive corpus includes 1352 exhaustive and 250 seeded syntax inputs,
10600 original extensions, 115340 normalized valuations, 38936 address checks,
10000 nested-product stress, 14 malformed inputs, nine adversarial groups and
three CLI roundtrips. [Source](check_expression_normalization.py),
[saved evidence](../results/expression-normalization.json).
These are finite checks; the arbitrary-tree model-transfer theorem is the
separate Lean proof. Fresh combined-tree runs and saved-count comparisons
passed on wb-marcus; historical environment metadata is preserved.

The full-input dependency audit checks all 91 named declaration closures in
ExpressionNormalization, its native audit, and EntailmentDecision, including
39 non-theorems with no classical choice. The default import graph contains
the semantic normalizer and final decision; the native audit executable is
built and kernel-replayed separately. The consolidated Lean workflow runs
both normalization suites and this audit when its dependency paths change.
[Exact pins, proof and review](../notes/2026-09-19-entailment-decision.md).

<a id="e052"></a>

### E052 — Full-expression native entailment regressions

**Command.** `python3 experiments/check_entailment_decision.py`.

**Scope.** Execute the actual Lean full-input Boolean or its normalized/raw
entry points on a small independently justified corpus. Expected positive
answers come from exact logical arguments; negative answers have explicit
models. The checker does not treat the absence of a bounded finite model as
proof of universal entailment. Individual processes have a 20-second cap;
timeouts are UNKNOWN, not negative Boolean answers.

**Evidence.** [Checker](check_entailment_decision.py),
[saved result](../results/entailment-decision.json),
[complete theorem and validation boundary](../notes/2026-09-19-entailment-decision.md).
The saved record states actual path coverage and incomplete cases. A successful
fast guard is not reported as exercising the raw finite-enumeration backend.
The existing branch-specific native suites remain separate evidence.

**Executed result (Mac, Lean 4.33.1, checker e867092).** Of 38 attempted cases,
25 completed and agreed: 17 full-expression calls, five guarded normalized
calls and three direct raw-backend calls. Thirteen timed out at 20 seconds,
with zero disagreements or unexecuted cases. The full report is therefore
`UNKNOWN`, not a complete native PASS. All completed direct raw calls returned
false; none of the raw positive-answer probes completed within the cap. The
separate terminal and C029 suites still supply their own complete small-state
differentials.

The 17 full-expression smoke cases also replayed with `--phase smoke --strict`
and no timeout; CI runs this strict subset and checks saved answers and exact
source identities. The full diagnostic command remains available; no CI pass
is claimed for its timed-out cases. Every timed-out process group is killed
and reaped. No further native process remains after a completed run.

<a id="e053"></a>

### E053 — Literal extension boundary checks

**Command.** `python3 experiments/check_extension_boundaries.py --check results/extension-boundaries.json`.
To regenerate: `python3 experiments/check_extension_boundaries.py --output results/extension-boundaries.json`.

**Scope.** Compare literal finite bottom/top/product order with the finite-graph
order after replacing explicit top by the infinite full product tree. Check
the zero-spine countermodel, the constant-free ambient-domain countermodel
`x=x×x, x<=y` with failed query `y<=x`, and the depth-two contravariance obstruction.
The target graph checker uses finite pair reachability; an independent
product-address predicate checks it on the finite top-free corpus.

**Result.** PASS at checker commit `66eed7d`: 1,444 ordered pairs of 38 source
trees through depth two, including 45 failures of order reflection and no
preservation failure within the corpus. The full labelled graph checker also
agrees with the independent finite order on all 1,444 pairs. The top-free graph
order agrees with literal address inclusion on 676 additional pairs. The zero-spine
and both contravariant orientations pass. None of 677 finite trees through
depth four satisfies the zero-spine premise; the all-depth impossibility is
the separate induction in the note. Results include the exact checker hash.
The regular model `x=Omega, y=top` satisfies the constant-free premises and
fails the query. The separate all-word induction proves top-free validity;
that conclusion does not come from the finite census. Saved-JSON replay also
passes after correcting tuple/list normalization in the first replay implementation.

**Evidence and limits.** [Checker](check_extension_boundaries.py),
[result](../results/extension-boundaries.json),
[ordinary arguments and feasibility](../notes/2026-09-19-post-c081-extensions.md),
[independent readback](../notes/2026-09-19-post-c081-extension-readback.md).
The literal counterexamples refute specific encodings. The finite census does
not settle extension decidability, prove an all-size preservation theorem,
or establish the separate regular-countermodel argument.

<a id="e054"></a>

### E054 — Matched native diagnostic for the gated entailment decision

**Command.** `python3 experiments/check_entailment_lazy.py --compare-baseline --output tmp/entailment-lazy.json`.
Omit `--compare-baseline` for the gated implementation alone, as in CI.

**Scope.** Reuse all 38 E052 inputs and independent expectations. Execute the
original and equality-proved gated Lean decisions under the same per-fixture
limits: 20 seconds wall/CPU, 16 GiB Linux address space, one Lean thread and
32768 KiB stack. Compilation failures or wrong answers fail the check; capped
cases remain UNKNOWN. A successful diagnostic process does not mean every
fixture completed.

**Observed result.** At `89385df1b41825bed8983cac232b7778698db926` on wb-marcus,
the original completed 22/38 and the gated implementation completed 24/38.
All completed answers agreed. The two gains are direct raw-backend positive
probes: `raw-reflexive` (20-second UNKNOWN to 0.869 seconds) and
`raw-unsat-denial-lower` (20-second UNKNOWN to 0.669 seconds).
Both implementations complete the same 17 full-expression and five normalized
cases. Fourteen gated cases remain UNKNOWN, so the full diagnostic status is
UNKNOWN. No practical worst-case bound follows. The old E052 Mac 25/38 result
is preserved and is not a matched hardware comparison.

**Evidence.** [Driver](check_entailment_lazy.py),
[combined source, audit, diagnostic and CLI receipts](../results/entailment-lazy.json),
[proof/interface/limits](../notes/2026-09-20-c081-solver.md).
The optional-module build/kernel replay, 17 declaration dependency audits and
default core passed at the diagnostic revision. A later certificate-only
trust-label correction changed no Lean or benchmark source. The current
16-test Python suite and actual positive/negative CLI plus graph readbacks
passed separately at `20c1f23937f9d43bf47b0b3890afff75ed613be5`.


<a id="e055"></a>

### E055 — Proved finite saturation, cached solver and deeper-input limits

**Build and commands.** Use pinned Lean 4.33.1 and build the optional module:

```sh
(cd lean && lake build +Subtail.EntailmentFast)
python3 scripts/check_fast_summary.py
python3 experiments/check_fast_summary.py --components \
  --output tmp/fast-components.json --scratch tmp/fast-components
python3 experiments/check_fast_summary.py --benchmark --compare-baseline --generated \
  --output tmp/entailment-fast.json --scratch tmp/entailment-fast
```

Omit `--compare-baseline` for the candidate-only diagnostic. The harness's
`--components` includes both system-level and normalized SAT/separation checks.
Default process caps are 20 seconds wall/CPU, 16 GiB Linux address space, one
Lean thread and 32768 KiB stack; the initial module build is separate. Full
receipts record source hashes, exact revision, host, expected answers and
individual PASS/FAIL/UNKNOWN outcomes. A capped run supplies no Boolean answer.

**Scope.** Independent P-automaton predecessor saturation checks five aggregate
Boolean vectors across 62 zero/one/two-control systems. Each vector is compared
by length and two rolling digests; six normalized SAT/separation vectors use
an exact integer encoding. These are regression tests alongside the all-input
Lean proofs. All 38 E054 fixtures are rerun against the current gated baseline
and the new wrapper. The seven raw probes deliberately call the same old raw
backend in both variants. Nineteen generated cases cover transitive chains,
covariance, supplied-address depth and original-expression nested products.
The last family exercises candidate paths beyond the short-word prefix.

**Observed result.** At `9a866c196f30f2fe1f11d4201d6237642fbd3cb8` on wb-marcus:
33/38 candidate cases complete versus 24/38 baseline, with no wrong answers
or regressions. Frontend completion is 26/26 versus 17/26, taking 0.668–0.771
seconds per candidate including Lean startup. Normalized completion is 5/5
for both. Raw completion is unchanged at 2/7; five cases remain UNKNOWN.
Both component phases PASS. Generated completion is 16/19; supplied depth
twelve and full-expression depths six and eight remain UNKNOWN. Thus the
basic acceptance target passes while the full diagnostic status is UNKNOWN.

**Evidence and limits.** [Driver](check_fast_summary.py),
[combined receipts](../results/entailment-fast.json),
[ordinary proof, declarations, failed harness attempts and remaining costs](../notes/2026-09-20-fast-summary.md),
[source readback](../notes/2026-09-20-fast-summary-readback.md).
The identical Lean source passed default and optional build/kernel checks plus
97 declaration audits at `cf12580`. The interface keeps its separate Python
trust boundary and incomplete explanation search. No global backend speedup,
peak-memory measurement, per-phase cost profile or practical worst-case bound
is claimed. The E052/E054 receipts are preserved unchanged.

A later diagnostic-only signal-classification repair at `6163f27` preserves
UNKNOWN when a killed process emits no message. Its 17 boundary tests and
replay of 97 recorded native outcomes PASS; no measured answer or status
changes. This is not a new native run, and the original `9a866c1` receipt is
retained with its exact hashes.


<a id="e056"></a>

### E056 — Finite-tree growth classification and complete small finite models

```sh
python3 experiments/check_finite_trees.py --output tmp/finite-tree-experiment.json
python3 -m unittest discover -s scripts -p 'test_finite_trees.py'
python3 scripts/check_finite_tree_reduction.py --output tmp/finite-trees.json
```

The first command needs only Python. The final command uses pinned Lean 4.33.1
and builds/replays the optional semantic module, audits every declaration,
runs Python regressions, and exercises seven actual CLI cases. Use an isolated
Lake checkout. The CLI cases allow 40 seconds each; one deliberately tiny cap
must return UNKNOWN. Native successes do not erase the classifier's ordinary
Python trust boundary.

This paragraph describes the E056 checkpoint. E057 below closes the classifier
gap in Lean and changes the current CLI; the E056 receipt remains historical.

**Independent experiment.** Seed 5803, 300 systems with one to four controls:
Hot endpoints from consuming-cycle analysis agree with a separate exact
P-automaton predecessor-saturation oracle. The oracle checks accepted prefixes
of length n and possible continuations; it does not use another SCC algorithm.
148 systems have consuming cycles. Separately exhaust every set of at most
three normalized clauses on one/two controls: 1,809 inputs and 44,880 finite
valuations. The literal finite-tree evaluator finds 636 satisfiable inputs;
1,147 inputs have growth obstructions, and 26 are unsatisfiable without growth.
All results agree with the C085 finite-SAT reduction.

The finite-SAT enumeration uses height at most n, justified by C085's bound
for the least forced-root closure in the no-growth case. This is a complete
cutoff for the stated satisfiability census, **not** a new entailment witness
bound. These are finite regressions alongside the ordinary all-input proof;
they do not prove classifier correctness in Lean.

**Validation.** At `8f6fad6` on wb-marcus: module build/kernel, 31 declaration
audits (13 non-theorems free of Classical.choice), 13 finite-mode tests, 24
existing CLI tests and nine extraction tests PASS. Seven actual CLI checks
cover finite/arbitrary disagreement, cold unsatisfiability, finite negative
variable/ground inputs, infinite-certificate rejection and UNKNOWN on a cap.
Three actual C084 instance proofs verify arbitrary non-entailment. The initial
`0b772bb` contradiction fixture also triggered growth; it is retained in the
receipt with that coverage limitation, and the corrected cold case was rerun.

[Ordinary construction](../notes/2026-09-20-finite-tree-reduction.md),
[exact source/mathematical readback](../notes/2026-09-20-finite-tree-readback.md),
[combined receipt](../results/finite-trees.json). Existing E055 performance
numbers and earlier extension-boundary receipts are preserved unchanged.

<a id="e057"></a>

### E057 — Checked finite-tree classifier and original-expression decision

```sh
python3 scripts/check_finite_tree_decision.py --output tmp/finite-tree-decision.json
```

Use pinned Lean 4.33.1 in an isolated Lake checkout. The driver builds and
kernel-replays `PopAcyclic` and `FiniteTreeDecision`, audits all 13 named
declaration closures (including the private trace lemma), and forbids classical
choice in the three runtime definitions. Those closure audits also include
the imported runtime dependencies.

The actual Lean `growthCheck` is compared with the independent predecessor-
saturation oracle on 300 seeded systems and eight named boundary cases.
Seed: 5807; random systems have one to four controls. Named cases include zero
controls, epsilon-only cycles, both letter self-loops, a balanced excursion
without growth, and a consuming cycle whose return needs a balanced excursion.
The oracle uses no cycle classifier. These regressions supplement the all-input
theorem; they do not establish it.

Nine actual CLI cases cover forced infinite growth, unsatisfiability without
growth, finite negative variable/ground inputs, the same growth input under
arbitrary semantics, rejection of an infinite supplied graph, a cap returning
UNKNOWN, zero-variable reflexivity and query-only product names. Three negative
cases also receive C084 kernel-checked arbitrary non-entailment certificates.
Finiteness of certificate roots remains a Python check.

[Source-pinned receipt](../results/finite-tree-decision.json) and
[readback](../notes/2026-09-20-finite-tree-decision-readback.md) record host,
revision, source hashes, commands and independent review. This is a correctness
and interface test, not a new E055 performance measurement or finite-SAT theorem.

<a id="e058"></a>

### E058 — Profile and prove primitive-table solver reuse

```sh
python3 scripts/check_prepared_summary.py --cli --output tmp/prepared-audit-cli.json
python3 experiments/check_prepared_summary.py --components --benchmark --generated --compare-baseline --output tmp/entailment-prepared.json
python3 experiments/profile_entailment.py --output tmp/profile-baseline.json --scratch tmp/profile-baseline
python3 experiments/profile_entailment.py --primitive-tables --output tmp/profile-tables.json --scratch tmp/profile-tables
python3 experiments/profile_entailment.py --prepared --output tmp/profile-prepared.json --scratch tmp/profile-prepared
```

Run serially on the same host in an isolated Lean 4.33.1 checkout. The matched
harness preserves the original E054 38 fixtures, E055 19 generated inputs,
`#eval` launch and per-process 20-second wall/CPU, 16 GiB Linux address-space,
one-thread and 32768 KiB stack caps. It compares `EntailmentFast` with the new
proved `EntailmentPrepared` endpoints. Raw fixtures use the identical terminal
backend in both variants. A capped or interrupted process remains UNKNOWN.

The independent P-automaton oracle checks 62 prepared systems, including zero
controls, all one-state primitive patterns, both letters, reversals and sparse
or dense cases. The actual Lean output is compared using vector lengths and
two checksums for primitive bits, balanced relations, control paths, arbitrary
reachability and control reachability. This is finite regression evidence,
not a proof or a collision-free comparison of every individual bit.

The all-input Lean proof is whole System equality, prepared-record equality,
and equality of the original-expression decision. Build, kernel replay and all
24 declaration closures are checked; all 13 runtime declarations exclude
classical choice. Five actual JSON runs cover positive and zero-variable
inputs, the depth-six/eight negatives with their expected countermodels and
paths, and a cap that returns UNKNOWN with exit two.

The phase profiler deliberately uses `--run` so interrupted traces survive.
Its forced summaries add diagnostic overhead. The preparation-only ablation
keeps uncached query predicates and is distinct from the final implementation.
The initial `#eval` buffering failure, phase locations and partial improvement
are retained in the [combined receipt](../results/solver-profile.json).
[Ordinary proof and limits](../notes/2026-09-20-solver-profile.md);
[exact readback and matched results](../notes/2026-09-20-solver-profile-readback.md).
This does not change C080, the finite endpoint, complexity or explicit-top semantics.

<a id="e059"></a>

### E059 — Stream the exact raw cycle search

```sh
python3 scripts/check_infinite_lazy.py --cli --output tmp/infinite-lazy-audit.json
python3 experiments/check_infinite_lazy.py --components --full38 --compare-baseline --timeout 20 --output tmp/infinite-lazy-matched.json --scratch tmp/infinite-lazy-matched
python3 experiments/check_infinite_lazy.py --stress-raw --timeout 20 --output tmp/infinite-lazy-stress.json --scratch tmp/infinite-lazy-stress
python3 experiments/profile_raw_backend.py --variant baseline --output tmp/raw-baseline.json --scratch tmp/raw-baseline
python3 experiments/profile_raw_backend.py --variant stream --output tmp/raw-stream.json --scratch tmp/raw-stream
python3 experiments/profile_raw_backend.py --variant gated --output tmp/raw-gated.json --scratch tmp/raw-gated
```

Use an isolated pinned Lean 4.33.1 checkout and build before benchmarking.
The original 38 inputs, 20-second wall/CPU, Linux 16-GiB address-space,
one-thread, 32768-KiB stack and original `#eval` invocation are retained.
Raw probes compare the old `TerminalDecisionLazy` with `InfiniteDecisionLazy`
directly; the other 31 compare existing fast and prepared endpoints. The
fixed manifest includes all 38, the 19 generated fixtures and 14 named C029
probes; CI freezes its hash. The independent validation writer owns no proof
implementation. A parsed value without an expected value or reference
comparison is not a validated result.

The matched run at `471f973` completes 38/38 candidate inputs versus 33/38;
all five raw UNKNOWNs are resolved, with the seven raw calls taking
0.669–0.719 seconds. The unchanged deeper corpus still passes 19/19 in a
separate E058 run. Fourteen abstract comparisons include missing transitions,
pre-final loops, terminal-only cases, unsafe initial states and nonabsorbing
instances. Two cases have no independent expected value and test Boolean
equality only. The semantic C029 theorem still requires absorption.

Separate larger raw tests complete n=3 and return UNKNOWN for n=4. The forced
`--run` trace locates that n=4 timeout in summary construction, before cycle
search. Diagnostic timings include forcing/output overhead and are separate
from the matched uninstrumented run. The proof is generic exact/bounded-list
search equality plus a necessary zero-cut safety gate, then raw and prepared
composition. It changes no cycle bound, monitor language or terminal decision.

[Source-pinned receipt and preserved ablations](../results/raw-backend.json);
[ordinary argument](../notes/2026-09-20-raw-backend.md);
[proof, review, tests and limitations](../notes/2026-09-20-raw-backend-readback.md).
This is a proved runtime refinement, not a new complexity or signature result.


<a id="e060"></a>

### E060 — Exact cached raw summary construction

```sh
python3 scripts/check_summary_cached.py --cli --output tmp/summary-audit.json
python3 experiments/check_summary_cached.py --components --timeout 60 --output tmp/summary-components.json --scratch tmp/summary-components
python3 experiments/check_summary_cached.py --full38 --compare-baseline --timeout 20 --output tmp/summary-matched.json --scratch tmp/summary-matched
python3 experiments/check_summary_cached.py --stress-raw --compare-baseline --timeout 20 --output tmp/summary-stress.json --scratch tmp/summary-stress
python3 experiments/profile_raw_summary.py --variant cached --timeout 20 --output tmp/summary-profile.json --scratch tmp/summary-profile
```

Build `Subtail.EntailmentPrepared` on pinned Lean 4.33.1 first. Raw comparison
uses the previous `InfiniteDecisionLazy` endpoint and the cached public raw
endpoint directly, retaining the original `#eval` invocation and 20-second
wall/CPU, Linux 16-GiB address-space, one-thread, 32768-KiB stack limits. All 38
fixtures and 19 deeper inputs retain their identity. Larger stress has empty
premises and query `0 <= 1` at 3/4/5/6 variables, independently false by the root/bottom
countermodel. Only the displayed inputs support performance claims.

Whole-instance validation covers 29 constraint cases and all 83 queries, with
candidate and reference emitted in 166 separate processes. The independent
P-automaton oracle compares every initial index, transition, Bad/final bit and
ordered flag, including diagonal/unreachable states. There are no digest-only
comparisons in this new check. Its correctness-only CI cap is 60 seconds for the
slow reference; raw performance remains 20 seconds. UNKNOWN cannot pass the
component gate or supply a Boolean answer.

The Lean proof is literal whole-Instance equality under the exact System/cache
invariant, then unconditional public raw/frontend equality. Build, kernel,
47 declaration closures, 23 runtime closures and actual CLI/model/cap checks pass.
The earlier core and deeper/component checks retain their distinct scopes.

[Ordinary route and failed attempts](../notes/2026-09-20-raw-summary.md);
[exact proof/measurement readback](../notes/2026-09-20-raw-summary-readback.md);
[source-pinned receipts](../results/raw-summary.json).
Relation caching alone failed to remove the four-variable timeout. Reusing
decoded physical states succeeds on four/five variables; six remains UNKNOWN.
The `--run` profiler is diagnostic and forces only the final-vector size at
its summary marker. It is separate from the matched uninstrumented benchmark.
Batched timeout, output truncation and initial proof-elaboration failures are
preserved. No smaller state space, complexity, memory, C080 or signature claim
is inferred from these measurements.


<a id="e061"></a>

### E061 — Independent terminal and shared-generator fixtures

```sh
python3 experiments/issue67_independent_fixtures.py --output tmp/issue67/strict.json
python3 experiments/issue67_independent_fixtures.py --seed 77 --output tmp/issue67/replay.json
python3 experiments/issue67_independent_fixtures.py --mode stress --max-work 100000 --wall-seconds 20 --cpu-seconds 18 --output tmp/issue67/stress.json
```

The independent oracle checks literal cut/suffix witnesses, reverse-prefix
safety, direct-string prefix graphs and table-observer BFS. It derives a
complete path bound by checking the entire finite transition graph is acyclic;
it refuses cyclic inputs. Expected answers do not call the compiler evaluator.
The 13 strict cases cover ordered/reversed flags, diagonal and empty cuts,
empty witnesses, overlapping returns, coincident marks and a nonempty self-wrap.

Two original compiler invocations replay the chain `0 -> 00 -> 000` from a
shared intermediate reference. This is certificate-directed depth-two replay.
The shared-generator positive and negative queries use exact-length and parity
observers on one common first return. The negative query has individually
satisfiable atoms but no common extension. A scoped ordinary argument removes
only unsatisfiable shape classes of the unchanged Python compiler. The complete
remaining S-only projection evaluates 4,880 positive and 6,480 negative compiled
clauses, with one and zero satisfying clauses respectively. This is not physical
exhaustion of the original unpruned iterator.

The author's partial-source receipt is preserved. A fresh complete checkout at
`da74a4327579ac090846e142f7a1fb834451a7bb` passes all 13 cases under both hash
seeds on Python 3.13.14/Linux AArch64, with identical within-host logical rows.
All six original-decider/unpruned-union stress cases remain UNKNOWN at 100,001
work units for a 100,000-unit limit. Native Lean and original-expression C081
frontend coverage are NOT RUN here; automatic successful depth two remains open.
No existing implementation, proof, default import or CI workflow changes.

[Exact oracle/projection argument and author limitations](../notes/2026-09-20-issue67-independent-fixtures.md);
[author receipt](../results/issue67-independent/receipt.json);
[full-checkout replay and review scope](../notes/2026-09-20-issue67-replay.md);
[complete parent receipt](../results/issue67-independent/full-checkout-replay.json).


**Native follow-up, September 21.** The accepted driver and supervisor from
`3135cd075e8ce31292fa609d3e9b3a80b2b9bb35` are now integrated. On Linux run:

```sh
(cd lean && lake build +Subtail.EntailmentPrepared +Subtail.TerminalDecisionLazy)
python3 experiments/issue67_native_probe.py --mode selftest --output tmp/issue67/native-supervisor.json
python3 experiments/issue67_native_probe.py --mode acceptance --output tmp/issue67/native-acceptance.json
python3 experiments/issue67_native_probe.py --mode stress --output tmp/issue67/native-stress.json
```

Fourteen strict cases must pass. The six stress cases may remain UNKNOWN;
inspections, phase probes and frontend shortcuts never receive automatic
promotion credit. Wall/CPU limits and a sampled process-group RSS threshold
bound runs; a 50ms sampler can overshoot its memory threshold. The fresh
[publication receipt](../results/publication-reproduction-20260921.json) records
actual outcomes and all source pins. This is diagnostic validation, not a new
proof, performance improvement or completion of the broader #67 scope.


<a id="e062"></a>

### E062 — Smaller compiler and original-F regression evidence

```sh
python3 experiments/check_smaller_compiler_astra.py --output tmp/compiler-literal.json
python3 experiments/check_smaller_compiler_astra.py --repository --output tmp/compiler-repository.json
python3 experiments/f_only_astra.py --output tmp/f-bounded.json
python3 scripts/check_original_bounds.py
```

The compiler corpus checks common assignments and generators, repeated interval
coordinates, empty/zero-length cases, ordered flags and exact integer envelopes.
The repository mode also replays the unchanged old compiler's oversized clause;
the new filter rejects that diagram. The saved standalone receipt must match.
These are bounded literal checks, not an enumeration of all possible diagrams.

The F corpus uses seed `2026092069`, 1,000 random trials, random word cap 10 and
three-state census word cap 8. It checks literal witnesses, return deletion,
finishing cases and integer comparisons. It returns
`PASS_BOUNDED_CHECKS_NOT_GLOBAL_PROOF`; unsuccessful capped searches remain
UNKNOWN unless independently decided. Its semantic receipt matches the saved
one except for Python/platform and elapsed-time metadata.

The last command additionally builds and kernel-replays the three integrated
Lean modules, audits all 48 public declarations and runs native guards. The
all-input theorem comes from those checked declarations and their independent
mathematical review, not from the bounded corpus.
[C086](../research/claims.md#c086),
[combined validation](../notes/2026-09-20-original-bounds-integration.md),
[compiler receipt](../results/smaller-compiler-astra.json),
[F receipt](../results/f-only-astra.json).

<a id="e063"></a>

### E063 — Exact-domain Henglein–Rehof hardness transfer

```sh
python3 experiments/check_hr_topfree_transfer_70.py --output tmp/hr-topfree-transfer-70.json
```

Seed `2026092070`. The independent checker covers 4,104 exhaustive one/two-state
epsilon-NFAs and 400 seeded cases, 33,447 premise comparisons, and 4,913
additional graph valuations that are not restricted to the encoding's image.
It also checks 677 finite state-value assignments against an infinite reference.
The graph comparisons are exact for their regular unfoldings. The failed
identity/reversed/finite-reference repairs are preserved expected counterexamples,
not failures of the final marker reduction. The finite corpus is no all-input
proof and yields no finite-model lower bound.

[C087](../research/claims.md#c087),
[unchanged receipt](../results/hr-topfree-transfer-70.json),
[ordinary proof](../notes/2026-09-20-hr-topfree-transfer-70.md),
[fresh replay and independent review](../notes/2026-09-20-hardness-top-integration.md).

<a id="e064"></a>

### E064 — Compatible explicit-top projections

```sh
python3 experiments/check_explicit_top_dual_projection.py --output tmp/explicit-top-dual-projection.json
python3 scripts/test_check_explicit_top.py
python3 scripts/check_explicit_top.py
```

Seed `2026092071`. The independent graph/tree predicates check 393 systems,
5,156 lifted projected models, 292 same-observation-word countermodels and
2,384 source projections. There are 1,444 finite-tree and 5,184 cyclic-graph
order comparisons. The 217 systems without two bounded projection witnesses
remain UNKNOWN, as do any absent bounded derivations. Limits include tree
depth 2, enumerated graphs through 2 nodes, targeted graphs through 4 nodes,
and direct derivation stack cap 6. No C081 backend is executed by this corpus.

The last command builds and kernel-replays the optional Std-only language
module, audits all 29 explicit declarations, and replays both E063 and E064.
It rejects unused custom axioms/placeholders, unexpected imports and incomplete
audit output. Main/PR Lean CI runs these checks. Semantic JSON fields match
the unchanged author receipts; only recorded Python/platform/machine fields
are ignored as applicable. The full C088 expression/tree reduction remains
an ordinary proof, not a result of finite tests or a native Lean top solver.

[C088](../research/claims.md#c088),
[unchanged receipt](../results/explicit-top-dual-projection.json),
[ordinary proof](../notes/2026-09-20-explicit-top-dual-projection.md),
[combined validation](../notes/2026-09-20-hardness-top-integration.md).

<a id="e065"></a>

### E065 — Fixed-arity summary and binary-code components

- **Command:** `python3 experiments/ternary_transfer.py --output tmp/ternary-transfer.json`
- **Claim:** [C089](../research/claims.md#c089); ordinary reduction with independent review.
- **Saved evidence:** [author receipt](../results/ternary-transfer.json).
- **Coverage:** finite summary/oracle comparisons, binary coding including
  incomplete-word completion, exact graph countermodels and naming fixtures.
  The `coding`, `expressions`, `full_pipeline_fixtures` and `status` fields
  distinguish the checks. The complete generalized pipeline and its actual
  C029 invocation are not executed.

<a id="e066"></a>

### E066 — Graph-only first-return component checks

- **Command:** `python3 experiments/standalone_first_return_astra.py --output tmp/standalone-first-return-astra.json`
- **Claim:** [C090](../research/claims.md#c090); ordinary schema theorem with independent review.
- **Saved evidence:** [author receipt](../results/standalone-first-return-astra.json).
- **Coverage:** shared-generator and origin constraints, interval products,
  empty and singleton boundaries, and failed stronger entrance/inverse-edge
  claims. `bounds`, `fixtures`, `interval_products` and `status` retain the
  finite scope. This is not an implementation of the complete generic compiler.

<a id="e067"></a>

### E067 — Function-only characterization and obstruction fixtures

- **Command:** `python3 experiments/check_function_only_transfer.py --output tmp/function-only-transfer.json`
- **Claim:** [C091](../research/claims.md#c091); ordinary characterization and precise obstruction.
- **Saved evidence:** [author receipt](../results/function-only-transfer.json).
- **Coverage:** 676 finite-pair comparisons, 729 small regular graph pairs,
  500 seeded graph samples, 2,025 finite-expression Horn cases and 1,300
  variable-only seeded countermodel cases. `counts`, `counterexample`,
  `random_seed`, `limitations` and `status` delimit evidence. This proves no
  general function decision and implements no general guarded-closure solver.

The continuing main/PR checks replay E065–E067 using
`python3 scripts/check_research_submissions.py`. It compares all scientific
receipt fields, including embedded source hashes, against preserved author
receipts. Only recorded platform/Python/timing metadata is ignored. Fresh
outputs go to `tmp/`; the historical receipts are not overwritten.

## Reconciled supporting evidence (September 20)

The original [concrete compiler-weight counterexample](check_rank_query_weight_counterexample.py)
and its [deterministic output](../results/rank-query-weight-counterexample.json)
are preserved from PR #47. Reproduce with
`python3 experiments/check_rank_query_weight_counterexample.py > /tmp/weight.json`
and `cmp results/rank-query-weight-counterexample.json /tmp/weight.json`.
This source-transcribed checker is separate from C082's checked native theorem;
the original F alone is not refuted by its oversized emitted clause.

The optional C030 direct proof is now integrated with continued CI coverage.
Its independent replay command is
`python3 experiments/replay_c030_independent.py --output /tmp/c030-replay.json`.
Fresh combined-tree build, kernel/dependency audit and replay commands/results
are recorded in the [reconciliation note](../notes/2026-09-20-repository-reconciliation.md)
and [receipt](../results/repository-reconciliation.json). Existing fixtures,
seeds, counts and original failed attempts are unchanged; no new performance
experiment or formal budget-preservation claim is inferred from this replay.
