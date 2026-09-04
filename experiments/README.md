# Experiment index

This index gives stable IDs for executable checks. Each entry records the
exact command, its scope and limits, the claims it informs, and the JSON keys
that carry its result.

Run the current suite from the repository root with:

```text
python3 experiments/run_experiments.py
```

The command writes [results/independent-checks.json](../results/independent-checks.json)
and prints the same JSON. The implementation uses only the Python standard
library. See [border_lab.py](border_lab.py) for the executable predicates and
the finite reverse-reading automaton.

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
and zero failures. Runtime definitions do not depend on classical choice.
The truncation proofs use standard classical axioms in erased proofs.

**Claims informed.** [C008](../research/claims.md#c008),
[C009](../research/claims.md#c009), [C013](../research/claims.md#c013),
[C014](../research/claims.md#c014). No concrete global bound or fixed-budget
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
- **Constructed hard-budget families.** E011 tried a bounded random search
  and found only small flag-induced growth. No construction with stronger
  asymptotic growth has been established. A witness-preserving generator is
  a proposed next attempt.
- **SEP-derived instance pipeline.** No executable experiment yet proves that
  the abstract summary automata and flag relations generated by `W` satisfy a
  structural restriction strong enough to bound `B(I)`.

## Adding an experiment

Use the next available ID. Record the exact command, code location, commit or
input generator, seed, word/state/resource limits, output JSON paths, and the
claim IDs that the run can support. Keep `UNKNOWN` separate from `NO`, and add
a new result key rather than silently changing the meaning of an existing key.
