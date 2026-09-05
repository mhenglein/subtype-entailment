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
- **Constructed hard-budget families (updated).** E014/E015 remain historical
  finite examples. C046/E031 below now give a proved superpolynomial
  terminal family with a word-preserving subtype realization.
- **SEP-derived instance pipeline.** No executable experiment yet proves that
  the abstract summary automata and flag relations generated by `W` satisfy a
  structural restriction strong enough to bound `B(I)`.

## Adding an experiment

Use the next available ID. Record the exact command, code location, commit or
input generator, seed, word/state/resource limits, output JSON paths, and the
claim IDs that the run can support. Keep `UNKNOWN` separate from `NO`, and add
a new result key rather than silently changing the meaning of an existing key.


<a id="e031"></a>

### E031 - Modular synchronization and coordinated-deletion counterexamples

**Command.** `python3 experiments/check_modular_sync.py`

**Code.** [Checker](check_modular_sync.py) and
[family generator](modular_sync_family.py); Python 3.9+, standard library only.
The saved [result](../results/modular-synchronization.json) records dependency
Git blob hashes, the full eight-state automaton, its 17-variable subtype
realization, all budget-split results, and parameterized checks.

**Coverage.** 32,767 binary words through length 14; 596 complete finite graph
searches across nine parameter tuples, including all 28 splits below budget
seven for the primary example; 288 exponent vectors; 18 word-budget checks;
153 exact regular-countermodel checks; 152 full/reduced summary comparisons;
3,276 bounded count vectors for the coordinated-deletion family; and all 40
zero/one/two-deletion sets for the seven-state three-block example.

**Result.** PASS. The primary word `11111101111110` is the unique shortest
witness, has exact budget seven on eight states, and has no shorter accepted
profile-dominated replacement. The general parameter formulas and the
superpolynomial bound come from the written proof, not the finite samples.
Large growth rows evaluate those formulas; they do not report graph searches
at the displayed large budgets. A graph cap would fail the exact regression
as inconclusive, never become NO.

**Claims informed.** [C046](../research/claims.md#c046),
[C047](../research/claims.md#c047), and refutations of
[Q002](../research/conjectures/Q002.md) and [Q003](../research/conjectures/Q003.md).
The original core border regression was separately replayed byte-for-byte;
the new proofs are not Lean-checked and independent review is requested.
