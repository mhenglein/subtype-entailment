# Claims ledger

Last reviewed: 2026-09-04

This ledger gives stable IDs for claims about Problem 1.7 and its BorderAvoid
reduction. It is the shared index for notes, experiments, and future review.

**Problem status:** Problem 1.7 remains unsolved in this repository. No claim
below establishes a general subtype decision procedure or reproduces the
memo's original census. Results for named restricted classes are separate.

## Evidence labels

- **MEMO:** reported in `sep-topfree.pdf`. The original `analysis-2026`
  scripts were unavailable when this repository was checked.
- **AUDIT:** a written proof inspection in this repository found the argument
  sound under the stated assumptions. This is not a proof-assistant
  formalization.
- **WRITTEN PROOF:** a mathematical proof was added to the review or notes.
  This label alone does not claim machine formalization.
- **LEAN:** the linked statement and its dependencies compile with the pinned
  Lean toolchain and pass the recorded axiom audit. Scope and hypotheses still
  matter; a conditional theorem does not prove its assumptions.
- **REPRO:** the committed Python code reproduced the stated finite cases.
  This is bounded evidence, not an all-length proof.
- **COUNTEREXAMPLE:** an explicit family or instance refutes the stated
  target under the stated model.
- **OPEN:** the claim is a gap, question, or status boundary. Do not treat it
  as a result.

## Claim records

<a id="c001"></a>

### C001 — Top-free path-set semantics

**Claim.** Under the memo's arbitrary-tree semantics, a type over `bottom` and
binary covariant product is represented by a prefix-closed path set
`X(t) subseteq {0,1}*`, and subtyping is set inclusion.

**Scope.** Variables range over arbitrary, possibly infinite trees. This claim
does not identify arbitrary-tree semantics with finite-tree semantics.

**Status.** `AUDIT` — proof inspection of the memo's Definition 1.1 and Lemmas 1.3 and 1.8
and the accompanying closure construction.

**Evidence.** [Proof audit](../notes/proof-audit.md#established-arguments);
[review](../REVIEW.md#1-what-the-problem-actually-asks).

**Limit.** The inverse construction needs the precise domain
`{epsilon} union X union X{0,1}`. See the proof audit for that formal detail.

<a id="c002"></a>

### C002 — Regular countermodels suffice for arbitrary entailment

**Claim.** For the memo's arbitrary-tree semantics, the regular countermodel
reduction in Theorem 2.6 and Corollary 2.7 is sound: if entailment fails, a
possibly infinite regular countermodel is enough.

**Scope.** Finite constraint sets satisfying the memo's stated satisfiability
premise. “Regular” here allows infinite trees whose path languages are regular.

**Status.** `AUDIT` — proof inspection, with one omitted invocation of
satisfiability and Proposition 2.5 recorded as a proof repair.

**Evidence.** [Proof audit](../notes/proof-audit.md#overall-status);
[proof audit](../notes/proof-audit.md#established-arguments).

**Limit.** This says nothing about finite-tree entailment. The finite and
arbitrary domains can differ for the same constraints.

<a id="c003"></a>

### C003 — The established reduction direction

**Claim.** The reviewed argument establishes the forward direction
`top-free SEP <= PrefixAvoid <= BorderAvoid`: a top-free subtype
counterexample gives a path satisfying the regular side conditions `(S)` and
`(F)` while avoiding the prefix-reach relation, and the later border form
encodes that avoidance.

**Scope.** Summary structures and transition systems produced by the memo's
normalization and pushdown system `W`.

**Status.** `AUDIT` — forward proof inspected. The converse from arbitrary
regular annotations remains unfinished.

**Evidence.** [Proof audit](../notes/proof-audit.md#established-arguments);
[review](../REVIEW.md#5-keep-the-reductions-and-negative-claims-precise).

**Limit.** A decision procedure for arbitrary BorderAvoid would decide Problem 1.7 through the forward reduction. Transferring an abstract hardness or undecidability result requires a converse or a reduction into actual SEP-derived instances.

<a id="c004"></a>

### C004 — Minimum-stack decomposition leaves periodic caps

**Claim.** For the memo's advertised push/pop/epsilon transition model, the
minimum-stack decomposition yields a finite union of regular heads followed by
periodic caps. Reversing the word turns the periodic condition into a border
condition, including empty and full borders.

**Scope.** The fixed transition model and endpoint-state slices used in the
memo. The result concerns the decomposition, not regularity of the entire
reachability relation.

**Status.** `AUDIT` — Theorem 4.2 and the border translation were inspected.

**Evidence.** [Proof audit](../notes/proof-audit.md#established-arguments);
[border audit](../notes/border-audit.md#claim-by-claim-audit).

**Limit.** The periodic residual is exactly the hard part. This claim does not
give a finite automaton for all prefix reachability.

<a id="c005"></a>

### C005 — The old exact regularity formula fails

**Claim.** In the memo's C0 push-only construction, the reachability language

`M = { 0^j 1 u : j >= 0 and u is a prefix of (0^j 1)^omega }`

is nonregular: its intersection with `0* 1 0* 1` is
`{0^j 1 0^j 1 : j >= 0}`. Therefore the earlier proposed exact regular-language
description is false.

**Scope.** The stated C0/push-only system and the fixed state slice used in the
nonregularity argument.

**Status.** `WRITTEN PROOF` in the proof audit, with `REPRO` bounded checks of
the closed-form characterization and the old formula.

**Evidence.** [Proof audit](../notes/proof-audit.md#established-arguments);
[experiment code](../experiments/run_experiments.py);
[result keys](../results/independent-checks.json) under
`theorem_3_2.words_checked`, `theorem_3_2.formula_disagreements`, and
`theorem_3_2.two_ones_language`.

**Limit.** The executable check covers binary words of length at most 11. The
all-length nonregularity conclusion comes from the written argument, not from
that finite check.

<a id="c006"></a>

### C006 — Rigidity does not imply nonmerging

**Claim.** Remark 8.17's equivalence is false. Rigidity only compares the
states at the starts of the first and last occurrences of each repeated suffix;
the two runs can merge later.

**Scope.** The partial two-state DFA with start `q0`, final state `f`,
`delta(q0,0)=f`, `delta(f,0)=f`, undefined `1` transitions, empty `Bad`, and
`G={(f,q0)}`. For every `n >= 1`, `0^n` is a witness and is rigid, while the
two runs merge after the first `0` whenever the repeated suffix is nonempty.

**Status.** `COUNTEREXAMPLE` — explicit all-length family. The source memo's
claim is refuted under the reviewed definition.

**Evidence.** [Review](../REVIEW.md#2-the-main-defect-rigidity-does-not-imply-nonmerging);
[border audit](../notes/border-audit.md#refutation-of-remark-817s-equivalence);
[family code](../experiments/border_lab.py) in `rigid_family()`.

**Limit.** The empty word needs separate handling because it cannot satisfy the
literal rigidity definition.

<a id="c007"></a>

### C007 — No universal `lrs` bound for all rigid witnesses

**Claim.** No bound on the longest repeated suffix `lrs` of **every** rigid
witness can depend only on the number of DFA states. The family in C006 has
two states and `lrs(0^n)=n-1` for every `n >= 1`.

**Scope.** Universal bounds over all rigid witnesses of arbitrary abstract
instances.

**Status.** `COUNTEREXAMPLE` — follows from the all-length family in C006.

**Evidence.** [Review](../REVIEW.md#2-the-main-defect-rigidity-does-not-imply-nonmerging);
[result keys](../results/independent-checks.json) under `rigid_family`.

**Limit.** This does not refute an existential computable bound on the minimum
successful instance budget `B(I)`, or a bound for shortest witnesses.

<a id="c008"></a>

### C008 — Suffix-trace truncation is sufficient

**Claim.** Let `pi` be a witness of length `n`, choose `0 <= e < n`, set
`v=pi[:e]` and `h=lrs(v)`. If `suffix_h(v)=suffix_h(pi)` and
`c(e-h)=c(n-h)`, then `v` is a witness. The case `h=0` is allowed and the
suffix equality is then automatic.

**Scope.** Defined runs of the reviewed partial DFA model, with its `Fin`,
`Bad`, and ordered flag obligations.

**Status.** `WRITTEN PROOF` for the stated finite-alphabet setting; `LEAN` for
the binary specialization, with `REPRO` bounded validation. Its literature
novelty is unknown.

**Evidence.** [Review](../REVIEW.md#3-a-stronger-truncation-rule);
[border audit](../notes/border-audit.md#a-stronger-useful-truncation-lemma);
[result keys](../results/independent-checks.json) under
`checks.suffix_trace_cuts` and `checks.cuts_on_rigid_words`.
The Lean theorem is `suffix_trace_truncation` in
[Truncation.lean](../lean/Subtail/Truncation.lean), checked by
[E008](../experiments/README.md#e008).

**Limit.** A sufficient cut is not a pumping theorem. It does not yet imply a
computable bound on `B(I)`.

<a id="c009"></a>

### C009 — Incoming-flag-set dominance is also sufficient

**Claim.** Define `Pred_G(q)={r : G(r,q)}`. In C008, state equality can be
replaced by: `c(e)` is accepting and
`Pred_G(c(e-lambda)) subseteq Pred_G(c(n-lambda))` for every
`0 <= lambda <= h`.

**Scope.** The same defined-run and suffix-transfer setting as C008.

**Status.** `WRITTEN PROOF` for the stated finite-alphabet setting; `LEAN` for
the binary specialization, with `REPRO` bounded validation. This is a
sufficient condition only.

**Evidence.** [Review](../REVIEW.md#3-a-stronger-truncation-rule);
[implementation](../experiments/border_lab.py) in `suffix_trace_cut(...,
use_profiles=True)`; [result keys](../results/independent-checks.json) under
`checks.profile_dominance_cuts`.
The Lean theorem is `profile_truncation` in
[Truncation.lean](../lean/Subtail/Truncation.lean), checked by
[E008](../experiments/README.md#e008).

**Limit.** Shortest witnesses resist every applicable cut only relative to the
tested criterion. That observation alone gives no bound.

<a id="c010"></a>

### C010 — Fixed-budget Sandwich searches have a precise status rule

**Claim.** For fixed `L,D`, the committed `Sandwich` implementation checks the
reviewed necessary and sufficient border predicates, including defined runs,
the start-state endpoint, and empty/full borders. Its finite graph search
returns `YES` with a word, `NO` only after graph exhaustion, and `UNKNOWN` on
the explicit state cap.

**Scope.** The implementation in `experiments/border_lab.py`, under its stated
finite-word and partial-DFA conventions.

**Status.** `AUDIT + REPRO` — construction and invariants were inspected, and
bounded comparisons passed. The whole implementation is not formally verified.

**Evidence.** [Border audit](../notes/border-audit.md#independent-finite-state-check);
[implementation](../experiments/border_lab.py) in `Sandwich`; [result keys](../results/independent-checks.json)
under `checks.automaton_comparisons`, `checks.finite_state_searches`,
`search_statuses`, and `failures`.

**Limit.** Fixed-budget search does not provide a global budget bound. A
resource limit must remain `UNKNOWN`, even when no word was found before it.

<a id="c011"></a>

### C011 — Singleton accepted-word instances have linear exact budget

**Claim.** For the `(n+1)`-state partial DFA whose only accepted word is
`0^n`, with empty `G`, the exact instance budget is
`B(I_n)=n-1` for every `n >= 1`.

**Scope.** The explicit abstract instances generated by `fixed_word_instance`.
Here `B(I)` is the least `L+D` for which the sufficient search has a witness.

**Status.** `WRITTEN PROOF` for this family, with `REPRO` exact lower-budget
exhaustion for selected values of `n`.

**Evidence.** [Review](../REVIEW.md#4-independent-experiments);
[instance generator](../experiments/border_lab.py) in `fixed_word_instance`;
[result keys](../results/independent-checks.json) under `singleton_budget_family`.

**Limit.** This refutes a constant budget bound for arbitrary abstract
instances. It does not imply undecidability and does not contradict a bound
for the memo's sampled or SEP-derived instances.

<a id="c012"></a>

### C012 — The budget criterion is conditional, and the target remains open

**Claim.** Under finite effective encodings, Theorem 8.9 reduces decidability
of abstract BorderAvoid to the existence of a computable upper bound on the
least successful budget `B(I)`. The memo and this review do not provide that
bound for BorderAvoid or for Problem 1.7, and no exact top-free entailment
decision procedure is established here.

**Scope.** Abstract BorderAvoid instances with an effective finite encoding,
then the narrower semantic top-free subtype problem.

**Status.** `AUDIT + OPEN` — the equivalence proof was inspected, but the
substantive bound and the top-free converse remain open.

**Evidence.** [Review](../REVIEW.md#1-what-the-problem-actually-asks);
[proof audit](../notes/proof-audit.md#consequence-for-the-attack);
[bounded literature check](../notes/literature-check.md#status).

**Limit.** A source search is not proof that no later result exists. Do not
promote the memo's unavailable source census or a bounded search to a global
undecidability, decidability, or complexity claim.

<a id="c013"></a>

### C013 — Context-restricted flag comparison preserves truncation

**Claim.** In C009, compare incoming flags only from states visited in the
retained prefix. More precisely, write `V_e={c(i):0<=i<=e}`. For every
`0<=lambda<=h`, require
`Pred_G(c(e-lambda)) intersect V_e subseteq Pred_G(c(n-lambda))`.
With the same suffix and acceptance hypotheses, `v` is still a witness.

The condition can be weakened further by replacing `V_e` with the states at
positions `i<e-lambda`, or only those positions where the suffix of length
`lambda` occurs. These are three sufficient conditions, not a claim that no
further weakening is possible.

**Scope.** Finite words and the same partial-DFA conventions as C009,
including the empty suffix, diagonal pairs, and `e=0`.

**Status.** `WRITTEN PROOF` for all three context variants. `LEAN` for the
binary visited-state variant. `REPRO` for the explicit strict examples and
bounded implication checks.

**Evidence.** [Context-cut proof](../notes/2026-09-04-context-cut.md);
`visited_profile_truncation` in
[Truncation.lean](../lean/Subtail/Truncation.lean);
[E008](../experiments/README.md#e008), [E010](../experiments/README.md#e010).

**Limit.** `0010 -> 00` shows that the visited-state rule can apply when C009
fails. The exact-occurrence rule is close to checking the shortened word
directly. None of these rules gives a global budget bound.

<a id="c014"></a>

### C014 — Finite budget enumeration is conditionally correct

**Claim.** Let `size`, `F`, and `success I L D` be supplied executable
functions. Suppose a successful test always yields a binary BorderAvoid
witness, and every instance with a witness has a successful pair satisfying
`L+D<=F(size I)`. Enumerating those finitely many pairs returns true exactly
when the instance has a witness.

**Scope.** Binary finite instances `Instance k`. The theorem exposes the
test-soundness and bounded-coverage hypotheses explicitly.

**Status.** `LEAN`, conditional. The runtime enumeration is total given its
function arguments; the theorem does not supply their implementations.

**Evidence.** `finiteBudgetDecision_correct` in
[Conditional.lean](../lean/Subtail/Conditional.lean);
[formalization note](../notes/2026-09-04-lean-core.md);
[E008](../experiments/README.md#e008).

**Limit.** The fixed-budget automaton, computable bound, semantic subtype
reduction, and their correctness proofs remain to be supplied. This is the
forward finite-enumeration argument, not a full formalization of the
equivalence in Theorem 8.9.

<a id="c015"></a>

### C015 — Supplied-path regular countermodels can be checked by automata

**Claim.** The new Python bridge represents all four normalized constraint
forms, saturates a finite P-automaton for seed reachability, and validates a
proposed regular countermodel using exact finite automata operations. Its
runtime checks have no stack-depth cutoff. The finite-depth closure is used
only as a diagnostic oracle.

**Scope.** Normalized binary top-free constraints and one supplied candidate
path. The output path sets may represent infinite regular trees.

**Status.** `AUDIT + REPRO` for the implementation and recorded cases. The
independent audit found no push/pop orientation or empty-stack error. This is
not a proof-assistant verification of P-automaton saturation.

**Evidence.** [Bridge implementation](../experiments/topfree_bridge.py);
[foundation and proof obligations](../notes/2026-09-04-bridge-foundation.md);
[E009](../experiments/README.md#e009).

**Limit.** A rejected path does not establish entailment. Normalization from
general input syntax and a complete search over candidate paths remain open.
The later summary-class implementation is recorded separately as C017.
See the note for the remaining all-input formal proof obligations.

<a id="c016"></a>

### C016 — Boundary slices give exact restricted decisions

**Claim.** Fix a final state `f` and forbid
`D_f = Bad union {q:G(q,q)} union {q:G(q,f)}`. The union of the resulting
single-final-state regular languages is exactly `N''(0,0)`. A full witness
additionally avoids the proper nonempty agreements `i<j<|w|`.

For at most two states, boundary nonemptiness is equivalent to witness
existence: a shortest boundary path has length at most one and hence no
proper obligations. Every nonempty such instance has `B=0`.

More generally, if no flagged ordered pair can occur on any accepting
boundary-safe run, the full witness language equals the boundary language.
This certified regular subclass has `B<=max(0,|K|-2)` when nonempty.

**Scope.** Well-formed finite annotated automata. The graph proofs allow any
finite alphabet; the current Lean specialization and census are binary.

**Status.** `WRITTEN PROOF + AUDIT` for the graph decisions and subclass
bound. `LEAN` for the boundary decomposition, zero-budget equivalence, and
the executable exact two-state decision.
`REPRO` for the implementations and corrected experimental baselines.

**Evidence.** [Boundary proof](../notes/2026-09-04-boundary-slices.md),
[Boundary.lean](../lean/Subtail/Boundary.lean),
[TwoState.lean](../lean/Subtail/TwoState.lean),
[E012](../experiments/README.md#e012), [E008](../experiments/README.md#e008).

**Limit.** Failure of the regularity certificate means UNKNOWN. Two subtype
variables need not produce a two-state automaton. The bound does not extend
to unrestricted BorderAvoid. None of E011's five budget increases survives
full boundary normalization; equal budgets do not imply equal languages.

<a id="c017"></a>

### C017 — Actual summary classes preserve the subtype side conditions

**Claim.** The Python construction builds paired pop-summary subsets for
`W` and `W^rev`, flags them by `B(left) intersect A(right)`, and retains the
memo's forced-root endpoint condition F and every-prefix denial condition S.
It outputs a `border_lab.Instance` for a satisfiable normalized constraint
system and query. Unsatisfiable input is explicitly rejected before summary
witnesses can be interpreted as counterexamples.

**Scope.** The four normalized binary top-free constraint forms. Query
variables may be absent from the constraints. Summary construction uses
finite saturation without a stack-depth cutoff.

**Status.** `AUDIT + REPRO`. The audit checked saturation and orientation,
identified generator consumption and a missing satisfiability guard, and
the implementation fixes both with regressions. This is not a Lean proof of
the complete reduction.

**Evidence.** [Summary construction](../experiments/summary_bridge.py),
[summary note](../notes/2026-09-04-summary-bridge.md),
[E013](../experiments/README.md#e013).

**Limit.** The finite comparisons cover particular input systems and candidate
words. General input normalization, formal verification of the all-word
reduction, and a complete witness search remain. This forward construction
does not realize arbitrary abstract flags as subtype inputs.

<a id="c018"></a>

### C018 — Direct budget predicates have checked soundness and coverage

**Claim.** For every binary instance and word, the Lean direct predicates
satisfy `Witness -> Necessary(L,D)`, `Sufficient(L,D) -> Witness`, and
`Witness w -> Sufficient(lrs(w),0)`. Executable Boolean checkers are proved
equivalent to each predicate. The suffix-occurrence side condition is proved
equivalent to its reversed-prefix formulation.

**Scope.** Individual finite words, arbitrary nonnegative L and D, and the
partial-DFA witness semantics including empty and full borders.

**Status.** `LEAN`, with bounded native/Python agreement in E008.

**Evidence.** [SandwichPredicates.lean](../lean/Subtail/SandwichPredicates.lean),
[formalization note](../notes/2026-09-04-lean-sandwich.md),
[E008](../experiments/README.md#e008).

**Limit.** An executable checker for one word is not a decision procedure for
existence of a word. The exact fixed-budget finite automaton remains the open
part of O4. Individual lrs coverage supplies no computable instance bound.

<a id="c019"></a>

### C019 — Shortest witnesses expose exact cut obstructions

**Claim.** Let `pi` be shortest and `v=pi[:e]` a proper prefix. If `v` ends
in a final state and shares its suffix of length `h=lrs(v)` with `pi`, then
some suffix of length `lambda<=h` has a strict earlier occurrence at `i`
with `G(c(i),c(e-lambda))` but not `G(c(i),c(|pi|-lambda))`.

Aligned shared contexts of any length `H>=h`, with equal states at their
starts, would allow C008 to shorten the word and are therefore excluded.
A three-state example has shortest witness `001`; deleting its final-state
loop produces `00` and a new forbidden proper border.

**Scope.** The finite-alphabet setting of C008/C013. Critical occurrences
may be of the empty suffix. Their positions and contexts are unbounded.

**Status.** `WRITTEN PROOF`, as consequences of C008/C013; `COUNTEREXAMPLE`
to shortening based on repeated DFA states alone. The finite example has
independent forward and reversed predicate checks.

**Evidence.** [Structure note](../notes/2026-09-04-minimal-witness-structure.md),
[example checker](../experiments/check_minimal_structure.py),
[E014](../experiments/README.md#e014).

**Limit.** No finite complete summary, deletion theorem for arbitrary loops,
or global bound follows. The example increases shortest length while its
minimum sufficient budget is still zero.

<a id="c020"></a>

### C020 — Six states exceed the regular-subclass budget bound

**Claim.** The explicit six-state binary instance in E015 has computed exact
budget `B=5`, shortest witness `001011010101` of length 12, and full-boundary
budget one. It refutes `B<=max(0,|K|-2)` as a bound for all abstract instances.

**Scope.** One abstract partial DFA, obtained by retaining only the states
visited by a known witness in E014's eight-state attempt 3.

**Status.** `REPRO + COUNTEREXAMPLE`, using complete fixed-budget automaton
searches and independent direct checks. State restriction preserves every
surviving sufficient word. The lower-budget graph correctness is audited
Python/memo machinery, not a Lean-checked emptiness proof.

**Evidence.** [Instance and argument](../notes/2026-09-04-trimmed-budget.md),
[reproducer](../experiments/trim_budget_example.py),
[E015](../experiments/README.md#e015).

**Limit.** This does not refute `B<=|K|` or any computable bound. No subtype
realization or asymptotic growth family is established. It does not contradict
the regularity hypothesis in C016.

## Explicitly unestablished

The following are deliberately not accepted claims in this ledger:

- a converse from arbitrary BorderAvoid annotations to top-free subtype
  constraints;
- a computable bound on `B(I)` for SEP-derived instances;
- decidability, undecidability, or PSPACE membership for Problem 1.7;
- reproduction of the memo's original `analysis-2026` census.
