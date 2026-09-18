# Claims ledger

Index updated: 2026-09-18. Original C001-C020 review: 2026-09-04.
Later claims retain the evidence and review scope of their linked records.

This ledger gives stable IDs for claims about Problem 1.7 and its BorderAvoid
reduction. It is the shared index for notes, experiments, and future review.
Later continuation records are indexed in [Continued claim records](#continued-claim-records).

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

## Continued claim records

C021-C045 extend the C001-C020 ledger. This section is a navigation index, not
a second proof text: each anchored entry keeps the claim's status and scope,
and links to the authoritative note containing its full statement, argument,
evidence, and limitations. The continuation records are not Lean-checked;
`REPRO` remains bounded evidence under the labels defined above.

<a id="c021"></a>

### C021 — Exact budget-growth family

**Statement.** For integers `m>=2` and `1<=t<m`, the one-flag family has
`B(I(m,t))=m+t-1` and shortest length `2m+t+1`; taking `k=m+1` and `t=m-1`
gives exact budget `2k-4` and shortest length `3k-3`.

**Status / scope.** `WRITTEN PROOF + REPRO`; abstract BorderAvoid only. No
subtype realization or literature-priority claim.

**Record.** [Full statement and proof](../notes/2026-09-04-budget-growth-family.md).

<a id="c022"></a>

### C022 — Exact decision for at most three states

**Statement.** For well-formed instances with at most three states, witness
existence, a witness of length at most six, nonemptiness of `Sufficient(2,0)`,
and nonemptiness of `Necessary(1,1)` are equivalent; length six and budget two
are sharp.

**Status / scope.** `WRITTEN PROOF + REPRO`; the proof allows finite alphabets,
while the exhaustive census is binary. No larger-state decision follows.

**Record.** [Full statement and proof](../notes/2026-09-04-three-state.md).

<a id="c023"></a>

### C023 — Actual summary absorption invariant

**Statement.** Every positive successor of a final state in an actual paired
summary output is final, has an empty `A` component, and has an empty incoming
flag column. The invariant also holds with denials.

**Status / scope.** `WRITTEN PROOF + REPRO`; actual `W/F/G` summary outputs,
not arbitrary abstract BorderAvoid instances.

**Record.** [Full statement and proof](../notes/2026-09-04-summary-absorption.md).

<a id="c024"></a>

### C024 — Exact decision for the Bad-free absorbing subclass

**Statement.** Total, Bad-free absorbing instances over at least two letters
admit an exact graph decision with a padding witness, witness length at most
`2k-1`, and budget at most `k-1`.

**Status / scope.** `WRITTEN PROOF + REPRO`; denial-free normalized subtype
outputs are included only through the audited forward bridge.

**Record.** [Full statement and proof](../notes/2026-09-04-summary-absorption.md).

<a id="c025"></a>

### C025 — Denial safety needs no separate subset component

**Statement.** On satisfiable normalized inputs, every-prefix safety is exactly
avoidance of `B(u) ∩ D`; the separate `S` subset component is redundant.

**Status / scope.** `WRITTEN PROOF + REPRO`; the satisfiability guard is
essential, and the claim concerns normalized subtype inputs.

**Record.** [Full statement and proof](../notes/2026-09-04-denials-and-continuations.md).

<a id="c026"></a>

### C026 — Exact continuation after a supplied safe prefix

**Statement.** After a supplied safe prefix enters the zero-column final
region, existence of a safe witnessing extension is decidable by a finite
periodic-ray product.

**Status / scope.** `WRITTEN PROOF + REPRO`; the result is local to the supplied
prefix. `NO_EXTENSION` is not unrestricted `NO`; entry-frontier completeness
also requires an acyclic safe pre-zero region.

**Record.** [Full statement and proof](../notes/2026-09-04-denials-and-continuations.md).

<a id="c027"></a>

### C027 — Cubic branching witness certificate

**Statement.** A reachable safe cyclic zero-region vertex with two safe outgoing
letters supplies a cubic-length witness certificate.

**Status / scope.** `WRITTEN PROOF + REPRO`; the alternate edge may leave the
cycle, and absence of this certificate is not `NO`.

**Record.** [Full statement and proof](../notes/2026-09-04-denials-and-continuations.md).

<a id="c028"></a>

### C028 — Actual subtype obstruction to deleting pre-final loops

**Statement.** An actual eight-variable subtype system has exact separating
paths `11 0^n 1` for `n>=1`; its shortest witness needs a pre-final loop, and
every separating path is terminal.

**Status / scope.** `WRITTEN PROOF + REPRO`; this refutes repeated-state deletion
and an infinite-extension-only completeness argument for actual outputs.

**Record.** [Full statement and proof](../notes/2026-09-04-denials-and-continuations.md).

<a id="c029"></a>

### C029 — Decision for infinitely extendable witnesses

**Statement.** For absorbing instances, existence of a witness admitting an
infinite safe continuation is decidable, including arbitrary pre-final loops,
using a finite periodic-suffix monitor.

**Status / scope.** `WRITTEN PROOF + REPRO`; `NO_INFINITE_EXTENSION` does not
mean unrestricted `NO`, because terminal witnesses remain possible.

**Record.** [Full statement and proof](../notes/2026-09-04-denials-and-continuations.md).

<a id="c030"></a>

### C030 — Terminal-final abstract instances are realizable

**Statement.** Every `k`-state binary terminal-final BorderAvoid instance has
an always-satisfiable normalized subtype realization on `2k+1` variables,
preserving exactly its witness words and budgets.

**Status / scope.** `WRITTEN PROOF + REPRO`; arbitrary flags and `Bad` are
allowed, and every accepting state must be terminal.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-realization.md).

<a id="c031"></a>

### C031 — Terminal-final decidability equivalence

**Statement.** Terminal-final BorderAvoid and normalized Problem 1.7 have
equivalent decidability through C030, C029, and the audited forward bridge.

**Status / scope.** `WRITTEN PROOF`; this is not a complexity equivalence or a
full converse for arbitrary BorderAvoid annotations.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-realization.md).

<a id="c032"></a>

### C032 — A nonregular actual terminal language

**Statement.** A nine-variable normalized system has exact terminal separating
language `0^m 1 0^(n+1) 1` for `n>=m>=0`, and this language is nonregular.

**Status / scope.** `WRITTEN PROOF + REPRO`; this rules out a finite automaton
recognizing all such witnesses, not a decision procedure for their existence.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-realization.md).

<a id="c033"></a>

### C033 — Presburger decision for fixed skeletons and flat terminal graphs

**Statement.** Fixed word skeletons with unbounded nonnegative exponents have
an exact Presburger translation; flat terminal candidate graphs have a finite
complete skeleton cover and hence a decision procedure.

**Status / scope.** `WRITTEN PROOF + REPRO`; practical solver caps retain
`UNKNOWN`, and the result does not cover nonflat terminal graphs.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-arithmetic.md).

<a id="c034"></a>

### C034 — Complete four-state terminal census

**Statement.** All normalized binary terminal-final instances with at most four
states are decided by exhaustive census; successful budget is at most two and
witness length at most four, both sharp.

**Status / scope.** `REPRO`; the finite census uses audited Python graph
emptiness and a written normalization argument, and gives no bound for larger
instances.

**Record.** [Full statement and proof](../notes/2026-09-05-four-state-terminal.md).

<a id="c035"></a>

### C035 — Nonflat edge support can be necessary

**Statement.** A six-state, two-flag terminal instance has exact witness
language `0 (0^r 1, r>=2)^+ 101`; every witness uses a nonflat edge support.

**Status / scope.** `WRITTEN PROOF + REPRO`; C030 gives a 13-variable subtype
realization. The result refutes flat edge-subautomata as a complete cover, not
richer bounded skeletons.

**Record.** [Full statement and proof](../notes/2026-09-05-nonflat-overlap.md).

<a id="c036"></a>

### C036 — Terminal suffix agreements cannot merge

**Statement.** Two agreeing suffix occurrences on a terminal accepted run
cannot merge at any aligned position; suffix-prefix chains have height at most
`k`.

**Status / scope.** `WRITTEN PROOF + REPRO`; terminal acceptance is essential,
and this gives no bound on suffix lengths or witness lengths.

**Record.** [Full statement and proof](../notes/2026-09-05-nonflat-overlap.md).

<a id="c037"></a>

### C037 — Last-flag overlap certificate

**Statement.** If the productive synchronized graph after the last flagged pair
is acyclic, an effective `H` makes `Witness` equal `Necessary(H,0)` on each
final slice.

**Status / scope.** `WRITTEN PROOF + REPRO`; `H` bounds shortest violation
detection, not the successful budget `B`. Cyclic residuals remain `UNKNOWN`.

**Record.** [Full statement and proof](../notes/2026-09-05-nonflat-overlap.md).

<a id="c038"></a>

### C038 — Terminal violations have bounded overlap exponent

**Statement.** For a terminal accepted run, a suffix violation with gap `d`
satisfies `floor((n-i)/d) <= k-1`; its periodic suffix has at most `k-1`
complete copies of the gap word, plus a prefix remainder.

**Status / scope.** `WRITTEN PROOF + REPRO`; the gap word can still be
arbitrarily long, and this is not a finite witness-length or decision bound.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-period-bound.md).

<a id="c039"></a>

### C039 — Forward-closed source-border bound

**Statement.** In a deterministic `n`-state terminal automaton with no positive
return to start `p`, if nonfinal target set `T` is forward closed before
terminal acceptance, a `T`-unbordered accepted word exists iff one exists of
length at most `6n+1`.

**Status / scope.** `WRITTEN PROOF + REPRO`; this is a written adaptation of
Anderson et al.'s theorem for the forward-closed class, not a general flag
theorem.

**Record.** [Full statement and proof](../notes/2026-09-05-source-border-anderson.md).

<a id="c040"></a>

### C040 — Source-wise impossibility and pruning certificate

**Statement.** Applying C039 to one source state's outgoing flags gives a
sound all-state impossibility/pruning certificate: proved-impossible states
may be added to `Bad` before rerunning C037, and the source-only
forward-closed class is decided exactly.

**Status / scope.** `WRITTEN PROOF + REPRO`; forward closure is required, and
resource caps preserve `UNKNOWN`.

**Record.** [Full statement and proof](../notes/2026-09-05-source-border-anderson.md).

<a id="c041"></a>

### C041 — Exact geometry of a word's sufficient budget

**Statement.** For a witness `w` of length `n`, `word_budget(w)` equals
`min_{1<=m<=n+1}(m-1+g_m)`, where `g_m` is the start gap from the earliest
occurrence of the terminal suffix of length `m` to its terminal copy for
`1<=m<=n`; the `m=n+1` term is the convention value `n`.

**Status / scope.** `WRITTEN PROOF` for the exact word-level identity.
The terminal `B<=k-2` candidate it originally reframed is now REFUTED; see
[Q002](conjectures/Q002.md) and the
[modular counterexample](../notes/2026-09-05-modular-synchronization.md).
That refutation does not refute this word-level identity.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-budget-geometry.md).

<a id="c042"></a>

### C042 — Source viability plus a residual cycle does not imply YES

**Statement.** A five-state terminal instance can satisfy every live
nonfinal state's own outgoing flags while the full multi-source instance is
exactly `NO`, certified by an empty `Necessary(2,0)` automaton.

**Status / scope.** `COUNTEREXAMPLE`; it refutes the source-only-viability
dichotomy for cyclic residuals. The exact instance and finite certificate are
in the linked record.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-budget-geometry.md).

<a id="c043"></a>

### C043 — Proper terminal violations have bounded fractional-power form

**Statement.** After boundary exclusions, every proper terminal violation has
the form `A(uv)^s u` with `1<=s<=k-1`, together with the stated flagged endpoint
and acceptance conditions.

**Status / scope.** `WRITTEN PROOF`; bounded checks are recorded in the linked
note. The factors `u` and `v` remain unbounded, so this gives no finite
automaton or decision procedure by itself.

**Record.** [Full statement and proof](../notes/2026-09-05-profile-and-fractional-power.md).

<a id="c044"></a>

### C044 — Budget bound equals agreement-profile domination

**Statement.** For each `k>=2`, the sharp terminal budget statement `TB(k)` is
equivalent to the agreement-profile statement `PD(k)`: every `k`-state
terminal DFA and every boundary-safe accepted word `w` have a boundary-safe
accepted replacement `v` with `A(v) subseteq A(w)` and budget at most `k-2`.

**Status / scope.** `WRITTEN PROOF` for the equivalence, not for either
universal bound. C034 establishes `TB(k)` and hence `PD(k)` for `k<=4`.
**Q002 is REFUTED:** the eight-state modular instance violates the `k-2`
budget and the corresponding profile-domination statement. See
[Q002](conjectures/Q002.md) and the
[counterexample](../notes/2026-09-05-modular-synchronization.md).
This does not refute the equivalence or claim failure for every individual
`k>4`. Earlier bounded searches remain historical evidence.

**Status correction (2026-09-09).** Replaces the stale larger-state OPEN
commentary. No new proof review or evidence-level promotion is claimed.

**Record.** [Full statement and proof](../notes/2026-09-05-profile-and-fractional-power.md).

<a id="c045"></a>

### C045 — Unbordered gap deletion is profile-safe

**Statement.** In a partial deterministic automaton, if an accepted word
`w=Xsys` ends in a terminal final, `s` is nonempty and unbordered, the state
after the first `s` equals the state before the terminal `s` (so `y` is a state
loop), and the shortened word `v=Xss` has a unique terminal suffix of length
`|s|+1`, then `v` is accepted, `A(v) subseteq A(w)`, and
`word_budget(v)<=|s|`.

**Status / scope.** `WRITTEN PROOF + REPRO` for this local theorem under
its three hypotheses. The uniqueness condition is essential.
**Q003 is REFUTED:** see [Q003](conjectures/Q003.md) and the
[modular counterexample](../notes/2026-09-05-modular-synchronization.md).
That refutation does not refute C045 or establish its hypotheses for arbitrary
witnesses; unconditional strict profile descent must not be inferred.

**Status correction (2026-09-09).** Replaces the stale conjecture commentary.
The local proof and its recorded evidence are unchanged. This is not a new
independent mathematical review or a full audit of every dependent use.

**Record.** [Full statement and proof](../notes/2026-09-05-unbordered-gap-normalization.md).

<a id="c067"></a>

### C067 — Single-source terminal existence reduces to word equations

**Statement.** Binary terminal BorderAvoid with at most one flagged source
state is decidable and in PSPACE. The source need not be initial and may
recur. Terminality makes each target's safe acceptance language prefix-free;
its unique accepted prefix yields an exact positive existential capture
formula. A first-to-last source deletion preserves witnesshood and reduces
existence to one source visit. The formula uses only concatenation equations
and explicit regular-language constraints, not a missing word-length bound.

**Status / scope.** `WRITTEN PROOF + REPRO`; independent mathematical review
pending; not Lean. The external dependency is Diekert--Gutierrez--Hagenah,
Theorem 4 for free monoids with involution, used in its involution-free
special case with all variables constrained to the binary alphabet. This is
not a PSPACE lower bound, not a decision for multiple recurrent sources, and
not a re-proof of the subtype bridge. Empty and diagonal flags, Bad states,
multiple terminal finals and source returns are included. The optional Z3
adapter is not the complete theoretical word-equation solver.

**Evidence.** [Exact construction, both directions and theorem transfer](../notes/2026-09-09-source-capture-word-equations.md),
[compiler](../experiments/source_capture.py), E043.
The single-source pumping route remains historical; this result bypasses its
new-border obligation rather than claiming that pump has been repaired.

<a id="c068"></a>

### C068 — Exact bounded-source-visit word-equation compilation

**Statement.** For a supplied sequence of flagged-source states, witness
existence with exactly that visit sequence reduces to a positive existential
word-equation formula with explicit regular constraints. Segment and suffix
variables retain one shared candidate word. Thus existence with at most a
supplied R source visits is decidable (in PSPACE when R is unary). A productive
graph with no cycle containing a source is a decidable special case, with
R at most the number of source states; unflagged components may be nonflat
and arbitrarily recurrent.

**Status / scope.** `WRITTEN PROOF + REPRO`; independent mathematical review
pending; not Lean. Counts are positions, not distinct states. There is no
proved computable visit bound for all positive instances (Q004), and a
terminating source-wise pruning iteration does not supply global completeness.
The compiler handles a supplied sequence; optional SMT resource limits remain
UNKNOWN. The implementation is not claimed to provide a complete practical
all-sequences or unrestricted solver.

**Evidence.** [Theorem, segment automata, limits and two-source counterexample](../notes/2026-09-09-source-capture-word-equations.md),
[compiler](../experiments/source_capture.py), E043.

<a id="c080"></a>

### C080 — Candidate unrestricted terminal decision by rank-query preimages

**Statement (proposed).** For every finite binary terminal instance with k
states, witness existence is equivalent to satisfaction of a finite existential
directed regular-path query with finite-colour guards on finitely many
two-vertex initial prefix graphs, obtained from a fixed finishing query by at
most k-2 promotion preimages. Consequently every positive instance has a witness
of length at most the explicit computable bound
`F(1)=0, F(k)=2(k+1)*prod_{j=1..k-2}(T_j+2)` with `T_0=k+10` and
`T_(j+1)=64k*T_j^(2T_j+2)`, and terminal BorderAvoid is decidable; through
C029/C031 the same would hold for normalized subtype entailment over arbitrary,
possibly infinite trees.

**Stages.** (1) terminal positive border depth at most k-1; (2) first depth
milestones are first returns of the preceding reference; (3) exact coloured
successor/KMP prefix-graph surgery for a first return, with a single entrance
from the old graph and no inverse edges; (4) promotion-preimage lemma: a whole
conjunction of path atoms compiles jointly, in both directions, to the old graph
through bounded portal diagrams and one shared generator per physical interval;
(5) grammar closure with clause weight at most `U_k(T)=64k*T^(2T+2)` and the
unwind to `F(k)`; (6) the C029/C031 semantic transfer.

**Status / scope.** `CANDIDATE`: `WRITTEN PROOF + AUDIT + REPRO`; not
established. `LEAN` (kernel-checked, no `sorry`, no custom axiom) for stages
1–3, for the pinned stage-4 statement with decidable satisfaction
([RankQuery.lean](../lean/Subtail/RankQuery.lean)), for the reverse half of
the Closure Lemma over any diagram enumeration (`closure_reverse` in
[RankQuerySound.lean](../lean/Subtail/RankQuerySound.lean) with the executable
compiler [RankQueryCompiler.lean](../lean/Subtail/RankQueryCompiler.lean)),
for the conditional stage-5 unwind and `T_h` recurrence
([RankQueryUnwind.lean](../lean/Subtail/RankQueryUnwind.lean)), and for the
stage-6 semantic foundation and executable normalized satisfiability
([CanonicalModel.lean](../lean/Subtail/CanonicalModel.lean),
[StackReachability.lean](../lean/Subtail/StackReachability.lean)). NOT
Lean-checked, hence `ClosureFor` and the decision remain unproved: the forward
direction (stage 4b: executable diagram enumerator and coverage), the
clause-weight bound and `F(k)` (stage 5), and the entailment decision of stage
6 (separating-address bound, `I_C`, absorption, C029/C031, composition). Two
separate AI-assisted audits, both informed by the author's argument, found no
gap in stages 1–5 and in the stage-6 bridge; neither is a human referee or a
blind derivation. Independent adversarial fixtures found no compiler
discrepancy; only one-atom unions and one zero-length two-atom union are
exhausted, other joint and higher-rank checks are certificate-guided or
work-capped. The capped generic driver returns UNKNOWN on recorded hard
fixtures, which is not negative evidence. No polynomial, elementary or
practical bound is claimed. A prior-work audit found no source supplying this
closure and requires comparison with the failed invariant of Schubert's
withdrawn 2021 Lemma 5.5 before any methodological-independence claim
([novelty matrix](../notes/prior-work/novelty-matrix.md)). The exact review
target is stage 4: Lemma 4 and Sections 5–7 of the candidate proof, Sections
3–5 of the closure note, now also readable as the pinned `ClosureFor`.
Problem 1.7's accepted status is unchanged by this record; the ID exists so
the candidate can be found, cited and reviewed.

**Evidence.** [Candidate proof](../notes/2026-09-15-candidate-rank-query-decision.md),
[closure proof and bound](../notes/2026-09-17-rank-query-closure-audit.md),
[closure review](../notes/2026-09-17-rank-query-independent-review.md),
[bridge review](../notes/2026-09-17-semantic-bridge-independent-review.md),
[compiler](../experiments/rank_preimage.py),
[compiler checks](../experiments/check_rank_preimage.py),
[separate fixed-reference oracle](../experiments/rank_frontier_oracle.py),
[results](../results/rank-preimage.json),
[review results](../results/rank-closure-review.json),
[candidate record](RANK_QUERY_CANDIDATE.md),
[compiler record](RANK_QUERY_COMPILER.md),
[prerequisites and failed quotients](RANK_ATTEMPT.md),
[referee brief](../notes/2026-09-18-closure-lemma-referee-brief.md),
[Lean statement readback](../notes/2026-09-18-lean-rank-query-statement.md),
[Lean compiler note](../notes/2026-09-18-lean-rank-compiler.md),
[adversarial fixtures](../notes/2026-09-18-closure-fixtures.md),
[prior-work dossier](../notes/prior-work/README.md).
Allocated 2026-09-18 by an integrator session (issue #25); the allocation is
navigation, not a review.

## Explicitly unestablished

The following are deliberately not accepted claims in this ledger:

- a converse from arbitrary BorderAvoid annotations to top-free subtype
  constraints;
- a computable bound on `B(I)` for SEP-derived instances;
- decidability, undecidability, or PSPACE membership for Problem 1.7;
- reproduction of the memo's original `analysis-2026` census.
