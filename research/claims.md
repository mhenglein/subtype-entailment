# Claims ledger

Index updated: 2026-09-19. Original C001-C020 review: 2026-09-04.
Later claims retain the evidence and review scope of their linked records.

This ledger gives stable IDs for claims about Problem 1.7 and its BorderAvoid
reduction. It is the shared index for notes, experiments, and future review.
Later continuation records are indexed in [Continued claim records](#continued-claim-records).

**Problem status:** [C081](#c081) is the complete Lean-checked executable
subtype entailment decision for finite bottom/product inputs over arbitrary,
possibly infinite trees. Its build, kernel/runtime audits and independent
semantic readback are recorded separately from finite native tests. The
explicit quantitative C080 bound remains a candidate. The memo's original
census has not been reproduced.

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

### C012 — The abstract budget criterion and its original open target

**Claim.** Under finite effective encodings, Theorem 8.9 reduces decidability
of abstract BorderAvoid to the existence of a computable upper bound on the
least successful budget `B(I)`. The memo and this review do not provide that
bound for unrestricted abstract BorderAvoid. The original review also left
Problem 1.7 open; the later [C081](#c081) now decides that subtype problem
through a different checked finite algorithm.

**Scope.** Abstract BorderAvoid instances with an effective finite encoding,
then the narrower semantic top-free subtype problem.

**Status.** `AUDIT + OPEN` — the equivalence proof was inspected, but the
unrestricted abstract bound and the full top-free converse remain open. This
status is not a remaining assumption of C081. Decidability for terminal and
absorbing instances already implies some computable existential witness bound
by finite-instance classification; it does not establish C080's specific F.

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

**Separate Lean construction (2026-09-19).** `SummaryAutomaton` now proves
exact same-word equivalence with canonical separation and arbitrary-tree
non-entailment equivalence, and derives strong absorption for every physical
state. It uses two summaries and an exact denial-danger predicate. This is
not a verification of the older Python source. Pinned build, kernel,
complete dependency audit, separate statement review and native differential
passed; [readback](../notes/2026-09-19-subtype-summary-bridge.md).

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

**Status / scope.** `LEAN` + independent source readback + native reproduction
(2026-09-19). `InfiniteDecision.infiniteWitnessCheck_correct` proves for every
`I : Instance k` that `Absorbing I` implies
`infiniteWitnessCheck I = true iff AbsorbingTerminal.InfWitness I`.
The total executable uses checked bounded-cycle enumeration and complete
finite reverse-graph search; the prefix length is not bounded in advance.
Both monitor language directions, nonprimitive rotation equality, concrete
periodic traces and finite original-witness extraction are proved. No
unproved witness bound or monitor/reduction hypothesis remains.

The original Witness, strong absorption, Bad states, partial transitions,
ordered/diagonal flags and empty prefix are unchanged. A false result does
not exclude terminal witnesses. This theorem does not itself assemble the
expression-level subtype decision or certify a quantitative U/F bound.
Pinned build, whole-library kernel replay, declaration/runtime audits and
independent semantic review are recorded in the completion note. Finite
native checks are reproduction evidence, separate from the all-state proof.

**Record.** [Original statement and proof](../notes/2026-09-04-denials-and-continuations.md);
[earlier cycle-only route and failed shortcuts](../notes/2026-09-19-c029-cycle-monitor.md);
[complete executable proof, construction and validation](../notes/2026-09-19-c029-completion.md);
[native independent checks](../results/infinite-decision.json).


**Equivalent incremental implementation (September 20).**
`InfiniteDecisionLazy.infiniteWitnessCheckLazy_eq` proves equality with this
Boolean on every finite instance, without an absorption hypothesis. It streams
the same bounded cycle words and rejects an unsafe initial state before the
scan. The semantic correctness theorem still requires `Absorbing I`.
[Ordinary argument, source review and native checks](../notes/2026-09-20-raw-backend-readback.md).
No stronger witness bound or complexity result follows.

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

**Status / scope.** `WRITTEN PROOF` for the whole decidability equivalence;
this is not a complexity equivalence or a full converse for arbitrary
BorderAvoid annotations. The safe-terminal-restriction subclaim is separately
`LEAN` (2026-09-19): `AbsorbingTerminal.c031` proves, under strong absorption,
`(exists w, Witness I w) iff InfWitness I or exists w, Witness (terminalize I) w`.
InfWitness contains an original witness, safe finite stem and nonempty safe
cycle. The finite graph proof and executable terminalization use original
finals and prune unsafe edges before the sink test. The composed subtype split
has an exact terminal Boolean and an InfWitness proposition. The later
[C029](#c029) completion now supplies a checked executable decision for that
infinite branch. [C081](#c081) now composes those decisions and normalization
into the full entailment Boolean. This C031 subclaim does not itself certify
the converse C030 realization or its budget-preservation statement.

**Record.** [Full statement and proof](../notes/2026-09-05-terminal-realization.md);
[checked subclaim and semantic readback](../notes/2026-09-19-subtype-summary-bridge.md).

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

**September 20 correction.** The old universal clause-weight conjunct for
`preimage I RankQueryCoverage.budget` is **REFUTED (LEAN + independent readback)**
by `RankQueryWeightCounterexample.terminal_counterexample`. The bundle below
is not an established quantitative theorem. The original F alone and an
existentially chosen smaller compiler remain open. Semantic preimage closure,
terminal decidability and C081 remain checked and do not use the false conjunct.
The larger replacement bound is recorded separately as [C082](#c082).
[Exact scope, provenance and dependency correction](../notes/2026-09-20-post-c081-quantitative-integration.md).
The original proposed statement and discovery history follow.

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
([RankQueryUnwind.lean](../lean/Subtail/RankQueryUnwind.lean)); also for the
semantic-only promotion unwind and its concrete compiler corollary, which
require no clause-weight hypothesis
([RankQuerySemanticUnwind.lean](../lean/Subtail/RankQuerySemanticUnwind.lean),
[workbench pilot and separate statement readback](../notes/2026-09-19-wb-semantic-pilot.md)); and for the
stage-6 semantic foundation and executable normalized satisfiability
([CanonicalModel.lean](../lean/Subtail/CanonicalModel.lean),
[StackReachability.lean](../lean/Subtail/StackReachability.lean)). Also
Lean-checked (2026-09-19): the stage-4b enumerator and `coverage :
DiagramCoverage I budget`, hence `closure_iff`, both directions of the semantic conjunct of
`ClosureFor I (preimage I budget)` for every safe reference
([RankQueryCoverage.lean](../lean/Subtail/RankQueryCoverage.lean), author
readback only). On September 19 the full terminal decision subclaim is also
`LEAN`: `RankQueryDecision.terminalWitnessCheck_correct` proves
`TerminalFinals I -> (terminalWitnessCheck I = true ↔ ∃ w, Witness I w)`.
`rankDecisionStatement` instantiates the pinned schema with
`preimage I RankQueryCoverage.budget`. Witness reversal, safe milestone chains,
finishing and executable boundary tests are included. This direct decision
does not require the numerical weight contract.
[Assembly, semantic readback and validation](../notes/2026-09-19-terminal-rank-decision.md).

Also `LEAN` (2026-09-19): the explicit finite `SummaryAutomaton` instance,
ordered-cut/forced-root/prefix-denial characterization, exact same-word
`witness_iff_separation`, arbitrary-tree `not_entails_iff_witness`, and
all-state strong absorption. The executable construction retains UNSAT as a
Bad bit. [Bridge proof and independent readback](../notes/2026-09-19-subtype-summary-bridge.md).

The original clause-weight conjunct of `ClosureFor` for the concrete compiler
is now refuted, as recorded in the correction above. The original F alone
remains open. [C081](#c081) supplies the complete qualitative stage-6 theorem
without those numerical claims. The reviewed PR #48 counterexample and larger
replacement are integrated separately as [C082](#c082); PR #47 preserves the
ordinary discovery history. The absorbing safe-cycle/terminal split
of C031 is now `LEAN`, as is the composed exact normalized non-entailment split
in `SubtypeTerminalBridge`. The later [C029](#c029) theorem supplies a checked
executable decision for its infinite branch. The original bundled statement is refuted at its concrete weight conjunct;
its original F remains a candidate, while terminal decidability is checked. Two
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
This historical quantitative bundle is not accepted; C081 records the
accepted qualitative decision and C082 the corrected quantitative result. Owner decision 2026-09-19: no
external human referee will be commissioned; acceptance requires the
kernel-checked end-to-end decision theorem plus cross-session statement
readback (#33). After the earlier pause, the owner resumed a bounded workbench
and proof pilot on 2026-09-19 (#30, #37). Its first result was semantic-only unwind; the subsequent #30 assembly proves
terminal decision. The subsequent C081 completes Problem 1.7's decision.
Q004 follows as an ordinary computability corollary of the terminal decision;
its explicit construction and review are recorded separately. C080's specific
F(k) remains unresolved; its old universal concrete-clause weight estimate is
refuted. C082 supplies a separate sufficient recurrence.

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

<a id="c081"></a>

### C081 — Complete finite-expression subtype entailment decision

**Statement.** For every natural n, finite input list `G : Input n` and finite
expressions `s t : Expr n` over variables `Fin n`, bottom and covariant binary
product, the total executable Boolean satisfies

```lean
Subtail.EntailmentDecision.entailsCheck G s t = true ↔
  Subtail.ExpressionNormalization.ExprEntails G s t
```

`ExprEntails` quantifies over all valuations into arbitrary prefix-closed
trees, including infinite and nonregular ones. The query is not a premise.
No SAT, finite/regular-model, witness-bound, U/F, C030 or absorption assumption
is required from the caller. The finite named-set/variable-query form of
Problem 1.7 embeds in this syntax by finite indexing and listing premises.

**Construction and proof.** Exact expression normalization preserves both
model extension/restriction and query meanings. For the same normalized
summary instance I, the Boolean is the negation of
`infiniteWitnessCheck I || terminalWitnessCheck (terminalize I)`.
Strong absorption of I is proved; terminalization preserves original finals
and removes unsafe edges. C029 decides the first branch, and the checked
terminal algorithm decides the second. Reflexivity, a listed premise,
UNSAT-vacuity and a root countermodel are separately proved early returns.
An unsuccessful root test invokes the complete backend; it is not an answer.

**Status / scope.** `LEAN + AUDIT`, with supplementary native regressions.
The source is pinned at `9f7d57cbd695a68dd52a69dc81b8446bd7c85d9e`.
The default build, full kernel replay and all 91 normalization/final named
transitive dependency closures pass; the 39 non-theorems use no classical
choice. Independent source readback found no semantic blocker. Prior chain
reviews and source provenance are preserved; this is not human peer review.

**Ordinary consequence.** Q004 is proved by effective finite enumeration of
labelled terminal k-state instances, complete terminal classification and
word enumeration on each positive instance. Taking the maximum first-witness
length plus one gives a total computable source-visit bound. This corollary
is ordinary mathematics, not a new Lean declaration or the proposed F(k).

**Evidence.** [Executable and theorem](../lean/Subtail/EntailmentDecision.lean),
[complete proof and exact validation record](../notes/2026-09-19-entailment-decision.md),
[independent semantic readback](../notes/2026-09-19-entailment-decision-independent-readback.md),
[normalization model transfer](../lean/Subtail/ExpressionNormalization.lean),
[dependency audit](../scripts/check_entailment_decision.py),
[E052 native coverage and limits](../experiments/README.md#e052),
[Q004 corollary](conjectures/Q004.md).

**Limits.** Native test caps remain UNKNOWN; they are not cutoffs in the
formal algorithm. The exhaustive backend is not a practical solver, and no
complexity or novelty claim is made. C080's quantitative estimates, C030's
separate converse certification and the unrestricted nonabsorbing abstract
BorderAvoid problem are not proved by this theorem. Other constructors and
finite-tree entailment are outside its semantics.

**Additive execution improvement (September 20).** The optional
`TerminalDecisionLazy.entailsCheckLazy_eq` proves unconditional equality to
the original full-input Boolean; `entailsCheckLazy_correct` retains the exact
C081 semantics. The global safe-reference gate skips a query construction only
when its candidate scan cannot succeed. The old core is unchanged.
[Proof, independent boundary review and native evidence](../notes/2026-09-20-c081-solver.md)
record build/kernel/runtime checks and E054. This is an evaluation improvement,
not a stronger decision theorem. The capped Python interface and certificate
checker have separate trust boundaries; remaining timeouts stay UNKNOWN.


**Equivalent raw-backend refinement (September 20).**
`InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy_eq` replaces only the
infinite-witness Boolean, leaving the summary construction and terminal branch
unchanged. `EntailmentPrepared.entailsCheck_correct` composes it into the
existing arbitrary-tree endpoint with no new assumption. Raw measurements
invoke the raw function directly; they do not use frontend shortcuts.
[Proof and execution boundary](../notes/2026-09-20-raw-backend-readback.md).

**Equivalent cached summary construction (September 20).**
`SummaryInstanceCached.summaryInstance_eq` proves literal equality of the
complete physical `Instance`, including unreachable states and every ordered
flag. It requires the exact constraint System and a correct cache.
`EntailmentPrepared.rawNormalizedEntailsCheck` supplies both internally;
its raw and original-expression correctness theorems add no caller hypothesis.
The refinement reuses relation tables and decoded states, retaining the
reference state enumeration and complete decisions.
[Ordinary argument, checked declarations and bounded measurements](../notes/2026-09-20-raw-summary-readback.md).
This is an implementation refinement of C081, not a new bound or signature.

<a id="c082"></a>

### C082 — Corrected compiler weight and terminal witness bound

**Statement.** For the unchanged concrete compiler and coverage budget, every
emitted clause from input weight at most T has weight at most
`Uhat_k(T)=64*k*T^(6*T^2+2)`. Put `T_0=k+10` and
`T_(j+1)=Uhat_k(T_j)`. For every `I : Instance k` with `TerminalFinals I`,

```text
(exists w, Witness I w) iff
(exists w, Witness I w and length(w) <= Fhat(k)),
Fhat(1)=0,
Fhat(k)=2*(k+1)*product_(j=1..k-2)(T_j+2) for k>=2.
```

`Witness` retains partial transitions, Bad states, ordered/diagonal flags,
empty suffixes and the empty word. No old `ClosureFor`, SAT, supplied bound or
restricted observer hypothesis occurs. The runtime value at k=0 is 2;
`Instance 0` is uninhabited, so no zero-state input is omitted.

**Proof and status.** `LEAN + independent source readback`. The exact endpoints
are `RankQueryWeightBound.preimage_clause_weight_le` and
`RankQueryLengthBound.terminal_witness_bound_iff`. The structural compiler
bound counts the whole conjunction. Bounded joint interval reconstruction
retains shared assignments and all observations, then promotion multiplies
the length budget. The original qualitative decision supplies the finishing
case; there is no circular use of this new length bound in that decision.

**Evidence.** [Detailed ordinary proof/readback and fresh validation](../notes/2026-09-20-post-c081-quantitative-integration.md),
[independent review](../notes/2026-09-20-c080-quantitative-independent-readback.md),
[weight source](../lean/Subtail/RankQueryWeightBound.lean),
[length source](../lean/Subtail/RankQueryLengthBound.lean),
[old-contract counterexample](../lean/Subtail/RankQueryWeightCounterexample.lean),
[combined build/kernel/runtime audit](../results/rank-weight-integration.json).
All 87 new declaration audits and the unchanged default core pass at
`7525724b3c86b6a9dbe0a7f62b062a9b8697a97c`; runtime definitions are choice-free.

**Limits.** The old C080 U is not silently redefined and its original F alone
is not refuted. This is not an original-input time bound or practical algorithm.
Q004 obtains the ordinary explicit source-visit bound `R(k)=Fhat(k)+1` for
k>=1, with R(0)=0; that corollary is not a new Lean declaration. No result for
explicit top, new constructor signatures or finite-tree semantics follows.

<a id="c083"></a>

### C083 — Directed reachability lower bound for exact entailment

**Statement.** For a finite directed graph with distinguished vertices s,t,
encode every edge u->v by the variable inequality x_u<=x_v and query x_s<=x_t.
There is a path s->t (including length zero) iff this input entails the query,
separately under arbitrary, regular and finite bottom/product tree valuations.
For the standard explicit-vertex graph encoding this is a deterministic
logspace many-one reduction. Hence the full C081 problem is NL-hard, already
on variable-only inputs.

**Proof and status.** Ordinary proof plus independent read-only review.
Reachability implies the query by transitivity/reflexivity. If t is unreachable,
assign the finite root-only product tree to vertices reachable from s, and
bottom to the others. Every edge constraint holds, while the query fails at
address []. Computing reachability is only part of the existence proof for the
countervaluation, not the reduction. The imported PATH NL-completeness theorem
uses the same logspace-reduction convention.

**Evidence.** [Full construction, primary source, encoding and independent review](../notes/2026-09-20-reachability-lower-bound.md).

**Limits.** This is an inherited elementary lower bound, not a novelty claim.
No NL membership, PSPACE-hardness, superpolynomial runtime lower bound or new
Lean declaration is claimed. The finite/regular equivalence here concerns only
the variable-only sublanguage; it does not transfer the general C081 theorem
to finite-tree entailment.

<a id="c084"></a>

### C084 — Checked finite-graph countermodel certificates

**Statement.** For every n,v, original finite `G : Input n`, expressions
`s t : Expr n`, and `c : RegularTreeCertificate.Certificate n v`,

```lean
RegularTreeCertificate.check G s t c = true →
  ¬ ExpressionNormalization.ExprEntails G s t
```

The stronger `check_sound` conclusion gives `ExprModels G (valuation c)`,
membership of the supplied word in the left expression, and its absence from
the right expression. A certificate contains a finite bottom/product graph,
variable roots, expression-node map, finite Boolean relation and word. Cyclic
graphs denote regular infinite trees inside the unchanged arbitrary-tree
semantics. The query is not inserted as a premise.

**Construction.** `simulationCheck` checks every true pair in the finite
relation. Induction on addresses proves tree inclusion for related roots.
`embedCheck` recursively checks every original premise/query expression;
`embed_eval` identifies each checked node with the expression's tree value.
The word test gives the counterexample. No producer normalization, witness
bound, SAT assumption or unchecked proposition occurs in the certificate.
`below_iff_simulation` separately characterizes graph inclusion by existence
of a proposition-valued locally closed relation; it is not an extractor.

**Status and evidence.** Checked Lean module with independent semantic
readback and native/instance-proof regression evidence. Source originated at
`7a3bcd3148d7b0c2e706c8e21593ab0bcc9d4dc3` and is integrated unchanged.
[Source](../lean/Subtail/RegularTreeCertificate.lean),
[ordinary construction and exact validation record](../notes/2026-09-20-regular-countermodels.md),
[separate readback](../notes/2026-09-20-regular-countermodels-readback.md),
[reproduction driver](../scripts/check_regular_certificate.py).

**Limits.** The complete canonical NFA extractor and its termination argument
are ordinary reviewed Python/mathematics, not a Lean-verified extraction
function. `--verify-certificate` generates a particular non-entailment theorem
using `check_not_entails ... (by decide)` and reports VERIFIED only after the
whole Lean process succeeds. JSON parsing and source emission remain outside
the kernel boundary; resource limits can yield UNKNOWN. No new finite-tree,
explicit-top, complexity or novelty conclusion is claimed.

<a id="c085"></a>

### C085 — Finite-tree entailment by a consuming-cycle test

**Statement.** For every normalized bottom/product constraint list C and query
variables a,b, let Growth(C) mean that the reverse-pop epsilon NFA has a cycle
containing a letter edge. Its states are the controls, epsilon edges are
balanced reverse-system pairs, and labelled edges are reverse-system pops.
Then

```text
FiniteEntails(C,a,b) iff Growth(C) or Entails(C,a,b).
FiniteSatisfiable(C) iff not Growth(C) and Satisfiable(C).
```

These are unconditional ordinary theorems, with exact finite computation of
Growth. Every consuming cycle contains an edge reversing a push into a forced
product root, so its repetition excludes finite models. Without such a cycle,
reverse-pop words have length less than the number n of controls. A canonical
closure seeded at words of maximum length d then has height at most n+d.
Finite-valued definitional normalization transfers the result to original
finite expressions. C081 supplies the arbitrary-tree decision in the second
branch. The theorem does not identify every arbitrary model with a finite one.

**Status.** `LEAN` for the total executable finite-expression decision:

```lean
FiniteTreeDecision.entailsCheck G s t = true ↔ FiniteExprEntails G s t
```

No supplied classification, word bound, satisfiability or regularity hypothesis
remains. `growthCheck_correct` connects the cached Boolean to an actual
reverse-pop return word. A positive test supplies a forced nonempty loop;
a negative test excludes all nonempty loops. `PopAcyclic` then proves every
consumed word has length less than the number of controls, discharging the
uniform-bound hypothesis below. The separate normalized satisfiability
equivalence above retains its independently reviewed `WRITTEN PROOF + REPRO`
status; this update does not add a separate finite-SAT Boolean theorem.

The earlier checked semantic components in `FiniteTreeReduction` remain:

- `closureBounded_iff_noHot`: for any finite seed list in a finite pushdown
  system, its full reachability closure has bounded word lengths iff no
  reached control has an unbounded reverse-pop language.
- `canonicalFinite_iff_noHot`: the same equivalence for canonical tree values.
- `forced_reverse_pop_loop_noFiniteModel`: a **supplied** nonempty reverse-Pop
  loop at a **supplied forced root** excludes finite satisfiability.
- `finiteEntails_iff_entails_of_uniform_reverse_pop`: a **supplied global
  reverse-Pop length bound** implies finite and arbitrary entailment agree.
- `normalize_finite_entails_iff`: finite-expression entailment is equivalent
  to finite entailment of the existing normalized input.

`FiniteTree` means a common product-address length bound. On binary trees this
is equivalent to a finite product-node set. `Hot` in Lean negates a bound
uniform over initial controls; because there are finitely many controls, this
agrees with infiniteness of at least one language L(q,m).

**Evidence.** [Ordinary proof and finite construction](../notes/2026-09-20-finite-tree-reduction.md),
[semantic/source readback](../notes/2026-09-20-finite-tree-readback.md),
[Lean module](../lean/Subtail/FiniteTreeReduction.lean),
[build/kernel/runtime/CLI driver](../scripts/check_finite_tree_reduction.py),
[receipt](../results/finite-trees.json), [E056](../experiments/README.md#e056).
The CLI's `--finite-trees` branch exposes vacuity and checks extracted graphs
for cycles reachable from original variable roots. Ordinary and Lean evidence
remain separate in the receipt.

The later [executable bridge](../lean/Subtail/FiniteTreeDecision.lean),
[acyclic path bound](../lean/Subtail/PopAcyclic.lean),
[independent readback](../notes/2026-09-20-finite-tree-decision-readback.md),
[new checker](../scripts/check_finite_tree_decision.py) and
[E057 receipt](../results/finite-tree-decision.json) supersede the earlier
classifier gap. The CLI now uses the Lean naming construction and decision;
the separate Python growth implementation is diagnostic only.

The [paper's Theorem 1.2 and Section 13](../paper/manuscript.md#13-entailment-over-finite-trees)
now present the full ordinary argument. The [declaration map](../paper/lean-map.md)
preserves both proof revisions, and the [revision readback](../notes/2026-09-20-finite-paper-readback.md)
records the checked correspondence and example. The [finite literature review](../notes/prior-work/finite-tree-comparison-2026-09-20.md)
does not change this claim's mathematical status or establish novelty.

**Limits.** JSON parsing/emission and countermodel extraction remain Python;
the latter's DAG normalization is separate from Lean naming. The C084 instance
certificate still proves arbitrary non-entailment; the graph-finiteness check
is ordinary Python. Caps remain UNKNOWN. The seed-dependent height bound is
not a new global shortest-witness bound. Explicit top, new constructor labels,
variance, tight complexity and novelty remain separate obligations.

## Explicitly unestablished

The following are deliberately not accepted claims in this ledger:

- a converse from arbitrary BorderAvoid annotations to top-free subtype
  constraints;
- the original C080 F or a practical complexity bound (the old concrete U
  is refuted; C082 proves a different sufficient bound);
- PSPACE membership for Problem 1.7;
- reproduction of the memo's original `analysis-2026` census.
