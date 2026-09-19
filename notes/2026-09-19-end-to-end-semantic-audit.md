# End-to-end semantic audit: exact normalized split, not yet a full executable decision

Date: 2026-09-19.
Actor/session: ChatGPT `end-to-end-semantic-audit-20260919`, independent source reviewer; subsequent documentation publication explicitly requested by Marcus.
Related workstreams: A010, A013, A017, A018. Related claims: C029, C030, C031, C080. Review #33; semantic bridge #31; parent #34; coordination #37.

**Evidence status: independent source/statement inspection and ordinary mathematical readback. Not a fresh Lean build, kernel replay, axiom audit, regression run, complete low-level compiler reproof, or original-PDF page-by-page verification. No scientific claim is promoted by this note.**

## 0. Verdict, revisions, and review limitations

The inspected components compose to the exact normalized non-entailment split below. I found no additional missing hypothesis in the composition of that split. Its semantics retain arbitrary, possibly infinite trees, unsatisfiable inputs, ordered flags, every-prefix safety, diagonal comparisons, and empty witnesses.

They do **not yet** provide an end-to-end executable decision for the full finite input language of Problem 1.7. The executable infinite-branch theorem, finite-expression normalization, and final composition are substantive remaining obligations at the inspected snapshot. This is a missing-proof-and-integration finding, not a counterexample to the proposed approach.

### Revision provenance

- Detailed source inspection: [`064fc7306b679bf607b91e7d8de259823f200c62`](https://github.com/mhenglein/subtail/commit/064fc7306b679bf607b91e7d8de259823f200c62), 2026-09-19 13:22:38 UTC, "Record checked subtype bridge and remaining infinite branch (#31, #37)".
- Final audit snapshot and documentation branch base: [`e1e8f635f0374d5c8112c8ee25c4220fc10198be`](https://github.com/mhenglein/subtail/commit/e1e8f635f0374d5c8112c8ee25c4220fc10198be), 2026-09-19 13:51:26 UTC, merge of the structured literature review.
- The [comparison](https://github.com/mhenglein/subtail/compare/064fc7306b679bf607b91e7d8de259823f200c62...e1e8f635f0374d5c8112c8ee25c4220fc10198be) was inspected: intervening changes were restricted to prior-work documentation/tooling. No audited Lean or decision-runtime source changed. STATE and SubtypeTerminalBridge were reread at e1e8f635; the mathematical decision boundary was unchanged.
- The repository reports combined build/kernel/dependency/native validation at parent checkpoint `85a9e812544e1fb055f7fc2f5f8beb157ed33a0d`. That is prior recorded evidence, not execution performed by this reviewer. See the pinned [bridge validation record][bridge-note].

The original request was read-only. No file edit or GitHub post was part of the initial mathematical audit. The owner then explicitly requested preservation of all findings on GitHub. This publication owns only this new note and its review-branch/PR handoff; it does not alter proofs, definitions, shared ledgers, toolchain, or other workers' branches.

### What was and was not checked

Inspected: the repository's original-problem transcription, STATE and relevant claims, TreeSemantics, Basic, CanonicalModel, CanonicalReachability, StackSummary, StackReachability, SummaryBridge, SummaryAutomaton, AbsorbingTerminal, SubtypeTerminalBridge, RankQueryDecision, and the critical terminal-rank/reversal/query-closure interfaces. Also inspected the existing Python infinite-extension implementation and its safe-extension dependencies. The terminal dependency review followed relevant definitions, code excerpts, and exact theorem interfaces; it did not independently reconstruct every lemma of the large coverage/reconstruction development.

Not executed by this reviewer: Lean build, leanchecker, `#print axioms`, the dependency-audit scripts, native regressions, the Python continuation suite, or performance benchmarks. No statement below that a theorem is "discharged in source" means those checks were freshly run.

Original-source limitation: the PDF's repository metadata was available, but readable PDF bytes were not obtained through the attempted routes. This review used the pinned [problem transcription][problem] and [initial semantic reconstruction][initial-review], not a fresh page-by-page comparison with `papers/sep-topfree.pdf`. The recorded PDF Git blob is `f5ff7db92590612a8d522fbdcd05257752ea082d`; the [paper provenance record][papers] supplies its historical checksum. Exact fidelity of the transcription to the original PDF remains an inherited dependency of this audit. This is not a request to recover the retired analysis-2026 archive.

The reviewer inherited the requested checkpoint and existing route context and read author arguments while checking interfaces. This was not a blind derivation, an external human referee report, or an exhaustive compiler audit.

## 1. Dependency map

Let `I := SummaryAutomaton.summaryInstance C alpha beta`.

```text
Original finite bottom/product constraint syntax
    |
    | REMAINING: executable normalization and conservative model transfer
    v
C : List (TreeSemantics.Constraint n), alpha beta : Fin n
    |
    | TreeSemantics: arbitrary prefix-closed product-node sets
    |               universal quantification over satisfying valuations
    v
not Entails C alpha beta
    |
    | CanonicalModel.not_entails_iff_canonical
    | CanonicalReachability.not_entails_iff_exists_check
    v
exists w, separationCheck C alpha beta w = true
    |
    | SummaryBridge: forced-root, ordered-cut, every-prefix denial equivalences
    | SummaryAutomaton.witness_iff_separation
    v
exists w, Witness I w
    |
    | SubtypeTerminalBridge.summary_absorbing supplies Absorbing I
    | AbsorbingTerminal.c031
    v
InfWitness I OR exists w, Witness (terminalize I) w
    |
    | terminalize_terminal supplies TerminalFinals (terminalize I)
    | RankQueryDecision.terminalWitnessCheck_correct
    v
InfWitness I OR terminalWitnessCheck (terminalize I) = true
    |
    | REMAINING: total executable infiniteWitnessCheck, exact InfWitness theorem
    v
Executable normalized non-entailment / entailment decision
    |
    | REMAINING: final composition with normalization and its model theorem
    v
Executable decision for the original finite input language
```

The canonical and summary equivalences have no external satisfiability, finite-model, regular-model, stack-height, or witness-length premise. The wrapper supplies absorption and terminality through the concrete construction. See [canonical semantics][canonical], [canonical checks][canonical-checks], [ordered-cut bridge][cuts], and the [final wrapper][wrapper].

The terminal backend has a separate dependency chain:

```text
Original Witness
  -> safe reversed reference
  -> rank bound at EVERY reversed prefix, using terminal finals
  -> bounded number of labelled first-return promotions
  -> finishing-query satisfaction

Concrete finite diagram enumeration
  + RankQueryCoverage.coverage
  + compiler reconstruction/soundness
  -> semantic preimage equivalence
  -> RankQuerySemanticUnwind.sat_promote_preimage_iff

Finite query satisfaction checker
  + both directions above
  -> terminalWitnessCheck_correct
```

This is the concrete semantic-closure route. It does not invoke the unresolved quantitative conjunct of `ClosureFor`. Sources: [reversal][reversal], [terminal rank][rank], [coverage][coverage], [semantic unwind][unwind], [decision][decision].

## 2. Obligation ledger at the inspected revision

"Discharged in source" below means an explicit theorem is supplied and the relevant caller hypotheses are accounted for. It does not mean this reviewer reran machine verification.

| Obligation | Status | Declaration and precise boundary |
|---|---|---|
| Bottom and one ordered covariant binary product over arbitrary trees | Discharged in source | `Tree`, `bottom`, `product`, `Below`, diagram/domain correspondence; no finite/regular/decidable-membership restriction. |
| Universal entailment, including inconsistent constraints | Discharged in source | `Entails`, `unsatisfiable_entails`, unconditional canonical reduction. |
| Arbitrary finite expression syntax to four normalized forms | Remaining | No integrated total normalizer with model extension, model restriction, and query preservation. |
| Exact unbounded-stack propagation and normalized satisfiability | Discharged in source | `reachesCheck_correct`, `controlReachCheck_correct`, `CanonicalReachability.satCheck_correct`; no stack cutoff. |
| Same-word ordered-cut summary reduction | Discharged in source | `prefix_reaches_iff_cut`, `witness_iff_separation`, `not_entails_iff_witness`. |
| Every-prefix safety, diagonal/empty comparisons, empty witness | Discharged in source | Literal `Basic.Witness`, `witnessCheck_correct`, and bridge preservation. |
| Strong absorption for constructed summaries | Discharged in source | `summary_absorbs` includes all physical states and all incoming sources. |
| Safe terminalization and cycle/sink split | Discharged in source | `AbsorbingTerminal.c031` assumes `Absorbing`; `terminalize_terminal` is unconditional. |
| Whole-query semantic preimage coverage | Discharged in source; interface reviewed, not exhaustive low-level reproof | Concrete `coverage` and `closure_iff`; one extension satisfies the query; physical interval generation is shared. |
| Total terminal witness decision | Discharged in source | `terminalWitnessCheck_correct` requires `TerminalFinals`; the wrapper supplies it for `terminalize I`. |
| C029 decision for exact `InfWitness` | Remaining as executable Lean obligation | Written argument/Python implementation exist; no integrated total Boolean correctness theorem at this checkpoint. |
| Final total Boolean equivalent to original entailment | Remaining | Current endpoint is an equivalence containing `InfWitness : Prop`. |
| Advertised quantitative U/F bounds | Remaining, not a dependency of the direct terminal decision | The stronger weight contract is separate from semantic closure. |
| C030 converse realization | Separate scope | Useful for broader equivalence/hardness; not needed to finish the forward subtype-decision route. |
| Fresh build/kernel/axiom/regression execution by this reviewer | NOT RUN | Repository-reported validation remains separate provenance. |
| Fresh original-PDF fidelity check by this reviewer | NOT COMPLETED | Problem transcription and prior source audits were read instead. |

Pinned status sources: [STATE][state], [claims][claims], [wrapper][wrapper], [bridge record][bridge-note]. The stronger ledger C031 claim and the theorem named `AbsorbingTerminal.c031` have different scopes; see F8 below.

## 3. Findings with exact declarations and consequences

### F1. The normalized semantics genuinely quantify over arbitrary trees

`TreeSemantics.Tree` contains `nodes : Word -> Prop` and a prefix-closure proof. It requires neither a finite set, a regular language, a computable presentation, nor decidable membership. `Valuation n` assigns such a tree to each variable; `Entails C alpha beta` universally quantifies over all valuations satisfying `Models C`.

The interpretation of product inserts a product root and prefixes the operands' product addresses by the corresponding binary directions. The diagram/domain theorems retain an actual bottom root when the product-node set is empty. The empty set is not an absent tree. The full infinite product tree is a greatest semantic element; allowing it does not add a top constructor to the input language. Source: [TreeSemantics][trees].

The canonical argument does not replace universal entailment by checking only the unseeded least model. For each candidate address `w`, `CanonicalModel.pathSeeds` includes every prefix of `w` at `alpha`, together with every forced root. `derived_sound` and `canonical_least` relate this closure to every original model. `not_entails_iff_canonical` gives the exact existential-address characterization.

A finite separating address does not imply a finite witnessing valuation. The source includes `lower_self_zero_spine` and `lower_self_has_arbitrarily_deep_nodes` as explicit semantic checks of recursively forced unbounded depth. Source: [CanonicalModel][canonical].

**Consequence:** no finite-tree or regular-tree weakening was found in the normalized chain. The theorem's normalized input type nevertheless does not supply the separate translation from arbitrary finite compound expressions.

### F2. Unsatisfiability is explicit, not a hidden premise

`CanonicalReachability.satCheck_correct` establishes:

```text
satCheck C = true <-> Satisfiable C
```

The summary annotation is:

```text
Bad(B,A) = not satCheck C OR B intersects Danger.
```

`Danger` is defined by arbitrary-word reverse Pop reachability from denied controls and decided through finite control-graph reachability. It is not an unexplained bounded approximation. Sources: [canonical checks][canonical-checks], [SummaryBridge][cuts], [SummaryAutomaton][summary].

For inconsistent `C`, every summary state is Bad, including the initial state. Therefore no word is a witness, including the empty word, in agreement with vacuous entailment.

The exact intermediate theorem is `SummaryBridge.avoids_iff`:

```text
AvoidsDenials C (pathSeeds C alpha w)
  <-> Satisfiable C AND not UnsafeCut C alpha w.
```

It separates contradictions from forced roots from contradictions caused by the proposed path seeds. The satisfiability conjunct is incorporated into the automaton instead of silently assumed.

**Consequence:** no external satisfiability premise is missing from the wrapper. Earlier memo arguments that required satisfiability are not imported as unspoken assumptions here.

### F3. Ordered flags and shared word parameters survive both translations

`Basic.Agrees w i j` is `(w.drop j).IsPrefix (w.drop i)`. `Witness` checks the directed flag from the state at earlier cut `i` to the state at later cut `j`, for `i <= j <= |w|`. It does not symmetrize the relation. Source: [Basic][basic].

For one shared candidate `w`, the summary bridge uses:

```text
B_i = {m : Pop W alpha (w.take i) m}
A_j = {m : Pop (reverse W) beta (w.take j) m}
flagged(i,j) <-> B_i intersects A_j
```

Both summaries, the ordering of cuts, and suffix agreement refer to that same `w`. `prefix_reaches_iff_cut` proves the equivalence by minimum-stack factorization. Its converse constructs the prefix seed `w.take i ++ w.drop j`. There is no replacement by independently chosen words satisfying the two Pop conditions. Source: [SummaryBridge][cuts].

`RankWitnessReference.witnessRef` uses `w.reverse` and labels reversed cut `j` by original cut `|w|-j`. `witnessRef_safe` transports the directed flag obligation rather than substituting a symmetric border test. Source: [reversal][reversal].

At the compiler boundary, `SatClause` uses one vertex assignment on one graph. The semantic preimage conclusion is one safe first-return extension whose graph satisfies the whole query, not an extension chosen separately per atom. Within one physical interval, `intervalStep` advances every active observer over the same emitted bit and the same two fresh colours. Independent path witnesses remain permitted where the query grammar permits them; the compiler does not impose a new global equality of all path labels. Sources: [RankQuery][query], [compiler][compiler], [coverage][coverage].

**Consequence:** the inspected interfaces preserve the needed quantifier order and sharing. This finding is not a claim to have independently reproved every coverage/reconstruction lemma.

### F4. Prefix, diagonal, and empty cases are part of the predicate

`Witness` checks definedness and safety at cuts `0` through `|w|`. Its comparisons include `i=j`, hence every visited state must have an unflagged diagonal. They also include `j=|w|`: the empty suffix agrees with every earlier suffix, so all corresponding incoming comparisons matter. Source: [Basic][basic].

For `w=[]`, the requirements are exactly:

```text
initial is not Bad;
initial is final;
(initial,initial) is not flagged.
```

`terminalWitnessCheck` starts with `witnessCheck I []`, while `SafeReference` is explicitly nonempty. These two branches fit together; the nonempty-reference contract does not exclude empty witnesses. Source: [decision][decision].

Distinguish `Basic.safeCheck`, which tests definedness and Bad, from `AbsorbingTerminal.safeState`, which excludes both Bad and diagonal flags. `witness_safeCut` derives the stronger safe-state property from the full original witness predicate. Pruning diagonal-flagged states therefore removes no valid witness. Source: [AbsorbingTerminal][absorbing].

Undefined original transitions return `none`; a failed run is rejected rather than totalized by an accepting fallback. The actual summary automaton is total, but its image under terminalization is partial and uses the same original witness semantics.

**Consequence:** reversal and terminalization do not obtain their theorems by dropping hard endpoint or empty-word cases.

### F5. The strong absorption hypothesis is necessary and is supplied

The actual contract is:

```text
Absorbing I :=
  every defined successor q of an original final f
  is final AND flags[p][q] = false for every state p.
```

This is stronger than closure of final states under transitions. It neither says that the current final already has an empty incoming column nor that every successor is non-Bad. Source: [AbsorbingTerminal][absorbing].

`witness_append_safeRun` uses both parts. If a comparison's target remains in the original witness, agreement after appending implies the relevant old agreement. If its target lies strictly in the appended continuation, absorption supplies an empty incoming flag column. Every-cut safety still needs its separate `SafeRun` proof. This is not an assumption that complete agreement profiles are unchanged.

The summary construction proves strong absorption for every enumerated state, including unreachable states. Finality means its A component avoids forced controls. Every reverse-pop source is forced, so one transition makes A empty; this implies both successor finality and a completely empty incoming column. Source: `reverse_pop_source_forced`, `reverse_next_empty`, `summary_absorbs` in [SummaryAutomaton][summary].

Reachable-state interpretation is a separate issue. `nextSet` takes a direct pop followed by a balanced suffix. The last-letter Pop decomposition proves correctness for actual reached summaries, which are already appropriately closed. It does not assert that arbitrary non-closed subsets have the same Pop interpretation. For example, an epsilon edge p->r followed by r--a(pop)-->s allows Pop(p,a,s), while a direct-pop step from the singleton {p} need not find s. The initial summary includes the balanced closure and avoids this error. The all-state absorption proof does not need that false universal interpretation. See the preserved [bridge readback][bridge-note].

A diagnostic counterexample to weakened absorption: initial/final 0, final 1, only edge 0--0-->1, no Bad states, and flag (0,1). The empty word is a witness, but the only terminal candidate `0` is forbidden. Final-state closure alone would make the intended split false; the actual strong contract excludes it. This example is preserved in the earlier bridge note, not newly discovered here.

Terminalization first removes edges with unsafe sources or targets. It then marks final exactly the safe ORIGINAL-final states with no surviving outgoing edges. Initial state, Bad, and ordered flags are preserved. A newly created nonfinal sink must remain rejecting; an unsafe initial state must not yield an empty witness.

**Consequence:** `terminalize_terminal` provides the exact hypothesis required by the terminal decider. Applying that decider directly to an absorbing but nonterminal instance has no general completeness guarantee from `terminalWitnessCheck_correct`.

### F6. InfWitness does not hide a decision or a bound on the initial witness

`AbsorbingTerminal.InfWitness` retains:

```text
an original finite Witness I w;
its endpoint q;
a SafeRun from q along a finite stem v to r;
a SafeRun from r along a cycle c back to r;
c != [].
```

The stem may be empty; the cycle may not. The original `Witness I w` is indispensable. Source: [AbsorbingTerminal][absorbing].

The finite-state argument in `c031` begins after such a witness has been supplied. Growing a safe continuation either reaches a terminalized accepting sink or repeats a state and yields a nonempty safe cycle. The finite graph bound controls this continuation, not the length of the original witness. The infinite and terminal branches need not be mutually exclusive.

A reachable safe cycle alone is insufficient: the path leading to it must satisfy all original word-dependent comparisons. Also, an infinite safe continuation is a property of the word automaton, not a division between finite and infinite type valuations. Terminal witnesses can coexist with necessarily infinite type models. Sources: [AbsorbingTerminal][absorbing], [continuation note][continuation-note].

C029 does have a written argument and reproduction evidence. `infinite_extension_decision` implements proposed graph, lasso, and periodic-monitor cases. Its default monitor search is resource-capped and preserves `UNKNOWN`. This is not the missing total Lean Boolean with a correctness theorem for the exact `InfWitness` proposition. The present review does not promote the written C029 argument to a freshly verified all-input result. Sources: [C029 ledger][claims], [Python implementation][infinite-python], [safe-extension dependencies][safe-python].

**Consequence:** the current disjunction cannot be converted into a total entailment decision by checking graph recurrence alone, ignoring UNKNOWN, or treating the existential original witness as already decided.

### F7. The terminal decision no longer assumes the disputed numerical bound

The decisive declaration is:

```text
RankQueryDecision.terminalWitnessCheck_correct
  (I : Instance k) (ht : TerminalFinals I) :
  terminalWitnessCheck I = true <-> exists w, Witness I w.
```

`terminalWitnessCheck_sound` is stronger in one direction: it does not require terminality. Completeness uses terminality to bound rank at EVERY reversed prefix. It then covers a nonempty witness with at most `k-2` first-return promotions from a safe one-letter reference and finishes at a maximal-rank milestone. It does not bound only the rank of the complete word. Sources: [decision][decision], [terminal rank][rank], [finishing semantics][finish].

The closure obligation is actually instantiated:

```text
RankQueryCoverage.coverage I
  : DiagramCoverage I RankQueryCoverage.budget
```

The concrete semantic unwind calls `RankQueryCoverage.closure_iff`. A caller of the terminal correctness theorem need not supply a DiagramCoverage proof, a generic semantic-closure oracle, or a weight bound. Sources: [coverage][coverage], [enumeration][enumeration], [semantic unwind][unwind].

Three bounds must not be conflated:

1. The proved terminal border/rank bound controls promotion depth.
2. The finite computable diagram-syntax budget has a coverage theorem.
3. The stronger `ClosureFor` clause-weight contract and its advertised F(k) remain unresolved at the inspected snapshot.

Only the first two are needed by the direct terminal algorithm. `ClosureFor` bundles semantic correctness with the quantitative clause-weight conjunct, but the concrete semantic unwind deliberately avoids assuming that whole bundle. Having definitions called `closureBound` and `ClosureStatement` is not a proof of their stronger claims. Source: [RankQuery][query].

Small-state conventions are not hidden restrictions: `Instance k` contains an initial `Fin k`, so no zero-state instance is constructible; one-state/empty cases are handled by the original empty-word branch and natural-number subtraction. No additional k>=2 premise appears in `terminalWitnessCheck_correct`.

**Consequence:** C080's quantitative U/F investigation must remain independent. Failure or uncertainty of that numerical estimate does not by itself invalidate the checked qualitative terminal theorem; conversely the qualitative theorem does not prove the estimate.

### F8. Existing runtimes are concrete; the absent runtime is not disguised

The inspected runtime route uses explicit finite subset/table enumeration, recursion over supplied finite words, finite diagram enumeration, finite graph saturation, finite assignment enumeration, and a fixed finite number of query promotions.

For example, `StackSummary.balancedCheck` intersects all finite closed tables instead of choosing a semantically correct table through an oracle. `RankQuery.satCheck` enumerates finite assignments and checks finite product-graph reachability. `RankQueryEnumeration.diagrams` reads finite syntax limits, not an unbounded reference/word search or semantic oracle. These constructions can be extremely expensive; mathematical termination is not a practical cost claim. Sources: [StackSummary][stack-summary], [RankQuery][query], [enumeration][enumeration], [decision][decision].

Classical reasoning inside completeness proofs is distinct from runtime choice. The bridge audit script permits `Classical.choice` for theorem dependencies but rejects it for the audited runtime declarations. I inspected that script; I did not execute its transitive dependency audit. Source: [audit script][audit-script].

`SubtypeTerminalBridge` does not manufacture a Boolean for InfWitness using classical decidability. It stops at a proposition. This is an honest missing implementation, not a noncomputable algorithm disguised as executable code.

Two additional scope cautions:

- The theorem named `AbsorbingTerminal.c031` proves the safe cycle/terminal split. It does not prove the entire broader decidability equivalence recorded under ledger C031, which also references C029 and C030.
- C030's converse realization is not needed to finish the forward subtype decision. It should not be added as another missing dependency of the current forward route.

Historical README/module comments and older notes may describe an earlier frontier. Resolve current status through exact declarations and the dated STATE entry, not through a theorem-like definition name, stale introductory sentence, or issue title. Sources: [claims][claims], [STATE][state], [wrapper][wrapper].

## 4. Strongest assembled conclusion

At the inspected snapshot the supplied theorem is exactly:

```lean
theorem not_entails_iff_infinite_or_terminal
    (C : List (Constraint n)) (a b : Fin n) :
    ¬ Entails C a b ↔
      InfWitness (summaryInstance C a b) ∨
        terminalWitnessCheck
          (terminalize (summaryInstance C a b)) = true
```

Its composition has no remaining caller-supplied satisfiability, absorption, terminality, semantic coverage, or witness-bound hypothesis. One disjunct remains an undecided proposition; the input language remains normalized. Source: [SubtypeTerminalBridge][wrapper].

Writing `T(C,a,b)` for the terminal Boolean and `I` for the summary instance, ordinary classical logic yields:

```text
Entails C a b <-> not InfWitness I AND T(C,a,b) = false.
```

This is a mathematical consequence of the assembled equivalence, not a new executable declaration claimed to exist in the repository. A terminal true is conclusive non-entailment. A terminal false alone is not conclusive entailment.

The normalized semantic composition is materially stronger than a conditional reduction and does not appear to lose arbitrary-tree meaning. It still does not establish the full executable Problem 1.7 decision. Fresh source-PDF fidelity and executable verification are separate review limitations, not hidden claims of completion.

## 5. Follow-up contracts for the integrator and future agents

These are proposals and acceptance criteria, not new worker assignments or reservations. Read current #31/#33/#34/#37 and the current main before starting; this note is pinned historical evidence and may be superseded by later theorems.

### 5.1 Finish C029 against the exact proposition, without changing its meaning

Required target:

```text
Absorbing I ->
  (infiniteWitnessCheck I = true <-> AbsorbingTerminal.InfWitness I).
```

Give an explicit finite representation, initial state, transitions, acceptance condition, and termination argument. Retain the original Witness conjunct, every-cut safety, empty stem, nonempty cycle, arbitrary pre-final loops, and partial transitions. A state cap must return UNKNOWN in an experimental implementation; it cannot become a theorem premise or a negative answer of the total decider.

For the existing primitive-period forward monitor, prove the invariant before relying on its implementation: after reading t letters with fixed endpoint offset h, the buckets record exactly the cut states in the maximal final segment matching the chosen periodic phase, grouped by residues modulo the primitive period; the conflict bit records an ordered flagged pair in that segment with compatible residues. On mismatch the segment starts at the new cut, previous buckets/conflict are reset, and that cut is seeded. Diagonal safety is checked separately. Acceptance must be proved equivalent to absence of a persistent forbidden ray, not just tested on bounded words.

A nonprimitive-cycle/rotation formulation needs its own exact phase-equivalence theorem; raw congruence modulo the displayed cycle-word length is not a substitute for primitive periodic equality. Prove the chosen representation's relation to actual infinite tails. Then prove both directions between successful monitoring and an original finite witness with a retained infinite safe future.

At publication preparation, #31 already had an active `c029-cycle-monitor-20260919` owner considering a simpler safe-cycle enumeration / rotation-based route. Its [scope claim](https://github.com/mhenglein/subtail/issues/31#issuecomment-5742392557) excludes normalization and U/F. Do not duplicate or overwrite that implementation. The alternative route is a proposal by that worker, not an additional theorem certified by this audit.

### 5.2 Normalize finite syntax conservatively over models

An independent, disjoint next contribution can close the syntax boundary. Specify original finite expressions, evaluation into arbitrary `Tree`, variable embedding, fresh-variable construction, normalized clauses, and normalized query variables.

The central contract is stronger than equisatisfiability. For normalization `N(C)` and restriction to original variables, establish both:

```text
every rho satisfying original C extends to rho' satisfying N(C);
every rho' satisfying N(C) restricts to rho satisfying original C.
```

Prove preservation of the interpretations of original variables and the queried inequality under the embedding. Then derive exact entailment equivalence. A mere theorem `Sat(C) <-> Sat(N(C))` is insufficient for universal entailment.

Handle nested products, bottom occurrences on both sides, repeated subexpressions/variables, empty constraint sets, and inconsistent constraints. Models remain arbitrary prefix-closed predicates; no finite or regular presentation may be inserted. Validate the implementation with concrete semantics as well as source inspection. None of this normalization was implemented or proved in this audit.

### 5.3 Assemble and audit the final executable theorem

After C029 and normalization are proved, define the normalized non-entailment Boolean from the two exact branches and negate it for entailment; then connect the original-syntax normalizer. Prove correctness against original universal entailment, with no oracle, supplied witness bound, conditional closure package, or resource-cap hypothesis.

Acceptance should include pinned build, kernel replay, complete theorem/runtime dependency audit, original-definition readback by a different session, and targeted regressions. Keep source inspection distinct from execution. Suggested semantic regression categories: forced-root contradiction and vacuity; a satisfiable system with no finite models; empty witness; diagonal-only obstruction; asymmetric ordered flags; safety failure only at a proper prefix; unsafe initial state; pruning an unsafe edge before the sink test; nonfinal sink rejection; cycle-only and terminal-only positive cases; and a negative case that cannot be inferred merely from the terminal branch.

The original memo is already preserved in the repository. A future reviewer with binary access should compare Problem 1.7 and the constructor/model definitions directly against it and record exact pages/checksum. This closes this review's transcription-fidelity limitation, without reopening the retired original-script reproduction task.

### 5.4 Keep quantitative and converse work out of the critical-path assumptions

The explicit U/F estimate and C030 converse realization remain useful independent research/review tasks. Do not require either to finish the already selected forward qualitative decision route. A theorem about terminal decision, a theorem about original-syntax entailment, a witness bound, and a converse reduction are different deliverables with different dependencies.

## 6. Publication and evidence handoff

Publication adds only this note. No source/interface, scientific status, shared ledger, generated index, or workflow is changed. Scope was announced on [#33](https://github.com/mhenglein/subtail/issues/33#issuecomment-5742581899) and [#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5742584823). Integration and any shared-ledger cross-reference remain with the current integrator; the publication does not claim a main integration lease.

The final PR/issue handoff records the actual publication commit, changed-file readback and any observed documentation CI result. Documentation CI is not a substitute for the NOT RUN Lean/kernel/axiom/semantic tests above. No background research or follow-up worker was launched by this publication. Other agents' local workspaces, stashes and unpushed work were not inspected or claimed clean.

Suggested durable indexing at integration: link this report under the A010/A018 review history and the #33 review record, without changing C029/C031/C080 evidence levels. The report does not change the scientific frontier, so no substantive STATE status promotion is warranted.

## Pinned source references

All source links below are pinned to the detailed inspection revision; the final wrapper and STATE readback at e1e8f635 were unchanged. Exact declaration names are given in the findings rather than unstable line-number guesses.

[problem]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/research/problem.md
[initial-review]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/REVIEW.md
[papers]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/papers/README.md
[state]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/STATE.md
[claims]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/research/claims.md
[trees]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/TreeSemantics.lean
[basic]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/Basic.lean
[canonical]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/CanonicalModel.lean
[canonical-checks]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/CanonicalReachability.lean
[stack-summary]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/StackSummary.lean
[stack-reach]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/StackReachability.lean
[cuts]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/SummaryBridge.lean
[summary]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/SummaryAutomaton.lean
[absorbing]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/AbsorbingTerminal.lean
[wrapper]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/SubtypeTerminalBridge.lean
[decision]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQueryDecision.lean
[rank]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/TerminalRank.lean
[reversal]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankWitnessReference.lean
[query]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQuery.lean
[compiler]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQueryCompiler.lean
[enumeration]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQueryEnumeration.lean
[coverage]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQueryCoverage.lean
[unwind]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQuerySemanticUnwind.lean
[finish]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/RankQueryFinishTrace.lean
[bridge-note]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/notes/2026-09-19-subtype-summary-bridge.md
[continuation-note]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/notes/2026-09-04-denials-and-continuations.md
[infinite-python]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/experiments/infinite_extensions.py
[safe-python]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/experiments/safe_extensions.py
[audit-script]: https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/scripts/check_subtype_summary.py
