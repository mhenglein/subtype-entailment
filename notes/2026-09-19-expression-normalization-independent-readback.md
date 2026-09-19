# Independent readback of the checked finite-expression normalizer

Date: 2026-09-19.
Session: `expression-normalization-independent-readback-20260919`.
Workstreams: A010/A018. Review #33; semantic bridge #31; coordination #37.

## 1. Verdict and exact review scope

**No mathematical or semantic blocker found in the reviewed normalization declarations.** PR #49 supplies the executable Lean normalizer and the unconditional entailment, satisfiability and same-address model-transfer theorems that the earlier end-to-end audit identified as missing. Its definition-only model extension is unique. This source readback supports accepting that normalization contribution at the pinned revision, subject to serialized integration and continuing verification of the combined tree. It does not establish the complete subtype decision.

The original end-to-end audit and Python reference are already completed and pushed in PRs #44 and #50. Another allocator or duplicate normalization proof is not warranted. The separate Lean author completed and released PR #49 before this review. The useful remaining work in this lane was the independent statement readback requested by that handoff, not taking over the existing proof or C029 work.

Reviewed PR #49 HEAD: **`d85e203e0d96bb5b452c89a4b06a6cc772195320`**.
Observed main and this documentation branch base: **`7185b15140fbc629bf1825063d1652d4feb8a43f`**.
PR #49's tested merge ref: **`998c6fbfc6c82bd715261c229515a429baa2e163`**, a test merge, not publication to main.
PR #50 reference HEAD: **`7b9ea558ad54753cd09af3e8dfa22bb45503735c`**.

Reviewer independence: this is the preceding end-to-end review session and the author of PR #50's separate Python reference, NOT the author of PR #49's Lean sources. The reviewer inherited the ordinary normalization route and read the Lean author's explanation. This is cross-session source/statement review, not blind invention, human refereeing, or an independent reimplementation of Lean's kernel.

Read in full: the two new Lean modules, the dedicated normalization workflow, and its Python finite-set/native-output checker. Reread the inherited TreeSemantics definitions and the current default import aggregator. Read the actual completed remote run metadata, step conclusions, and decoded job log. Checked both PR changed-filename lists.

No Lean build, kernel replay, axiom audit, or semantic test was newly run by this review session. The remote runs below are actual prior executions whose logs were inspected now, not newly executed tests. Original PDF bytes and the ongoing C029 proof were not re-audited. No proof, source interface, checker, result, shared ledger, default import, or workflow was changed by this review.

### Pinned source identities

| File | Git blob SHA |
|---|---|
| `lean/Subtail/ExpressionNormalization.lean` | `41a58630c8cad15a15d380d4032d338ca8adc8c2` |
| `lean/Subtail/ExpressionNormalizationAudit.lean` | `42a7b82f3e012f644be67554f4377d5374d19a30` |
| inherited `lean/Subtail/TreeSemantics.lean` | `ead23728e922fa57c8b8c846129086f4f7aaa435` |
| `experiments/check_expression_normalization_lean.py` | `eb46f0bb3972be35eb62f2f86b53b55b7903559b` |
| `.github/workflows/lean-expression-normalization.yml` | `c08e29f9c57b0c20671b48fc5e353d0a27ebd818` |
| inherited `lean/Subtail.lean` | `9cccaca253bef2fbb143035371bf7c68a30cc47f` |

## 2. Statement and dependency readback

Namespace: `Subtail.ExpressionNormalization`.

```lean
theorem normalize_entails_iff (G : Input n) (s t : Expr n) :
  ExprEntails G s t <->
    Entails (normalized G s t)
      ((naming G s t).ref s) ((naming G s t).ref t)
```

This declaration has no satisfiability, finiteness-of-model, regularity, decidable-membership, witness-length, C029, C030, or quantitative-bound premise. Its core imports only the existing TreeSemantics module. `Expr` is finite syntax with exactly variable, bottom, and ordered binary product constructors. `eval` recursively evaluates syntax into the unchanged arbitrary `Tree`; it does not recursively inspect or unfold the trees assigned to variables.

The source dependency map is:

```text
finite input expressions and both query expressions
  -> forest / Expr.pairs / Expr.hasBot
  -> naming with a proved positive output variable count
  -> naming_support + naming_closed
  -> both defining inequalities for every allocated product slot
  -> extend_definitions + representative_correct
  -> extend_models + restrict_models
  -> normalize_entails_iff / normalize_satisfiable_iff /
     normalize_separating_iff

all output indices partitioned into old / optional bottom / product slots
  -> extend_restrict + restrict_extend
  -> unique_definition_extension
```

`ExprModels` and `ExprEntails` quantify over `Valuation n = Fin n -> Tree`. `Tree.nodes` remains `Word -> Prop`, with prefix closure, not a finite set or an automaton presentation. Bottom is the empty product-node set; product always inserts its root. No top constructor or finite-tree reinterpretation is introduced.

## 3. Findings on the actual construction

### N1. The total fallback is contained by a proved support invariant

`Naming.ref` is total even on expressions absent from its table: unsupported products, and bottom when no bottom slot was allocated, use index zero. It would be wrong to assert semantic correctness for every arbitrary call to this function.

The actual correctness theorem does not assert that. `Supports b ps e` recursively requires a bottom slot for bottom and table membership plus support of both children for a product. `representative_correct` and `extend_ref` require this predicate. `supports_self`, `supports_forest`, and `supports_children` prove it from actual finite input syntax. `naming_support` covers both query roots and every premise root, while `naming_closed` covers the children of every allocated pair. The high-level theorems supply those proofs rather than asking the caller to assume them.

Therefore the fallback is not used where the compiler's semantic theorems need a representative. It is an API boundary for arbitrary hand-built `Naming` values, not a gap in `normalized`.

`Naming.positive` is also proved from a supported query expression, rather than assumed as an input restriction. Constant-only inputs with `n=0` remain included: the query syntax necessarily supplies a bottom or product allocation. There is no hidden `n>0` hypothesis.

### N2. Duplicate slots remain fully determined

`Expr.pairs` enumerates product occurrences in preorder and retains duplicates. `locate` uses decidable equality of FINITE SYNTAX and selects the first matching pair. This is not a test of semantic equality of arbitrary trees.

References to identical subexpressions may share the first slot, but `Naming.definitions` still emits an upper and lower defining inequality for EVERY occurrence index in `List.finRange R.pairs.length`. The left-hand proxy of those definitions is `R.slot j`, not the first-match representative. Consequently later duplicate slots are not unconstrained garbage.

`models_slot` proves equality with the product of the child representatives for every slot index, including slots not used by any parent or query root. In the audit module, `extend_restrict` partitions every output index into an old index, the optional bottom index, or a product slot. Its product branch applies `models_slot` and representative correctness to the slot's two children. Thus uniqueness covers all allocated variables, not just the reachable representatives.

The change from the advisory/reference's occurrence naming to first-match references is semantically sound. It is not a byte-for-byte identity with PR #50's postorder occurrence allocator, nor a claim of linear-time structural lookup.

### N3. Both product directions and the query-not-premise boundary are correct

For each slot, `Naming.upper` and `Naming.lower` refer to the same two child representatives in the same order. Mutual `Below` implies tree equality through `tree_eq_of_below`; no decidable equality of trees is required. The lower clause forces the product root even when both children are bottom. The upper clause rules out additional proxy nodes.

The optional bottom slot has exactly one denial. This suffices for equality to bottom because the reverse inclusion from the empty set is automatic.

`forest G s t` includes both query expressions and both sides of every premise. `normalized G s t` is exactly its definitions followed by variable inequalities obtained from G. It does NOT append the queried inequality. Definitions of query subexpressions are conservative over every original valuation; treating them as definitions is not treating the query as a premise.

### N4. Model preservation is stronger than equisatisfiability

`Naming.extend` preserves old variable values literally, assigns bottom to the optional bottom coordinate, and evaluates the original finite product expression associated with each product slot. Under `R.Closed`, `extend_definitions` holds for EVERY original valuation, whether or not that valuation satisfies G.

For an arbitrary model eta of the definitions, structural induction in `representative_correct` gives

```text
eta (R.ref e) = eval (R.restrict eta) e
```

for every supported e. The variable case is restriction, the bottom case uses the denial, and the product case uses both defining clauses followed by the two induction hypotheses. The invariant covers all supported subexpressions, not merely the two query roots.

`extend_models` and `restrict_models` apply this equality to both sides of every original premise. `restrict_extend` and `extend_restrict` give inverse maps on the definition models. `unique_definition_extension` explicitly states unique existence for each prescribed original valuation. For the generated naming, its closure hypothesis is supplied by `naming_closed`.

Together these declarations give the following ordinary corollary for every eta:

```text
Models (normalized G s t) eta
  iff
eta = (naming G s t).extend ((naming G s t).restrict eta)
  and ExprModels G ((naming G s t).restrict eta).
```

This line is a readback consequence of the named declarations, not a separately added Lean theorem. Inconsistent premises remain inconsistent on both sides; universal entailment is vacuous on both sides. No external satisfiability test is assumed.

### N5. Original indices and exact separating addresses are retained

`Naming.old` embeds an original variable using the same natural-number index. `old_value` and `variable_query_preserved` record that fact. `old_ne_slot` and `old_ne_bottom` establish the relevant fresh-name separation; slot indices start after the original block and the optional bottom slot.

`normalize_separating_iff` quantifies a fixed `w : Word` OUTSIDE the existential valuations and uses that same w on both sides. It proves the exact same-address countermodel equivalence, not merely equisatisfiability or existence of some potentially different word. `normalize_entails_iff` proves both universally quantified directions by extension and restriction, not by inspecting only one least model.

The API takes a declared `Fin n` original variable domain, including unused or query-only variables. It is not a theorem about a separate string parser or arbitrary JSON front end; a named-variable front end must preserve its own finite support embedding.

### N6. Counts and totality have the stated scope

The independent syntax recursion `Expr.productCount`, together with `pairs_length_count` and `forest_pairs_length`, connects the occurrence table's length to the number P of product occurrences. B is the Boolean bottom-occurrence indicator, converted to zero or one.

`added_variables`, `definitions_length`, and `normalized_length` give exactly P+B fresh variables, 2P+B defining clauses and m+2P+B total clauses for m premises. Query syntax contributes to P and B but not to m. These are list/occurrence counts, not a compressed-DAG size bound, a clause-deduplicated count, or a runtime-complexity theorem.

The executable construction traverses finite expressions/lists and performs decidable finite-syntax lookup. It does not enumerate models, query tree membership, solve a SAT problem, or search for an unbounded witness. Its finite output is established independently of the unrelated rank-query U/F estimate.

## 4. Adversarial coverage and limits

The audit module includes propositions, not just native assertions, for the following critical model boundary: `infiniteInput` is x times bottom below x. `infinite_input_model` supplies zeroSpine; `infinite_input_not_entails` separates x from bottom at the empty address; `infinite_input_every_model_unbounded` proves that EVERY satisfying valuation has arbitrarily long product addresses. The normalized non-entailment result is then transported by the actual normalization theorem.

`impossibleInput` has no original variables and asserts bottom times bottom below bottom. Both original and normalized unsatisfiability are proved. Executable `decide` fixtures additionally cover repeated product occurrences, no originals, empty premises, variable-only queries and a compound query which must not be asserted as a premise.

The Python checker uses literal finite product-node sets and untruncated product construction. It evaluates original syntax separately, checks normalized clauses directly, tests definition-only uniqueness, and compares actual Lean output records against its separate compiler. Its mutation guards remove either product inequality and test query-as-premise and freshness errors. Its finite corpus does not cover all infinite/nonregular valuations; the universal result comes from the Lean theorems, not those tests.

I found no additional semantic blocker in these source interfaces. I did not run a new adversarial corpus or claim that this readback independently reconstructs every original source-paper argument.

## 5. Remote evidence directly verified in this review

The authoritative dedicated run is [35451616693](https://github.com/mhenglein/subtail/actions/runs/35451616693), job [105919649027](https://github.com/mhenglein/subtail/actions/runs/35451616693/job/105919649027).

The run metadata ties it to PR #49 head d85e203. The decoded checkout log explicitly records test merge `998c6fbfc6c82bd715261c229515a429baa2e163`, merging that head into main `7185b15140fbc629bf1825063d1652d4feb8a43f`. The environment reports Lean 4.33.1, Lake 5.0.0, Ubuntu 24.04.5 x86_64 and Python 3.11.16.

| Observed remote check | Result and scope |
|---|---|
| `lake build +Subtail.ExpressionNormalizationAudit` | SUCCESS; both new modules actually rebuilt in the recorded five-job dependency build. |
| `lake env leanchecker Subtail.ExpressionNormalization` and audit-module replay | SUCCESS; explicit step completed, not merely the setup action's disabled optional checker. |
| Source unfinished/custom/native-proof guard | SUCCESS. |
| Named declaration audit | 82 names emitted, with a separate 36 non-theorem-name report. Observed closures use at most propext and Quot.sound; no Classical.choice, custom axiom or sorryAx appears in those declaration results. |
| Actual Lean output and finite-set oracle | SUCCESS: 372 matching records; 7,624 original valuations, 567,340 arbitrary extended finite valuations and 10,479 exact query-set checks. |

The workflow's generic Lean-action build/checker options are disabled because later explicit steps perform these tasks. The logs show those later commands running successfully; the result is not inferred from the setup step.

All seven PR #49 head-associated workflows were completed SUCCESS at this review's status readback: dedicated normalization 35451616693, Research 35451616609, Lean 35451616627, Experiments 35451616659, Replay 35451616591, Recovered 35451616572, and Guarded 35451616615. Only the dedicated normalization job received the detailed decoded-log inspection described above; the others are workflow-status observations.

All six workflows attached to the unchanged PR #50 head were also completed SUCCESS: Research 35451249137, Lean 35451249150, Experiments 35451249206, Replay 35451249146, Recovered 35451249154 and Guarded 35451249174. This closes the previously pending CI-status part of our reference handoff. It does not retroactively register PR #50's new standalone checker in an existing workflow or certify the Python program by Lean.

No remote workflow was newly dispatched, and no local Lean/Python proof or semantic test was rerun by this review. New documentation CI, if triggered by publication of this note, must remain separate evidence.

## 6. Remaining integration requirements, not another normalization proof

**I1: include the core in the intended default dependency graph.** The inspected `lean/Subtail.lean` does not import ExpressionNormalization. The dedicated job proves that the explicitly requested modules build; it does not make them default imports. Add the core deliberately during serialized integration. The audit module defines a top-level main for its executable differential, so its inclusion should be deliberate rather than blindly aggregating executable audit modules.

**I2: preserve dependency-triggered checks.** The isolated normalization workflow currently triggers on PR edits to ExpressionNormalization module names, its own workflow, and its `_lean` checker. It has no push trigger and does not itself select Basic, TreeSemantics or toolchain changes. This does not invalidate the inspected run. It does mean the integrator must preserve build/replay/axiom/native checks when imported dependencies change, either by consolidation into shared Lean CI or by appropriate triggers. A future dependency-only change must not silently bypass normalization verification.

**I3: keep the two implementations and their evidence distinct.** Actual changed-filename lists confirm PR #49 uses `check_expression_normalization_lean.py` and `expression-normalization-lean.json`, while PR #50 uses the generic checker/result names. Their six and four changed-file sets are disjoint. Both can be retained. Their naming algorithms differ, so PR #49's native comparison is not evidence of byte-identical output from PR #50.

**I4: integrate and index without overstating the project result.** Independent source readback is now supplied by this note. Main merge/default-import changes and shared A018/claims/STATE synchronization remain for the authorized integrator. Link this review and the actual checked proof revision. A prior statement that no Lean normalization exists is superseded on PR #49's branch, not retroactively false at its original historical checkpoint.

There is no reason to reopen the allocator/model-transfer proof merely to duplicate a completed contribution. After safe integration, the remaining forward route is the exact C029 executable theorem and final original-language Boolean composition, according to whichever current revisions the integrator verifies. This review does not audit or take over those ongoing tasks. Neither the separate converse C030 nor the quantitative U/F estimate is introduced as a new prerequisite.

## 7. Completion boundary and publication

The strongest reviewed formal conclusion is unconditional finite-expression entailment equivalence to the existing normalized semantics, plus model/satisfiability/same-address preservation, on the pinned PR #49 revision. Combining it algebraically with the earlier normalized summary split extends that split to finite expression inputs, but this note adds no new compiled composition declaration and does not turn the still-separate infinite branch into a Boolean.

Original audit/reference work is complete and pushed. The independent normalization readback is complete with this publication. The submitted proof/reference PRs were open, not merged, at the inspected snapshot. Integration and the complete subtype decision remain different milestones.

Only this new note is published by the review session. Scope was announced in [#31](https://github.com/mhenglein/subtail/issues/31#issuecomment-5743298995) and [#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5743299500). No integration lease was acquired. All note/review scope is released in the final commit-pinned handoff. Other agents' local workspaces, stashes and unpushed changes were not inspected or claimed clean.

## Source links

- [Reviewed core](https://github.com/mhenglein/subtail/blob/d85e203e0d96bb5b452c89a4b06a6cc772195320/lean/Subtail/ExpressionNormalization.lean).
- [Reviewed uniqueness/counts/regression module](https://github.com/mhenglein/subtail/blob/d85e203e0d96bb5b452c89a4b06a6cc772195320/lean/Subtail/ExpressionNormalizationAudit.lean).
- [Inherited arbitrary-tree semantics](https://github.com/mhenglein/subtail/blob/d85e203e0d96bb5b452c89a4b06a6cc772195320/lean/Subtail/TreeSemantics.lean).
- [Reviewed dedicated workflow](https://github.com/mhenglein/subtail/blob/d85e203e0d96bb5b452c89a4b06a6cc772195320/.github/workflows/lean-expression-normalization.yml).
- [Reviewed finite-set/native checker](https://github.com/mhenglein/subtail/blob/d85e203e0d96bb5b452c89a4b06a6cc772195320/experiments/check_expression_normalization_lean.py).
- [Inspected default import graph](https://github.com/mhenglein/subtail/blob/d85e203e0d96bb5b452c89a4b06a6cc772195320/lean/Subtail.lean).
- [Lean contribution PR #49](https://github.com/mhenglein/subtail/pull/49) and [separate Python reference PR #50](https://github.com/mhenglein/subtail/pull/50).
