# Checked finite-expression normalization over arbitrary trees

Date: 2026-09-19. Actor/session: ChatGPT `expression-normalization-lean-20260919`.
Related: A010/A018, finite-syntax obligation in #31, review #33, integration #37, advisory #45, implementation PR #49.

## Result and evidence boundary

The total finite-expression compiler and its model/entailment/address theorems are implemented in [ExpressionNormalization.lean](../lean/Subtail/ExpressionNormalization.lean). [ExpressionNormalizationAudit.lean](../lean/Subtail/ExpressionNormalizationAudit.lean) proves exact counts, freshness, uniqueness of all auxiliary values, and an infinite-only model regression, and exports a native corpus for an independent Python checker.

**LEAN:** both modules compile with pinned Lean 4.33.1 and pass bundled kernel replay. The complete named-declaration dependency audit and separate executable-definition audit pass; their observed axioms are only `propext` and `Quot.sound`, with no `Classical.choice`, custom axiom, or `sorryAx`. **REPRO:** 372 native Lean outputs match a separate Python syntax compiler; finite-set semantic checks also pass. This is not a finite-tree replacement of the theorem.

**Review boundary:** this is the advisory author's constructive continuation and same-session statement readback, NOT an independent cross-session review. That review remains pending. No main integration, shared import change, ledger promotion, C029 proof, general entailment decision, or C080 quantitative bound is claimed here.

The original ordinary proof is preserved in [advisory PR #45](https://github.com/mhenglein/subtail/pull/45), at `c33d0c8d65158fc7ba53e5bc24c14132f071dc42`. Its mathematical investigation inspected `064fc7306b679bf607b91e7d8de259823f200c62`. This implementation started from main `3ce7cf18899ad24a5562d4b614f738bec8bc8427` on a separate branch.

## Exact implemented input and output

`Expr n` is the finite inductive syntax `var (Fin n) | bot | prod (Expr n) (Expr n)`. `Input n` is a list of expression pairs interpreted as inequalities. `eval` returns the EXISTING `TreeSemantics.Tree`; variable values still have arbitrary predicates `Word -> Prop` with prefix closure, not finite or regular encodings. Only expression syntax is recursively evaluated.

Given premises `G` and a query `s <= t`, the public executable interface is:

```lean
let R := naming G s t
-- normalized premises:
normalized G s t : List (TreeSemantics.Constraint R.total)
-- queried original meanings, now represented by variables:
R.ref s : Fin R.total
R.ref t : Fin R.total
```

The syntax forest is query-left, query-right, then the two sides of each premise. Let P be its number of product occurrences and B be 1 exactly when bottom occurs. `R.total = n + (B + P)`. Old indices keep their exact numeric values; bottom, when present, is at n; product occurrence j is at n+B+j. There is no bottom slot if bottom is absent. No SAT oracle or semantic equality check occurs.

The implementation uses a deliberately simple naming variant of the advisory: product pairs are collected in PREORDER with duplicates retained. Every occurrence gets its own allocated and constrained slot, but a child or root reference to repeated identical syntax uses the FIRST matching table slot. This is syntactic equality on finite expressions, not semantic equality on trees. All duplicate slots retain both defining inequalities, so even unused duplicates are uniquely determined.

For every product table entry `(l,r)` at slot j, emit exactly `.upper (slot j) (ref l) (ref r)` and `.lower (ref l) (ref r) (slot j)`. The target of `lower` is LAST. Emit one denial for the bottom proxy if used, then one `.leq` for each original premise. The query comparison is NEVER appended as an assumption; only its definitions are present.

`Naming.ref` is total even on expressions absent from a generic table, using an index-zero fallback. The `Supports` invariant proves that this fallback is never selected for any expression actually compiled by `naming G s t`, including children, premises, and both query roots. `Naming.positive` is derived constructively from the existence of the input query expression; it is not an additional restriction on n=0 or on original valuations.

This first implementation does NOT claim the advisory's linear-time postorder algorithm: repeated structural lookup and list construction may be superlinear. Its variable and clause counts are nevertheless exact. An optimization must preserve the checked semantic contracts rather than silently changing them.

## Checked theorem interfaces

All names below are in `Subtail.ExpressionNormalization`.

| Obligation | Checked declarations |
|---|---|
| Every original valuation extends to the definitions | `extend_definitions`, `extend_ref`, `restrict_extend` |
| Representatives have exact meanings in every definition model | `representative_correct`, `models_slot`, `models_bottom` |
| Original models extend; normalized models restrict | `extend_models`, `restrict_models` |
| Entailment equivalent, no satisfiability premise | `normalize_entails_iff` |
| Satisfiability equivalent, including inconsistent inputs | `normalize_satisfiable_iff` |
| Every fixed separating address preserved | `normalize_separating_iff` |
| Original query indices preserved and fresh slots disjoint | `old_value`, `variable_query_preserved`, `old_ne_slot`, `old_ne_bottom` |
| Restriction/extension inverse on definition models | `extend_restrict`, `unique_definition_extension` |
| Exact syntactic sizes | `pairs_length_count`, `forest_pairs_length`, `definitions_length`, `normalized_length`, `added_variables` |

The top entailment statement has no hidden `Closed`, SAT, regularity, decidability-of-membership, or length-bound assumption:

```lean
theorem normalize_entails_iff (G : Input n) (s t : Expr n) :
  ExprEntails G s t ↔
    Entails (normalized G s t)
      ((naming G s t).ref s) ((naming G s t).ref t)
```

Generic helper statements about a supplied naming table require its finite syntactic support/closure invariant. `naming_support` and `naming_closed` discharge that invariant for every actual input. For unique existence, the audit module spells out an existential and a universal uniqueness clause instead of importing extra `ExistsUnique` notation.

## Ordinary readback of the implemented proof

For an old valuation rho, preserve rho on every old index, assign bottom to its proxy, and assign evaluation of a product pair to EACH occurrence slot. This is the explicit executable-on-values `Naming.extend` construction; the proof needs no ability to decide tree membership or equality. `extend_ref` identifies the first matching slot using `get_locate`, so all emitted definitions hold, independently of original premises.

Conversely, in any model eta of the definitions, the denial forces the bottom proxy to the empty product-address set. The upper and lower constraints force every product slot to equal the product of its two child representatives, including the mandatory product root. Induct on FINITE source syntax: old variables restrict exactly, bottom is forced, and both inclusions plus the child induction hypotheses give exact product evaluation. That is `representative_correct` for every supported expression, not merely query roots.

Every allocated duplicate slot also has its own two constraints. Apply representative correctness to its children and the slot equation to obtain its prescribed evaluated value. Case analysis on an output index (old, optional bottom, product slot) proves `extend_restrict`. Therefore the definitions uniquely extend every original valuation and the full model classes are in bijection under extension and restriction.

A translated root premise now holds exactly when its original evaluated inequality holds. This yields both model implications. Apply those implications to an arbitrary model and use root correctness to obtain entailment equivalence. Retaining the SAME finite address w yields `normalize_separating_iff`; neither its word nor the original trees are approximated. Satisfiability equivalence follows from the same two model maps, so inconsistent inputs are preserved and their entailments remain vacuous.

`Expr.productCount` is an independent syntax recursion. Its equality with the product-table length is checked, as is the sum over the full forest. Each product entry contributes exactly two clauses; bottom contributes B; each premise contributes one. Thus:

```text
added variables = P+B
all variables   = n+P+B
definitions     = 2P+B
all clauses     = G.length+2P+B
```

Products and bottoms in the query count toward P and B; the query inequality contributes no premise. Finite n can be zero. Cycles among original constraints, such as `x × bottom <= x`, are not cycles in expression syntax and trigger neither infinite unfolding nor an occurs check.

## Regression evidence and its limits

The checker [check_expression_normalization_lean.py](../experiments/check_expression_normalization_lean.py) does NOT call a normalized solver to evaluate original premises. It recursively evaluates the original expressions into complete finite address sets, and separately evaluates each emitted normalized clause. Products are never truncated. Its own compiler uses a first-occurrence dictionary rather than Lean's dependent finite-index lookup; every native emitted index, ordered clause, query root, and total variable count is compared exactly.

The deterministic corpus has all height-at-most-one expression pairs over n=0,1,2, used both as empty-premise queries and single-premise inputs, plus nested repetitions, an infinite-only premise, a ground inconsistency, and a fresh-collision fixture. Across 372 cases it checks:

- 7,624 original valuations and their canonical extensions, including 5,781 original models.
- 567,340 arbitrary extended valuations over five finite trees, with at most 15,625 such valuations per fixture.
- 2,855 definition models, 2,354 full normalized models, and 10,479 exact query-set comparisons.
- 372 native Lean output records matching the independently produced records.
- Adversarial guards for deleting either product inequality, asserting the query, and colliding a bottom proxy with an original variable. The first three explicitly mutate or add clauses; the collision guard checks the countervaluation and preserved original indices.

The five finite values are empty, root-only, root-with-left, root-with-right, and root-with-both product-node sets. No failure to find a finite model is treated as arbitrary-tree UNSAT. The bounded corpus supports implementation validation; the quantified Lean theorem supplies the arbitrary-tree result.

The Lean audit separately proves `infinite_input_model`, `infinite_input_not_entails`, `normalized_infinite_input_not_entails`, and `infinite_input_every_model_unbounded` for `x × bottom <= x`. The last proves every model has product addresses longer than any N, so a finite-tree-only interpretation would be genuinely wrong. It also proves the original and normalized ground inconsistency `bottom × bottom <= bottom`, plus checked small output counts using ordinary `decide` (not `native_decide`). The advisory's nonregular square-position valuation remains a mathematical example, not a claim that a finite enumerator exhausts nonregular trees.

## Actual validation and reproducibility

**Validated source checkpoint:** `01e276eed795d017df656875a06da6445152db53`.
**Actual PR merge snapshot checked:** `4fe5f307f83a64f369b6269327c6de0c603b3b16`, combining that head with main `7185b15140fbc629bf1825063d1652d4feb8a43f`.
**Passing dedicated run:** [35451433222](https://github.com/mhenglein/subtail/actions/runs/35451433222), job `105919161375`. Run steps and decoded logs were inspected, not inferred from publication. Research checks also passed at that head in run `35451433242`.

The checked code blobs are core `41a58630c8cad15a15d380d4032d338ca8adc8c2`, audit `42a7b82f3e012f644be67554f4377d5374d19a30`, and Python checker `eb46f0bb3972be35eb62f2f86b53b55b7903559b`. The later packaging rename preserves these exact bytes and changes only the dedicated workflow's checker path; the PR handoff pins the final head and any final-tree replay separately.

Actual remote environment: Ubuntu 24.04.5 x86_64, Python 3.11.16, Lean 4.33.1 / Lake 5.0.0, Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The existing toolchain file was not edited. The dedicated workflow is read-only and has a 15-minute job timeout; no tighter remote memory cap is claimed.

Commands (the successful pre-rename run used the old checker basename without `_lean`):

```sh
cd lean
lake build +Subtail.ExpressionNormalizationAudit
lake env leanchecker Subtail.ExpressionNormalization
lake env leanchecker Subtail.ExpressionNormalizationAudit
cd ..
mkdir -p tmp
(cd lean && lake env lean --run Subtail/ExpressionNormalizationAudit.lean) > tmp/normalization-native.jsonl
python3 experiments/check_expression_normalization_lean.py --lean-output tmp/normalization-native.jsonl
```

The isolated [workflow](../.github/workflows/lean-expression-normalization.yml) also prints dependency closures for all 82 named declarations and separately for the 36 non-theorem declarations, checks an explicit axiom allowlist, and rejects incomplete/custom-axiom source. Anonymous small `example`s are kernel-replayed with the audit module; they are not falsely included in the named-declaration count. Standard `propext`/`Quot.sound` appear in erased indexing/extensionality proofs. Actual printed closures contain no `Classical.choice`, including the executable compiler and native exporter. Shell pipelines use `pipefail` so failed Lean invocations cannot be hidden by `tee`.

Actual local Python-only replay used `/usr/bin/python3` 3.13.5 on Linux x86_64, with 20 CPU seconds, 256 MiB address-space and 30-second wall caps. Runs with `PYTHONHASHSEED=0` and `1` both passed with byte-identical JSON. The source SHA256 was `010f6ff29b67fa5653fa5a93cf2505eb35ee326b547e39bf0f4a6fad99349c3e`. No local Lean build is claimed: Lean was unavailable and local GitHub DNS resolution failed. An earlier capped virtualenv-Python attempt exited by signal 9 without diagnostics; its cause is unknown, not a semantic negative. The system-Python replays and remote Python run are the positive evidence.

Machine-readable evidence is in [expression-normalization-lean.json](../results/expression-normalization-lean.json). The full repository default build and all other experiment suites were not independently completed by this worker; do not promote a partial/general workflow status to such a claim.

## Retained failures and collaboration reconciliation

The first core build failed on two arithmetic proof closures and an unavailable congruence lemma name. These were repaired without changing the compiler or theorem assumptions; core-only checking then passed at `6afd0137c2cdaae6c3618c00830b9c859347d8ca` (run `35451020940`). The first audit build failed on list-length simplification, unavailable unique-existence notation, inferred fixture arguments, a replicate rewrite and string formatting. They were repaired directly, not replaced by assumptions.

At `4df65545808368e7f2643e6852bbd33b92be7da7`, both modules, kernel replay and axiom audits passed, but an unused-simp warning was mixed into the native JSON output, causing strict parsing to fail (run `35451341684`). Removing the unused proof hint made the complete run pass at the checkpoint above. The checker was not weakened to silently discard malformed output, and the failed runs remain in history.

During final readback, the separate Python implementation PR #50 was discovered to propose the same generic checker/results paths on another branch. This worker renamed ONLY its own files to the `_lean` / `-lean` names, preserving the checker blob, and announced that amendment in [#31](https://github.com/mhenglein/subtail/issues/31#issuecomment-5743006803). No other branch or main file was overwritten. PR #50 is a separate reference implementation, not the source compiled by the theorem in #49; its correctness/evidence must not be silently attributed to this Lean compiler or vice versa.

## Integration and next obligation

The contribution has only six new, disjoint paths: two Lean modules, this note, the Lean-specific Python checker/result, and one dedicated workflow. Existing TreeSemantics, main, C029 modules, toolchain, shared workflows/imports, STATE and claim/approach ledgers are unchanged by this worker. The new modules are intentionally not added to the shared import aggregator before the integrator's acknowledgment.

A different session should read back the stated quantifiers, the total-ref fallback/support invariant, both product directions, duplicate-slot uniqueness, original index preservation, and the separation of query definitions from assumptions. Then the authorized integrator can merge and wire the agreed public interface into the normalized decision composition, rerunning the combined imports and synchronizing A018/claims/STATE. The reusable status is 'checked normalization on the pinned branch, independent statement readback and integration pending', NOT 'Problem 1.7 solved'. No optimization, broader worker launch, or ongoing background task is implied.
