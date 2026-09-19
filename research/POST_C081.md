# Post-C081 programme

Started: 2026-09-19. Updated: 2026-09-20. Owner: Marcus. Coordination: [#53](https://github.com/mhenglein/subtail/issues/53), integration [#37](https://github.com/mhenglein/subtail/issues/37).
Starting checkpoint: `c946d86b9e65da2877e0df42c710abbdcb5a4037`.

The qualitative decision theorem C081 is complete at this checkpoint. This
programme explains, compares, analyses and improves that result. It does not
silently strengthen its signature, tree domain, complexity or quantitative bounds.

| Order | Deliverable | Acceptance criterion | Current state |
|---|---|---|---|
| 1 | Ordinary mathematical paper | Full terminal preimage construction and proof, exact semantic bridge, infinite branch, termination, worked examples and checked-declaration map; independent exposition readback | Ordinary draft and follow-up exposition readback complete |
| 1 | Focused novelty review | Primary-source theorem matrix; backward/forward citation trail; exact new/inherited/uncertain statements; recorded search limits | Focused source comparison complete; priority and exact transfers remain uncertain |
| 2 | Complexity | Explicit effective resource bound with input encoding and algorithm identified; independent readback of quantitative proposals; lower-bound transfers proved or left conditional | C082 quantitative source reviewed and freshly checked; complete input accounting is under review |
| 3 | Usable verified algorithm | Measured costs, at least one meaningful proved improvement, small interface, sound status handling and explanatory examples; failure evidence independently checked where supplied | Global safe-reference gate implementation and proof active; interface remains |
| 4 | Explicit-top study | Exact problem, proof-dependency audit, tested reductions/obstructions and a feasibility conclusion with remaining obligations | Feasibility study complete; naive encodings fail, new label-aware semantics needed |
| 4 | Other transfers | Separate arguments or counterexamples for regular/finite trees, arities, constructors and variance; standalone automata results identified | Regular-transfer ordinary proof and boundary map independently reviewed; new signature theorems remain open |
| 5 | Reader package and checkpoint | Consistent README/paper/proof map, reproduction, issue disposition and immutable checkpoint; metadata accurately records licensing/authorship status | Published 29cda9a, all four CI runs PASS; tag c081-research-2026-09-20 verified |

Marcus chose **licensing pending** and **author/affiliation placeholders**.
Do not add a license grant, assign human authorship, or describe the checkpoint
as publication-ready. Supplied papers remain unchanged and outside any proposed
license for original material. This owner-deferred decision does not block
research, reproducible drafts or a labelled research checkpoint.

## Proof route for the exposition

Exact input: finitely many inequalities between finite expressions over a finite
variable set, bottom and one covariant binary product. A valuation assigns
arbitrary prefix-closed subsets of binary words, including nonregular infinite
trees. The output decides universal entailment, with no satisfiability premise.

The checked route is:

1. Exact fresh naming reduces expressions to four normalized constraint forms.
2. Least propagation models turn non-entailment into a finite separating address.
3. Finite balanced stack summaries give an absorbing flagged-word instance.
4. Safe extension splits its witnesses into a terminal branch and a branch with
   a safe cyclic continuation.
5. Terminal witnesses have bounded **border rank**, not bounded word length.
   First returns extend a prefix graph by a directed strip with one entrance.
6. A finite diagram compiler eliminates a whole positive path-query conjunction
   through that extension. One generator per physical interval preserves shared
   words. Both coverage and reconstruction are required.
7. At most `k-2` semantic promotions, evaluated on one-letter references, decide
   the terminal branch. A finite reverse periodic monitor decides the other.
8. Negating the disjunction and undoing naming proves the original theorem.

Each implication above is already checked at the starting checkpoint. The
exposition must explain the construction, not replace a proof with a declaration
name. The main new writing risk is mistranslating the large preimage proof or
its quantifiers; an independent readback is an acceptance gate.

The former `ClosureFor` bundles semantic closure with a numerical bound. The
qualitative proof uses the semantic part proved separately. The old universal numerical weight bound for the concrete compiler is now
refuted. C082 records the separately proved larger bound. The original F
alone and an existential smaller compiler remain open. Exact source/readback
and fresh combined checks are in the [integration note](../notes/2026-09-20-post-c081-quantitative-integration.md).

## Experiments and review

Prioritize shared-generator conflicts, repeated traversal of one interval,
overlapping returns, an endpoint return, equal physical marks with different
roles, equal origins at distinct marks, empty paths and nonprimitive periods.
Worked examples should be checked by literal word/tree definitions.
Source links and dependency maps are checked against actual declarations and
imports. Existing Lean results are attributed to their original checked revisions;
documentation checks are not relabelled as fresh kernel replay.

For explicit top or other extensions, keep both decision and obstruction routes
open. A failed encoding refutes that encoding, not the extension. Ordinary
semantics and small falsification come before substantial new formalization.

Execution ownership is recorded in the approach registry and concrete issue
claims. This programme lists future deliverables; it does not reserve every path
or imply all investigations have started.

## Checkpoint evidence and next work

- [Ordinary paper](../paper/manuscript.md), [source map](../paper/lean-map.md),
  [initial and follow-up exposition readback](../notes/2026-09-19-post-c081-paper-readback.md).
- [Focused novelty review](../notes/prior-work/c081-review-2026-09-19.md): inherited,
  candidate-new and uncertain claims, exact signatures, backward/forward trail.
- [Complexity investigation](../notes/2026-09-19-c081-complexity-review.md): an
  alternative terminal enumerator using the corrected C082 Fhat
  theorem; [independent accounting corrections](../notes/2026-09-20-post-c081-cost-readback.md).
  Complete normalization/summary costs and lower-bound transfers remain open.
  The separate guarded NP99 reduction supplies a PSPACE upper bound only for
  inputs without bottom constants; no implementation bound follows from it.
- [Extensions](../notes/2026-09-19-post-c081-extensions.md) and
  [readback](../notes/2026-09-19-post-c081-extension-readback.md): explicit NFA
  construction for regular countermodels, finite/top/variance obstructions and
  the remaining arity/label obligations. E053 is bounded evidence only.

The next implementation target is a measured, proved improvement to the actual
entailment entry point, followed by a small input/output interface. Reuse the
E052 cases and preserve UNKNOWN on resource exhaustion. Investigate the repeated
closed-table enumeration in `StackSummary.balancedCheck`, the eager summary
carrier, and obvious source-level implications before choosing an optimization.
A small guarded example running successfully does not validate backend speed.
The regular construction gives a route to finite countermodel output, but no
extractor or verified optimized interface has been implemented in this checkpoint.

Quantitative #48 is integrated through its exact released files with the corrected
C082 status; #47 preserves its discovery argument. Direct-realization #51 and preserved
advisory notes #44/#45 remain separate contributions. Their open disposition is
intentional: the paper checkpoint does not integrate, discard, or certify their
unique content. Reconcile each exact patch and its released scope before closing
its issue or branch. No branch is retired by this programme update.
