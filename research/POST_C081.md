# Post-C081 programme

Date: 2026-09-19. Owner: Marcus. Coordination: [#53](https://github.com/mhenglein/subtail/issues/53), integration [#37](https://github.com/mhenglein/subtail/issues/37).
Starting checkpoint: `c946d86b9e65da2877e0df42c710abbdcb5a4037`.

The qualitative decision theorem C081 is complete at this checkpoint. This
programme explains, compares, analyses and improves that result. It does not
silently strengthen its signature, tree domain, complexity or quantitative bounds.

| Order | Deliverable | Acceptance criterion | Current state |
|---|---|---|---|
| 1 | Ordinary mathematical paper | Full terminal preimage construction and proof, exact semantic bridge, infinite branch, termination, worked examples and checked-declaration map; independent exposition readback | Drafting |
| 1 | Focused novelty review | Primary-source theorem matrix; backward/forward citation trail; exact new/inherited/uncertain statements; recorded search limits | Active separate investigation |
| 2 | Complexity | Explicit effective resource bound with input encoding and algorithm identified; independent readback of quantitative proposals; lower-bound transfers proved or left conditional | Active separate investigation |
| 3 | Usable verified algorithm | Measured costs, at least one meaningful proved improvement, small interface, sound status handling and explanatory examples; failure evidence independently checked where supplied | Planned |
| 4 | Explicit-top study | Exact problem, proof-dependency audit, tested reductions/obstructions and a feasibility conclusion with remaining obligations | Planned |
| 4 | Other transfers | Separate arguments or counterexamples for regular/finite trees, arities, constructors and variance; standalone automata results identified | Planned |
| 5 | Reader package and checkpoint | Consistent README/paper/proof map, reproduction, issue disposition and immutable checkpoint; metadata accurately records licensing/authorship status | Planned |

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
qualitative proof uses the semantic part proved separately. The old numerical
bound, its concrete-compiler counterexample, a replacement bound, and the
original witness formula must remain distinct during review of #47/#48.

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
