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
| 2 | Complexity | Explicit effective resource bound with input encoding and algorithm identified; independent readback of quantitative proposals; lower-bound transfers proved or left conditional | Reviewed ordinary full-input time/space bound using checked C082; C083 proves an NL lower bound; tight class remains open |
| 3 | Usable verified algorithm | Measured costs, at least one meaningful proved improvement, small interface, sound status handling and explanatory examples; failure evidence independently checked where supplied | Equality-proved global gate, capped JSON CLI and exact graph checker complete; matched E054 improves 22/38 to 24/38 with 14 UNKNOWN |
| 4 | Explicit-top study | Exact problem, proof-dependency audit, tested reductions/obstructions and a feasibility conclusion with remaining obligations | Feasibility study complete; naive encodings fail, new label-aware semantics needed |
| 4 | Other transfers | Separate arguments or counterexamples for regular/finite trees, arities, constructors and variance; standalone automata results identified | Regular-transfer ordinary proof and boundary map independently reviewed; new signature theorems remain open |
| 5 | Reader package and checkpoint | Consistent README/paper/proof map, reproduction, issue disposition and immutable checkpoint; metadata accurately records licensing/authorship status | Published paper checkpoint 29cda9a, all four CI runs PASS; tag c081-research-2026-09-20 verified; later source checks and exact issue dispositions recorded below |

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
claims. These deliverables are research results and feasibility studies, not
proofs that all extensions or performance questions are solved. Follow-up
proposals do not reserve paths or launch workers.

## Checkpoint evidence and next work

- [Ordinary paper](../paper/manuscript.md), [source map](../paper/lean-map.md),
  [initial and follow-up exposition readback](../notes/2026-09-19-post-c081-paper-readback.md).
- [Focused novelty review](../notes/prior-work/c081-review-2026-09-19.md): inherited,
  candidate-new and uncertain claims, exact signatures, backward/forward trail.
- [Full original-input resource account](../notes/2026-09-20-c081-input-complexity.md):
  an explicit total-recursive time/space bound for a specified reference
  algorithm using C082, including summary construction and bit arithmetic.
  Independent accounting review found no remaining blocker. This is ordinary
  mathematics, not a Lean complexity theorem or native runtime estimate.
  [C083](../notes/2026-09-20-reachability-lower-bound.md) gives a separately
  reviewed logspace reachability reduction and NL lower bound. The guarded
  NP99 PSPACE upper bound covers only inputs without bottom constants.
- [Solver and checked optimization](../notes/2026-09-20-c081-solver.md): an
  optional equality-proved gate, native JSON CLI, incomplete regular-model
  explanation search and exact Python graph checker. Native build/kernel/
  dependency checks and current 16-test boundary suite pass. Matched E054
  gains two direct raw-backend cases (22/38 to 24/38), with no wrong answer
  and no new full-expression completion. Fourteen cases remain UNKNOWN.
  [Exact revision/hash/timing receipts](../results/entailment-lazy.json).
- [Extensions](../notes/2026-09-19-post-c081-extensions.md) and
  [readback](../notes/2026-09-19-post-c081-extension-readback.md): explicit NFA
  construction for regular countermodels, finite/top/variance obstructions and
  the remaining arity/label obligations. E053 is bounded evidence only.

The most useful next implementation question is whether cached balanced
reachability or a smaller summary representation can reduce the unchanged
full-expression timeouts. A complete regular-countermodel extractor remains
open; the current candidate library is deliberately incomplete. Other next
questions are tighter complexity, external mathematical review and explicit-top
label semantics. The [current plan](PLAN.md) gives distinct follow-up targets.

## Issue and branch disposition

Remote states and exact heads were read on September 20. None of these
dispositions certifies unreviewed unique content or retires a branch.

| Item | Exact source or head | Disposition |
|---|---|---|
| #48 quantitative proof | `881d4beeb903d679d7d36a8a9abc2aa0efa60a52` | Closed as integrated in main `98bbcde`; exact source files retained, isolated workflow folded into the shared Lean job. Branch retained. |
| #47 ordinary counterexample | `42be43f35a98d4d23a4ba26439833730bbcd6510` | Open historical discovery/proof evidence. C082 supersedes the old bound; unique experiment/notes remain preserved for separate patch reconciliation. |
| #44 semantic audit | `99d951077ace1c93d0fec604839674fb3f19dbc9` | Open advisory note. Not newly certified or integrated by this programme; retain for a separate provenance/readback pass. |
| #45 normalization advisory | `c33d0c8d65158fc7ba53e5bc24c14132f071dc42` | Open advisory note. The final normalization proof is on main; this note's unique observations are retained for separate reconciliation. |
| #51 direct realization | `db55acded6064b12d5d483216e29653ae3d884f3` | Open optional C030 converse certification. Outside the required forward C081 proof; no integration or independent validation is claimed here. |
| #30 and #34 quantitative tracking | Main `98bbcde` correction | Remain open for original F alone and an existential smaller compiler. Their bodies distinguish the refuted old concrete U from C082. |
| #37 integration coordination | Main and scoped release comments | Remains the shared coordination record; this session releases its lease after final checked publication. |
| #53 this programme | Source and publication receipts in comments | The seven requested deliverables are covered at the stated evidence levels. Final main CI and release are recorded in the issue; licensing/authorship remain owner-deferred. |

All worker scopes used in this episode were explicitly released. Other
workspaces' uncommitted files, stashes and unpushed work were not audited;
there is no claim that every historical local artifact has been recovered.
