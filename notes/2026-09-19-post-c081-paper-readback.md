# Post-C081 ordinary-paper readback

Date: 2026-09-19  
Reviewer: independent successor readback for issue #53  
Scope: ordinary exposition and declaration correspondence; no authorship of the manuscript

## Scope and evidence

I reviewed the manuscript at commit
[`6d8fc58`](https://github.com/mhenglein/subtail/commit/6d8fc58318940b6606c3becfef85792c0ec65086),
the declaration map and reproducible paper material at
[`609fb79`](https://github.com/mhenglein/subtail/commit/609fb798088690ae09fcc5c22b8e13e7ca36bf2d),
and the source definitions and theorem statements at the C081 source checkpoint
[`c946d86`](https://github.com/mhenglein/subtail/commit/c946d86b9e65da2877e0df42c710abbdcb5a4037).
The readback covered `paper/manuscript.md`, `paper/lean-map.json`, the mapped
P8--P17 declarations, and the P4/P5 declarations used by the composition.
The manuscript writer's ordinary argument and source files were read-only for
this review. I did not run the Lean build or claim an independent kernel replay.

## Verdict

The manuscript's P8--P14 argument corresponds to the checked definitions and
theorems at the stated source revision. I found no direct semantic contradiction
in the terminal decision route. P11 is supported by a concrete finite `budget`,
the forward coverage theorem, and reverse reconstruction; it is not merely an
unproved compiler sketch. P13 and P14 use the semantic preimage theorem and
terminal rank bound rather than the historical stronger `ClosureFor` weight
bundle.

The exposition is close to a usable mathematical proof, but it still needs
local clarification before an outside reader can reliably reconstruct the
central terminal-decision argument. The main risk is compression: several
sentences are correct only after importing details from long Lean declarations.
This is an editorial and proof-presentation finding, not a change to C081's
scientific status. No new theorem, conjecture, novelty claim, or quantitative
bound is established by this readback.

## Readback of P8--P14

### P8: terminal rank bound

The text at `paper/manuscript.md:345-358` matches
`TerminalRank.accepted_prefix_eq`, `borderState_injective`, and
`border_count_le`, with the reversal step supplied by
`RankMilestones.reversed_prefix_rank_le`. The intended argument is sound:
each border of an accepted suffix gives an accepting run from its border-start
state, and two distinct border lengths cannot start in the same state because
the corresponding accepted words are prefix-comparable. There are at most
`k` states, including the zero border, so the positive-border rank is at most
`k-1`.

Add one sentence making the mapping explicit. “Along the borders of any
accepted suffix” is too compressed and could be read as a claim about arbitrary
accepted words rather than the border-start runs of one accepted suffix. The
paper should also say explicitly that the empty border is the zero label and
that reversal turns the suffix statement into the prefix statement used later.
The code checks these details, but the ordinary proof should carry them.

### P9: milestones and first returns

The text at `paper/manuscript.md:360-381` agrees with
`RankMilestones.first_milestones_parent`,
`first_milestones_first_return`, `milestones_are_first_returns`, and
`no_return_after_maximal_rank`. The proof handles overlap and explains why the
maximum rank must be taken over all prefixes, not just the complete word.
The later completeness argument correctly uses the first milestone of that
maximum rank and obtains at most `k-2` first-return extensions after the first
letter.

For readability, define in the prose that `pi(j)` is the parent of
`R.take j` and state the domain condition `m_h,m_{h+1} <= |R|` when invoking
P9. These are implicit in the current notation and formal hypotheses but are
worth making visible in the paper.

### P10: generator and graph surgery

The text at `paper/manuscript.md:385-480` matches the word-level generator
(`FirstReturnGenerator.generator_first_hit_iff`), the graph surgery theorems
(`FirstReturnColours.first_return_graph_exact`,
`RankQueryFirstReturn.old_to_fresh`, and `fresh_edge_shape`), and the literal
`prefixGraph` definition. The one old-to-fresh entrance, forward fresh strip,
endpoint wrap, fallback to the old origin, and the `L=1` self-loop are all
represented correctly. The worked `B=0`, `C=00` example is a useful check on
the overlap convention.

One correspondence is spread across modules rather than exposed by one named
P10 theorem. The safety of the generated labels, masks, Bad/diagonal checks,
and the exact `FirstReturnExt` record are assembled in the coverage
construction (`RankQueryCoverage.Ext`, `Gen`, `SafeWalk`, and its extension
lemmas). The paper currently says that (6.1)--(6.2) “generate exactly” the
safe extensions, while the declaration map points mainly to the surgery
lemmas. Add a short cross-reference to the coverage construction and define
`FirstReturnExt` in ordinary terms: prefix extension, old-label agreement,
nonempty first return, and all safety conditions. This will stop a reader from
mistaking the word generator alone for the full labelled safe-extension claim.

### P11: semantic promotion preimage

The text at `paper/manuscript.md:482-762` is the central section and is broadly
faithful to `RankQueryCompiler`, `RankQueryEnumeration`, `RankQuerySound`, and
`RankQueryCoverage`. In particular:

* The query grammar is positive and directed. Path witnesses are independent
  except for shared clause variables; the generated intervals use one shared
  product observer. The paper does not accidentally add inverse edges,
  negative reachability, or equality of independent path labels.
* `intervalObs` has the stated finite product control. The generator state,
  next-bit lookahead, positive-step flag, and all active observer controls see
  the same emitted bit and produced colours.
* The bounds `b=3a+2sigma`, `g=2+v+2a+2sigma`,
  `r=v+2ab`, and `z=r+g+2b+a+sigma+1` match
  `RankQueryCoverage.budget`. The actual implementation enumerates a finite
  envelope and permits redundant diagrams.
* `RankQueryCoverage.coverage` supplies the forward extraction direction, and
  `RankQuerySound.compile_sound` supplies reconstruction from a satisfying
  compiled clause. `RankQueryEnumeration.preimage_iff_of_coverage` combines
  these directions into the semantic closure theorem.

The paper should state these roles at the point where it claims (7.1), rather
than requiring readers to infer them from the declaration map. It should also
say that the semantic theorem is the concrete `budget` theorem and is distinct
from the historical `ClosureFor` predicate, whose extra numerical clause-weight
conjunct is not used by P13 or P14. The current P14 caveat at
`paper/manuscript.md:842-848` is correct; moving a shorter version of it into
P11 would prevent a common misreading.

Two presentation details deserve explicit wording:

1. The `s_i+1` fresh-block estimate comes from a product-simple accepted path
   and loop erasure in the finite graph-observer product. It is not a bound on
   arbitrary accepting paths. The code's visit lemmas support this restricted
   representative, so the paper should name the restriction when introducing
   (7.2).
2. The “one common generator” claim is stronger than sharing interval
   endpoints. The reconstruction joins every interval witness through the
   shared generator state, bit, origins, marks, and seam controls. A small
   fully instantiated two-observer diagram would make this easier to verify;
   the current incompatible-bit and direction examples explain the need but
   do not instantiate all fields of one diagram.

The current text says that a diagram's origins may coincide. That is correct:
origins are matching cursors, not physical fresh positions. Positive-length
interval atoms provide the physical separation. This distinction should remain
prominent because an informal “nonmerging” statement would be false.

### P12: finishing without another return

The text at `paper/manuscript.md:765-795` matches
`RankQuery.finishQuery`, `RankQueryFinishTrace.finish_iff_no_return_completion`,
and `finish_implies_witness`. It correctly includes the endpoint `F` edge,
the `K`-only continuation, rejection of the old endpoint at subsequent
positions, and the empty completion case. The proof also separates diagonal
safety from the incoming-mask test.

Clarify the observer construction in one sentence: `Finish_I` starts at the
old endpoint's proper-border cursor and original control, then uses the
one-edge endpoint clause plus the finite continuation observer. The current
prose describes these pieces, but a reader has to reconstruct their conjunction
from the source map.

### P13: semantic unwind

The text at `paper/manuscript.md:797-812` agrees with
`RankQuerySemanticUnwind.sat_promote_preimage_iff`. The induction is genuinely
semantic: `Phi_(h+1)` is a disjunction between the shorter chain and one
first-return preimage followed by a chain of length at most `h`. No numerical
weight premise is hidden in this theorem. This is one of the clearest
paper-to-source correspondences in the manuscript.

### P14: terminal decision

The text at `paper/manuscript.md:814-848` matches
`RankQueryDecision.terminalWitnessCheck`, `milestone_chain`,
`complete_reference_promotes_finish`, `prefix_oneLetter`,
`terminalWitnessCheck_complete`, and `terminalWitnessCheck_correct`.
The algorithm handles the empty word, enumerates both first letters and all
two-label one-letter references, applies exactly `k-2` promotions, and treats
`k=0` and `k=1` separately. Completeness uses the maximum rank over every
prefix, then P9 and P12, as the ordinary proof says.

Add an explicit sentence about `prefix_oneLetter`: the two-vertex graph is a
formal one-letter reference whose labels are enumerated; labels beyond its
physical word do not matter because `prefixGraph` only exposes positions up to
that word's length. This is proved by the source theorem but is not obvious
from “enumerate all `k^2` pairs of labels.”

## P4/P5 and P15--P17 spot checks

The earlier summary construction and witness bridge are consistent with the
mapped declarations. P4's balanced/pop/normal decomposition corresponds to
`Balanced`, `Pop`, `Normal`, `reaches_iff_normal`,
`balancedCheck_correct`, and `controlReachCheck_correct`. The implementation
enumerates closed finite tables and is explicitly described as expensive; no
efficient-runtime claim is made. P5's summary automaton corresponds to
`SummaryAutomaton.witness_iff_separation` and `not_entails_iff_witness`,
including ordered cuts, diagonal flags, empty suffixes, and unsatisfiable Bad
states. I found no semantic mismatch in these sections.

The infinite branch is also aligned with the source:

* P15's monitor carrier is the finite state, phase, matching flag, and bucket
  vector, with size at most `2*k*d*2^(k*d)`. The source requires a nonempty
  cycle word (`c != []`) and the accepted-path theorem carries the safe seed,
  final/empty-column cycle hypotheses. Add these hypotheses to the ordinary
  lemma statement or point to the cycle enumeration immediately before P15.
* `PeriodicMonitor.accepts` checks `current = I.initial`. Thus the phrase
  “accept exactly monitor states whose original control is `s`” at
  `paper/manuscript.md:923` should say “the original initial state
  `I.initial`,” avoiding confusion with a generic variable named `s`.
* P16's finite extraction uses the stated `2n+d` horizon (implemented as
  `n+(n+d)`) and the concrete word `v c^(n+1)`. The manuscript's explanation
  agrees with `PeriodicRun` and `InfiniteWitness`.
* P17 enumerates safe nonempty cycles of length at most `k`, with final base
  and empty incoming column, then runs finite monitor reachability. The source
  `InfiniteDecision.prefixCheck` searches the finite monitor carrier with fuel;
  it does not impose an unproved cutoff on the prefix word.

## What this review establishes and what it does not

Established by this readback: the ordinary statements P8--P17 are materially
consistent with the mapped source definitions and theorem statements at the
recorded revisions; the main local exposition gaps are identified above.

Not established by this readback: a fresh Lean build, a fresh kernel replay,
an independent reproof of the long P11 coverage construction, publication
novelty, the C080 numerical bounds, complexity bounds, explicit-top or other
signature extensions, or a human peer review. The existing source/check logs
remain historical evidence at their pinned commits. The 25/38 native diagnostic
result and 13 timeouts remain `UNKNOWN` observations, not counterevidence to
the theorem.

## Recommended paper edits

1. Expand P8 with the border-start-state argument and the reversal/empty-border
   mapping.
2. Define the P9 parent domain and cross-reference the maximum-rank theorem.
3. Cross-reference the full safe `FirstReturnExt` construction in P10.
4. State in P11 that `coverage` and `compile_sound` are the two directions of
   the concrete semantic theorem, and distinguish it from `ClosureFor` there.
5. Add one complete finite diagram example to P11, including shared generator
   coordinates and positive interval seams.
6. Clarify the P12 observer/endpoint conjunction and the P14 one-letter graph
   enumeration.
7. State the nonempty-cycle and `I.initial` hypotheses in P15.

These are bounded exposition improvements. They do not justify changing C081
from its current qualitative status or promoting any quantitative claim.

## Status and handoff

Status: `READY_FOR_INTEGRATION` for this readback. The only owned writes are
this note and the small correction in
`notes/prior-work/c081-review-2026-09-19.md`; no paper, Lean, ledger, or
experiment files were modified. The novelty correction separately records
that NP03 cap universality is a characterization of the full-signature
problem, not an established decision theorem, so a reduction there would not
by itself prove decidability.

