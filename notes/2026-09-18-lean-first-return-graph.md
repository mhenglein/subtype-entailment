# Lean: exact first-return graphs and the query-path interval bound

Date: 2026-09-18. Workstreams A018/A017. Issues #26, #28; tracker #34.
Author: ChatGPT, continuing the original stage-3 formalizer session.
Integration base: `0e9ab725cb73719353459d319a485d39675f228d`.
Prior graph source: `11539a544ba6a5bc6a848ca4737ec124f3171ffa`.
Checked query-interface source: `57896b5610ac296498bf41dd287b7e874af7aace`.

**Kernel-checked graph identities and a bounded observer-path interface. Not a
proof of the uniform preimage compiler, the global witness bound, or subtype
entailment. C080 remains a candidate.** This formalizes dependencies in the
existing candidate argument, not a claim of a new complete decision theorem.

## 1. What was completed

The four stage-3 modules now establish the exact local graph construction,
including its converse word-generation condition:

- [PrefixMatching.lean](../lean/Subtail/PrefixMatching.lean): matching is a
  finite maximum of literal suffix candidates; maximum, matching, fallback and
  prefix-stability equations are derived rather than postulated.
- [FirstReturnGraph.lean](../lean/Subtail/FirstReturnGraph.lean): the old-graph
  cursor computes every new failure parent; every K edge satisfies the local
  construction, including old-end redirection and new-end wrap.
- [FirstReturnGenerator.lean](../lean/Subtail/FirstReturnGenerator.lean): the
  old-graph first-hit predicate is equivalent to literal first return. The
  converse does not assume the very word-border property being reconstructed.
- [FirstReturnColours.lean](../lean/Subtail/FirstReturnColours.lean): all five
  colour fields and every F/S/K0/K1 edge agree, for every vertex. Literal border
  masks include both empty and full borders. Each fresh mask is its original
  state's flag column OR the mask at its old-graph cursor. The local guard is
  exactly the corresponding full-mask clearance test.

The exported equality is `first_return_graph_exact`; `generated_graph_exact`
uses the generator-side premise. Inputs are an actual binary word, a nonempty
old prefix, a literal first return, arbitrary original-state labels and flags.
Safety is unnecessary for these structural identities; they apply in particular
to safe references. They do not by themselves supply a safe reverse run or the
full `FirstReturnExt` reconstruction from a compiled query.

Graphs have exactly `word.length + 1` vertices. Numeric positions are not colour
fields. Function-valued masks here and vector masks below describe the same
finite set of original states. No source/target flag direction is changed.

## 2. Connecting to the other agent's actual query semantics

The separately delivered [RankQuery.lean](../lean/Subtail/RankQuery.lean) and
[RankQueryPaths.lean](../lean/Subtail/RankQueryPaths.lean) remain byte-unchanged.
Their `Graph`, `Observer`, `Run`, `Accepts`, `SafeReference`, `FirstReturnExt`,
`Sat` and pinned `ClosureFor` are reused, not replaced by a competing model.

[RankQueryFirstReturn.lean](../lean/Subtail/RankQueryFirstReturn.lean) proves:

1. `advance_eq`: the query module's literal longest-prefix/suffix maximum equals
   the stage-3 border-based maximum at every valid vertex and either letter.
2. `mask_get_eq`, `colour_eq_surgery`: the incoming masks and all colour fields
   coincide under the explicit function-to-vector conversion.
3. `edge_eq_surgery`: each directed edge of `RankQuery.prefixGraph` has exactly
   the destination given by the verified surgery row.

Consequently subsequent query proofs can use the graph theorem on the literal
`prefixGraph` occurring in `ClosureFor`; no unproved identification between two
similar graph encodings is left at this interface.

## 3. The single entrance and the s+1 bound

Let the old word length be m and the first-return word length be n, with
0 < m < n. Fresh vertices are precisely m+1,...,n.

`fresh_edge_shape` proves, on the literal query graph, that an edge with a fresh
destination v satisfies either v = u+1 or (u = n and v = m+1). In particular:

- every old-to-fresh edge is m -> m+1 (`old_to_fresh`);
- every failure link lands in the old portion (`parent_le_old`);
- every fresh transition which is not a physical forward continuation lands at
  m+1 (`fresh_break_target`). This includes the endpoint wrap and its singleton
  self-loop case.

`freshIntervals` is an executable count of maximal physical-forward fresh
sections of a node list. A section begins at an initially fresh node, or when a
step enters the fresh part without continuing from another fresh node to its
immediate physical successor. A wrap starts a new section even when it lands on
the same physical vertex. The count refers to actual vertices, not their colours
or old-graph cursor values; equal cursors do not collapse distinct positions.

The theorem `breaksAfter_le_visits` charges every section start except the initial
one to a later visit of m+1. Combining it with the other agent's proved
`accepts_bounded_visits` gives `accepts_bounded_fresh_intervals`:

    Accepts (prefixGraph I B) O u v ->
    there is an allowed product-simple chain with the same accepted endpoints
    whose number of maximal forward fresh sections is at most O.size + 1.

There is NO reference-length or extension-length parameter in this bound.
There is no assumed path-length cap, finite diagram family or closure theorem.
An accepting path is simplified only in the fixed product of this graph and
this observer, preserving the actual endpoints and allowed controls.

The theorem is stated for all first-return words and arbitrary finite observers,
including colour-dependent moves. Safe/terminal instances are a subclass; those
extra hypotheses are not needed for this path-shape argument. This is the
bounded fresh-section ingredient of the candidate's diagram proof, not the full
diagram proof or shared-word synthesis construction.

## 4. Discriminating examples and regression scope

The separate [checker](../experiments/check_rank_query_first_return.py) constructs
edges by literal suffix comparisons and partitions paths independently by their
node indices. It checks 258 distinct first-return words/old-prefix choices with
whole-word length at most 9, 8,822 directed edges, 86,408 product-simple paths of
at most five edges, and 2,000 arbitrary-list partition/count comparisons.

The +1 is material. For old word `0` and first-return word `010`, a colour guard
`End OR (not Root AND next = 0)` allows precisely fresh vertices 2 and 3. An
s-control observer with K1 preserving control and S increasing it has the forced
accepted path

    (3,0), (2,0), (3,1), (2,1), ..., (3,s-1), (2,s-1).

It has s+1 forward fresh sections. The checker exhausts every permitted next
step on this entire guarded path for s=1,...,8. These are structural graph toy
fixtures, not claimed safe terminal-instance witnesses.

The first-return premise is also necessary for this statement. On word `0000`
with m=1, the product-simple one-control F path 4 -> 3 -> 2 has three fresh
sections, exceeding 1+1. This word is NOT a first return of its initial `0`.
This rejects dropping the hypothesis, not the candidate's stated argument.

With `--lean`, the checker evaluates the actual Lean `freshIntervals` definition
on the 2,009 retained lists and compares it with the explicit partition. It
reports native PASS only after successfully executing the pinned toolchain.
Without that flag it explicitly reports NOT_RUN. Word/path bounds are finite
regression coverage, not the all-word justification for the Lean theorems.

## 5. Evidence and limitations

The original complete graph source passed run
[35311455230](https://github.com/mhenglein/subtail/actions/runs/35311455230).
The new source at `57896b5610ac296498bf41dd287b7e874af7aace` passed run
[35328724436](https://github.com/mhenglein/subtail/actions/runs/35328724436):
default build, explicit query-interface target, bundled kernel replay, every
public declaration's dependency-axiom audit, native/literal graph comparisons,
the original RankQuery differential, the earlier Lean core and its unchanged
saved result, and canonical research-index validation.

The 16 new interface declarations contain no unfinished proofs or custom
research axioms. Runtime definitions reject Classical.choice and native axioms;
proofs permit only the project's standard logical axioms. The initial bridge
drafts needed proof-script reductions for Fin/Option/Vector values, explicit
reflexivity and recursive arithmetic; target statements and assumptions were
not weakened. Failed builds are retained in branch history.

The additional finite interface checker was executed in Python locally. Its
native Lean execution and later integration workflow must be checked at the
revision being reported; merely committing that new test does not establish
that it ran. Lean runs described here used the repository runner, not a local
Lean installation in the chat container. `leanchecker` reuses Lean's kernel;
it is not an independent external kernel implementation. Statement readback
was by the author, not an independent human semantic referee.

## 6. Exact next obligations

The bridge is ready for the central compiler formalization. Preserve the pinned
`RankQuery.ClosureFor` statement and implement the actual finite preimage map.

First, use the s+1 chain bound to construct the complete ordered mark/diagram
representation, including coincident vertices, disequalities, crossings,
old-core pieces and endpoint wraps. Prove coverage by the executable enumerator,
not only that an abstract bounded representation exists. The arithmetic target
is at most v+2+2*sum(s_i+1) physical marks for a clause with v variables.

Second, every physical interval must have ONE generator word shared by all its
active observations. Construct the interval-product observer and prove both
sound reconstruction and complete capture against the same labelled extension.
Different interval observations must not silently choose independent words.
Nonempty adjacent intervals and complete boundary-control agreement matter.

Third, prove the compiler's output has the same finite syntax, its explicit
weight bound, and repeated-closure correctness. Finally instantiate the global
witness bound and connect to the original arbitrary-tree subtype semantics.
None of these later results is assumed or promoted by this contribution.

```sh
cd lean
lake build +Subtail.RankQueryFirstReturn
lake env leanchecker Subtail.RankQueryFirstReturn
cd ..
python3 experiments/check_lean_first_return_graph.py --repository --lean --output /tmp/graph.json
python3 experiments/check_rank_query_first_return.py --lean --output /tmp/query-first-return.json
python3 scripts/check_lean.py
python3 scripts/research_index.py --check
```
