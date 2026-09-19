# Separate review of the proposed rank-query closure proof

**September 20 correction.** The old universal weight estimate
`64*k*T^(2*T+2)` is false for the concrete enumerator: a checked terminal
five-state counterexample emits a larger clause. The semantic compiler and
qualitative C081 decision remain checked. C082 proves the separate replacement
`64*k*T^(6*T^2+2)` and the resulting Fhat witness bound. The original F by itself
and a smaller existential compiler are not refuted. Earlier unqualified size
arguments and reviews below are superseded at precisely that point; the text
is preserved as history. [Exact correction and dependency audit](2026-09-20-post-c081-quantitative-integration.md).

Date: 2026-09-17. Reviewed commit: `8b3ac145c67a1f7dabcc7173d76e8f14cca7a27a`.
Workstream A017; support for the other investigation's proposed resolution.

**Assessment: the reviewed terminal rank/graph/closure/size arguments are supported
at ordinary-proof review level. No substantive counterexample or missing
implication was found in that scope. This is not Lean verification, a human
mathematical referee, or a fresh audit of the complete subtype semantic bridge.**
The project's accepted Problem 1.7 status and all C/Q evidence labels are not
promoted by this review. No additional agents were launched.

The subject is the [September 17 closure proof](2026-09-17-rank-query-closure-audit.md)
and its `rank_preimage.py` / `rank_preimage_core.py` implementation. The author
supplied the argument first; this later investigation read it and constructed
a different finite-state oracle. Thus this is a separate audit informed by the
candidate, not a blind independent discovery of the same proof. The five
reviewed implementation/dependency files remain byte-for-byte unchanged.

## 1. Publication and choice of target

The earlier C079/E051 target-return contribution was already published in
`47adf83c194aa941b525240f6470f3d77a69f81d`. The reviewed main contains that commit
as an ancestor; no duplicate push or replacement of that contribution is needed.
Main then added the rank prerequisites, candidate and symbolic compiler.

The new candidate does not assume return closure, a short power scheme, a
polynomial source-visit bound, or a finite quotient of exact reference words.
Its target is instead closure of existential finite-colour regular-path queries
under a first-return graph extension. A bounded number of promotions then gives
an explicit, potentially enormous witness bound. Reviewing this closing lemma
is more useful than extending the older restricted target-return solver again.

The complete ordinary argument has six logical stages:

1. Terminality bounds the depth of the reversed prefix's border chains.
2. Successive first rank milestones are first returns of the earlier reference.
3. A first return has the stated core/forward-strip graph description.
4. Any successful finite query has a bounded portal diagram, and each diagram
   compiles in both directions while preserving one generated reference.
5. The output stays in the same query grammar, with the stated computable size
   bound; repeated preimages and shortest interval paths give the witness bound.
6. The pre-existing C029/C031 and forward semantic characterization transfer
   the terminal result to the original arbitrary-tree subtype question.

This review addresses stages 1-5 and specific implementation interfaces. Stage
6 is a named outstanding independent review task, not a hypothesis silently
verified by testing the terminal code. Existing recorded proofs of that bridge
are neither rejected nor newly certified here.

## 2. Review of rank and graph representation

Work with a **nonempty** safe labelled reference B of length m. This restriction
is explicit in the code and is needed for the first-return construction; the
original empty-word case is handled separately. A reference is a reversed safe
terminal path, not necessarily a complete witness ending at the original start.

### Border depth and milestone parent

Distinct comparable terminal suffixes cannot start in the same original state.
Otherwise reading the shorter accepted continuation from the earlier equal
state reaches the terminal final before the longer defined run ends. Including
the empty border, a chain therefore has at most k vertices; the positive-prefix
depth is at most k-1.

Let n be the earliest prefix with depth h+1, and m the earliest prefix with depth
h. Its longest proper border j has depth h, hence j>=m. If j>m, the copy of the
length-j prefix ending at n contains a copy of B ending at n-j+m<n. That earlier
prefix has a length-m border and therefore depth at least h+1, a contradiction.
Thus j=m. Conversely an earlier complete return of B would itself have created
depth at least h+1. This establishes the first-return property, including an
overlap and a return occurring at the ultimate accepting cut.

### Why no longer hidden failure parent exists

Before the first return of B, a new prefix cannot have a proper border longer
than m. Such a border starts a noninitial copy of B that completes before the
current end. At the returning endpoint the same argument excludes a proper
border longer than m, and the complete return supplies border m. Therefore the
new failure parents are exactly the old-graph KMP origins in the candidate.
The new mask is the origin's border mask union the new state's incoming column.

All changes to old vertices are confined to the old endpoint: its next-bit/end
colour changes and its matching K edge is redirected into the fresh strip. A
fresh interior has a forward S edge and matching K edge, with F and mismatch
edges into the fixed old graph. The fresh endpoint has its F exit, mismatch
exit and the single matching wrap to the first fresh vertex. These assertions
remain valid for a one-vertex strip, where the wrap is a self-loop.

This gives the decisive directional invariant: later generation never creates
an edge into an arbitrary previously generated fresh interior. It can address
only the old core, the first fresh vertex, or the next/current fresh vertex.
The review does not assume this for arbitrary graph extensions or inverse edges.

## 3. Review of the uniform query-preimage argument

### A graph-size-independent diagram bound

For an atom with s observer controls, shorten a successful path by deleting any
repeated (graph vertex, observer control) configuration. This preserves its
endpoints, transition-colour tests and observer acceptance. Other query atoms
share only explicitly quantified vertices, not this path's internal history.
The resulting path visits the first fresh vertex at most s times, and has at
most s+1 fresh excursions, counting an initial excursion starting elsewhere.

The resulting bound on marked variables, strip endpoints and excursion ends
is independent of B's length. The finite enumerator need not know a particular
reference, origin address or successful word. Allowing additional nonsimple
realizing paths in a compiled clause is harmless: they still satisfy an
existential path atom.

### One physical interval, not independent generated words

All fresh marks are put in one weak order; coincidences mean the same physical
position. Distinct marks are separated by positive-length generator paths.
Their old origins need not be distinct. For example, two different fresh
positions can both fail to the old root. Treating unequal physical marks as
unequal origins would be an incorrect extra restriction.

Split every forward observation at every mark it crosses. On each resulting
physical interval, keep one actual reverse-state generator and all observing
controls in one product. Every coordinate sees the same actual bit and the
same produced source/target colours. It may independently choose S or the
matching K edge because both edges describe that same physical step; the query
never required its observers to choose identical edge-label sequences.

The boundary original state and guessed next bit are shared between adjacent
intervals. The next move consumes that very bit. The final origin is the old
endpoint; an intermediate origin is not. The generator forbids leaving End,
so a hidden earlier full return is impossible. A one-emission strip is treated
separately and does not accidentally require a positive intervening interval.

### Both closure directions

From a genuine extension and query models, take product-simple paths and their
actual marks, order, original states, origins, next bits and seam controls.
These instantiate one enumerated diagram. Core paths, portal edges and each
shared interval satisfy its compiled atoms. No arbitrary state-summary
substitution is used in this direction.

Conversely fix ONE model of a compiled diagram on ONE base graph. Select one
witness path for each physical interval atom and concatenate them with the first
emission. Shared boundary controls and origins guarantee a consistent reverse
run, and the first-return guards give one safe extension. Place old variables
at their chosen old vertices and fresh variables at the generated physical
marks. Mapped core observers use the actual recoloured old endpoint; portals
are genuine graph edges; the interval product supplies every forward observation.
All observer controls match at seams. The original clause therefore holds on
this one extension, not on a collection of separately chosen extensions.

No extra consistency obligation between different core stretches is missing:
the original query asks only for separate existential paths on the same old
graph with shared named endpoints. It does not equate their path labels.
Fresh/core equalities are impossible; fresh equalities are mark coincidences;
core equalities remain explicit constraints. Zero-length paths require an
allowed colour and an observer control that is both initial and final.

### Why repeated compilation stays in the language

The implementation's Map, Test and Observer descriptions form finite acyclic
syntax trees. A new constructor references already supplied finite objects;
none calls graph reachability, generates a string, or inspects an unbounded
position from inside a colour predicate. Their inputs are one or two members
of the fixed finite colour alphabet and finite controls. Consequently their
semantics can be expanded to finite tables before another compilation.

The core map changes only an End-coloured vertex. Fresh colours depend on one
origin colour plus fixed original-state/next-bit guesses. A portal predicate
combines only such finite maps. The apparent lookahead and nested predicates
therefore introduce neither a hidden register nor a negative reachability test.
This checks the self-application contract, rather than assuming that a compiler
for the initial finishing query automatically works on its own output.

## 4. Quantitative review

For input weight T=max(2,1+v+a+sum s_i), the candidate's constants safely bound
marked positions, core pieces, old variables and portal atoms. There are at most
6T interval products. At most 2T observer coordinates occur in one such product,
each of size at most T, alongside 6k generator controls. Core-observer states
contribute at most 2T^2 and the one-edge atoms contribute at most 4T+4 states.
Thus the loose output weight bound

    U_k(T)=64*k*T^(2T+2)

covers the construction. The number of disjuncts can be much larger and is still
finite. It need not be included in the size of a particular satisfied clause.
Finite unary predicates can be normalized to finite-colour tables; their syntax
size is not being smuggled into an unbounded graph oracle.

The finishing query has weight k+8<=T_0=k+10. Let T_(j+1)=U_k(T_j). On an old
graph with m+1 vertices, fix the satisfying mark assignments and endpoint
control tuples before shortening paths. Each physical interval can then use
a shortest observer-product path. The sum of their lengths is at most
(m+1) times the sum of their observer state counts, hence at most (m+1)T_j.
The seen bit preserves positive length. Together with the first emission and
old vertices, the new reference has at most (m+1)(T_j+2) vertices.

Unwinding at most k-2 preimages from a two-vertex initial reference and then
using a shortest k-state finishing-observer path gives the candidate bound

    F(1)=0,
    F(k)=2*(k+1)*product_(j=1..k-2)(T_j+2), k>=2.

The empty product and one-state case are consistent. A branch with fewer
promotions fits the same larger bound. Shortening takes place only AFTER the
shared interval products and their boundary controls have been fixed, so it
is not the unsound independent replacement of words with equal transition
actions refuted in earlier investigations.

Under the reviewed closure argument this is an explicit terminal decision
proof. The bound is not remotely a practical search recommendation, and this
review does not claim that the generic capped driver has solved the historical
hard fixtures. It is important not to replace an enormous finite construction
with a small test cutoff and then report mathematical NO.

## 5. A different all-length fixed-reference oracle

[rank_frontier_oracle.py](../experiments/rank_frontier_oracle.py) independently
decides the following restricted audit question: for a SUPPLIED concrete safe
nonempty B and supplied query, does any safe first-return extension satisfy it?
It never invokes the symbolic diagram enumerator, compiler, candidate query
CSP or candidate path-search function. It retains the entire concrete old graph,
so it is deliberately NOT a uniform preimage construction and supplies no
alternative unrestricted proof by itself.

### Finite state and transitions

Generate one extension online. Retain the m+1 old vertices, first fresh vertex,
current fresh vertex, and every fresh vertex already assigned to a query
variable. With v variables there are at most m+v+3 retained vertices. Store
the actual current state, old KMP origin, first bit, next-bit guesses, retained
colours and partial variable assignment. A variable is assigned either to an
old vertex initially or to a fresh vertex when that vertex is created. Several
variables may select the same vertex; equalities and disequalities are checked.

For each atom store the full reflexive-transitive reachability relation between
retained (vertex, observer-control) pairs. A generated step adds its graph edges
and saturates every relation by bit-matrix Warshall closure. Once the previous
current vertex is neither first nor named by a variable, forget it by restricting
the saturated matrices to the retained configurations. All matrices are updated
by the SAME generated bit, actual-state transition and vertex-colour choices.

The old graph, finite colour set and boundary size are fixed. Matrix dimensions
are bounded by (m+v+3)s_i for atom i, giving finitely many Boolean matrices and
assignments. Hence exhaustive search of these states terminates. Explicit caps
or host resource limits return UNKNOWN. Terminal endpoints do not generate
further letters. Acceptance requires every variable assigned, every unary and
identity constraint true, and an accepting control-pair in each atom's matrix.

### Exact forgetting invariant

The matrices represent exactly all paths in the graph generated so far, with
both endpoint configurations retained. When a vertex is forgotten, every path
through it is already represented by the saturated relation. No later edge can
address that forgotten vertex: the graph-surgery invariant in Section 2 permits
future attachment only to the old core, first fresh and then-current vertices,
all of which are retained. Adding future edges and resaturating therefore gives
exactly the same boundary reachability as retaining the entire generated graph.

Choosing variable values at creation is complete: any full satisfying assignment
can make those same choices as its vertices arrive. Conversely a final summary
corresponds to the one path of generator choices used to reach it, so all its
atom matrices refer to one actual reference. Merging identical summaries is
sound under this invariant, without identifying arbitrary reference words in
the uniform candidate construction.

This proves the all-length YES/NO scope of this separate oracle for a FIXED B.
It shares the original finite observer semantics and literal prefix-graph
construction; those are explicit common dependencies, not claimed independent
implementations of every definition. Its graph reachability and query assignment
mechanisms are separately written. Positive results are checked again on the
fully materialized literal graph.

## 6. Executed evidence and exact limits

[check_rank_closure_review.py](../experiments/check_rank_closure_review.py), seed
20260917113, records the following in
[results/rank-closure-review.json](../results/rank-closure-review.json).

* All 16 subsets of {F,S,K0,K1}, used as a one-state end-to-root observer,
  are compared on seven fixed bases: 112 complete all-length questions,
  84 YES and 28 NO. All 16 syntactic preimage unions are completely enumerated,
  emitting 52,992 clauses in total. There are 127,806 clause/base evaluations.
  Positive bases stop evaluating after their first model; every negative base
  checks every clause, and union enumeration itself always finishes.
* Those full unions use a one-state nonterminal graph fixture deliberately to
  test closure on infinite extension languages. They are graph-mechanism tests,
  not a substitution of nonterminal automata for the terminal subtype problem.
  Separately, 328 complete safe terminal first-return questions on unary path
  fixtures agree: 40 YES and 288 NO. Their whole first-return languages are
  known independently; no scan cutoff supplies their negative answers.
* A joint fixed-reference query asks for root-to-end S paths of lengths two
  AND three. Each requirement is independently satisfiable; the conjunction
  is NO after complete finite-state exhaustion. Thus the oracle does not
  multiply independently satisfiable word requirements.
* 280 finite graph queries with unary tests, aliases, equalities/disequalities
  and up to three path atoms agree with an exhaustive matrix/CSP interpretation
  (171 positive, 109 negative). There are 21 targeted compiled diagrams,
  including distinct physical marks sharing one old origin, coincident marks,
  zero-length paths, recoloured endpoints, portals and singleton overlap wraps.
* Seven successive ACTUAL preimages on three non-unary coloured terminal
  fixtures end in satisfiable two-vertex queries. These are guided positive
  branches, not exhaustive high-rank unions. Clause weights are recorded.
* Direct border definitions check 1,022 binary words and 1,850 milestone-return
  identities. A deliberately tiny frontier cap correctly returns UNKNOWN.

The full unions have one path atom. The joint cases use the separate oracle
and selected compiled diagrams, not full enumeration of joint-query unions.
No finite corpus proves the uniform all-query theorem. The ordinary audit in
Sections 2-4, rather than extrapolation from these counts, is the support for it.

The deterministic core and two half-union runs were executed and freshly replayed;
full results in each part were byte-identical. A monolithic local invocation hit
the execution tool's time limit, so it was not called an exhaustive result.
The split runs exhaust the identical mask range and combine without dropping
cases. The repository workflow runs the full command and separately replays
the candidate's original suite; its actual result must be checked before
claiming that integrated CI passed.

```sh
python3 experiments/check_rank_closure_review.py --output /tmp/rank-closure-review.json --full-output /tmp/rank-closure-review-full.json
cmp results/rank-closure-review.json /tmp/rank-closure-review.json
```

The five recorded dependency blob hashes establish which unmodified compiler
was reviewed. Larger models and all per-base certificates regenerate from the
code with --full-output; no chat attachment is required. The local environment
used a verified partial checkout, not a full repository/Lean build.

## 7. Handoff for completing the proof review

The result is substantive positive support for the proposed terminal argument,
not another obstacle family or a claim that a resource cap solves a hard input.
The remaining project-level review should independently trace C029/C031 and
the forward characterization through satisfiability, terminal restriction,
safe extension and arbitrary possibly infinite tree semantics. This review
has not reread the original memo or checked all those implementations.

A selective formalization could first fix the graph-surgery invariant and
finite query grammar, then prove the two closure directions and quantitative
unwind. That would target the main semantic risks; merely formalizing the test
counts would not. The candidate author should retain the nonempty-reference,
directed-edge and shared-interval hypotheses explicitly in the final theorem.

No changes to candidate algorithm/proof bytes, earlier failed quotients, original
border checker, C079, Q004 status, ownership or other agents' work are required
by this review. The proposed terminal proof has survived this scoped audit; the
complete original subtype result is not newly marked established here.
