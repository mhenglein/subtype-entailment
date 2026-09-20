# Constructive rank-query closure: compiler audit and an explicit witness bound

**Later September 20 result.** [C086](../research/claims.md#c086) proves the original terminal
F and the original U contract for a different, filtered compiler. The old
unfiltered compiler counterexample remains valid, and C082 remains a valid
larger bound. The dated argument and earlier open status below are preserved
as history, not the current C086 status.

**September 20 correction.** The old universal weight estimate
`64*k*T^(2*T+2)` is false for the concrete enumerator: a checked terminal
five-state counterexample emits a larger clause. The semantic compiler and
qualitative C081 decision remain checked. C082 proves the separate replacement
`64*k*T^(6*T^2+2)` and the resulting Fhat witness bound. The original F by itself
and a smaller existential compiler are not refuted. Earlier unqualified size
arguments and reviews below are superseded at precisely that point; the text
is preserved as history. [Exact correction and dependency audit](2026-09-20-post-c081-quantitative-integration.md).

Date: 2026-09-17. Base main: `afbb2954bb984998db3ecac252b5e2e23f62341a`.
Workstream A017; follows the [candidate proof](2026-09-15-candidate-rank-query-decision.md).

**Status: PROPOSED COMPLETE ORDINARY PROOF WITH AN IMPLEMENTED SYMBOLIC
COMPILER; independent mathematical review is still pending; not Lean-checked.**
This is a proposed resolution of terminal BorderAvoid, not a declaration that
Problem 1.7 has been independently settled. The compiler and tests below were
written in the same investigation as this audit. They are not another researcher's
mathematical review. No priority claim, useful complexity bound, full repository
CI result, or broadly benchmarked unrestricted implementation is asserted.

The earlier candidate's specific missing implementation is now supplied:
`rank_preimage.py` includes a finite syntactic diagram enumerator, a diagram-to-
query compiler, query evaluation, and the bounded-rank driver. The enumerator
and compiler have NO reference-word or concrete-base-graph argument. Tests now
compose the ACTUAL compiled query repeatedly, not only concrete graph extensions.

The substantive new derivation is an explicit, computable all-state witness
bound from quantitative closure. The proof has no assumed bound on reference
length, number of runs, or source visits. Its correctness still depends on the
closure argument surviving independent scrutiny. The original subtype transfer
is C031; that separate recorded dependency is not re-proved here.

## 1. Exact model and observer convention

Let I=(Q,delta,s,F,Bad,G) be a finite partial deterministic automaton over
{0,1}, with k=|Q|>=1, and no outgoing transition from any f in F. A safe
accepted word w with run c(0),...,c(N) is a witness exactly when

    (c(i),c(j)) in G implies w[i:i+N-j] != w[j:N]
    for every 0<=i<=j<=N.

Undefined transitions reject. Bad states at either endpoint reject. Empty
words, diagonal flags, empty suffixes and multiple terminal finals are included.
Reverse w to rho and let r_i=c(N-i). For each prefix length i, its proper
failure parent pi(i) is its longest proper border length, with pi(0)=0.
A safe labelled reference B has a full reverse run r_0,...,r_m with r_0 terminal;
it need not end at original start s. Define

    col(q) = {p : (p,q) in G},
    M_i = union of col(r_j) over all borders j of B[:i], including 0,i.

The prefix graph P(B) has vertices 0,...,m and the directed labels F,S,K0,K1.
F(i)=pi(i), S(i)=i+1 when i<m, and K_a is the longest-prefix suffix update
on appending a. At i=m the K update starts by falling back to pi(m).
Its vertex colour is (r_i,M_i,next_i,root_i,end_i). The finite colour set is
contained in

    Q x 2^Q x {0,1,END} x {false,true}^2.

No numerical position is part of a colour.

An observer is an epsilon-free finite-state path automaton. It has finite
initial/final control sets, a permitted-colour predicate for each control,
and a finite transition relation

    (control, source_colour, edge_label, target_colour, next_control).

This is an ordinary finite alphabet: the graph supplies colours and edge labels.
It is equivalent to the alternating colour/edge convention of the candidate
proof. It permits finite endpoint-colour tests without hidden registers or
comparisons to quantified vertices. Internal observers are represented by
finite-state products, not black-box string predicates. Their transition
functions can always be expanded into finite tables, although doing so is
usually impractical.

A conjunctive query Q consists of finitely many existential vertex variables,
unary finite-colour tests, equalities/disequalities between those variables,
and path atoms with supplied observers. A union of finitely many such clauses
is allowed. No inverse edges, negative reachability, path-label equality, or
set quantification occurs. Queries are evaluated by finite CSP search and
finite observer/graph products.

## 2. Audited graph and rank facts

The elementary arguments from the candidate proof are retained, not replaced
by a numerical experiment.

1. Every border chain of a defined reversed terminal path has distinct original
   state labels. Two equal labels on nested borders would give a shorter
   accepted continuation that is a prefix of a longer accepted continuation
   from the same state, contradicting terminality. Hence depth(i)<=k-1.
2. If m_h is the first prefix attaining depth h, then pi(m_(h+1))=m_h.
   A larger parent would put an earlier occurrence of the length-m_h prefix
   before m_(h+1). Thus each new milestone is precisely the first return of
   the previous reference, including overlapping returns.
3. After the last milestone, the reference never returns completely. A full
   return at the final input position still creates a new level; it is not
   an uncharged accepting endpoint.

For a first-return extension C=B a_1...a_L, generate old-graph cursors by

    h_0=F(m), h_i=K_(a_i)(h_(i-1)),
    h_i != m for i<L, h_L=m.

Choose actual reverse states q_i with delta(q_i,a_i)=q_(i-1), starting at
q_0=r_m, avoiding Bad, diagonal flags and M_(h_i). New prefix colours are

    (q_i, col(q_i) union M_(h_i), a_(i+1), false, false), i<L,
    (q_L, col(q_L) union M_m, END, false, true), i=L.

All old vertices except m are unchanged. At m, the K_(a_1) edge is replaced
by a matching edge to the first new vertex; an S edge to that vertex is added;
its colour becomes non-end with next=a_1. Other old edges are unchanged.

At a proper new vertex i, F goes to h_i; S and K_(a_(i+1)) go to i+1; the
other K_b goes to the old K_b(h_i). At the new endpoint, F goes to old m,
K_(a_1) wraps to the first new vertex and the other K_b goes to old K_b(m).
This includes L=1, where the wrap is a self-loop. These identities follow
directly from the prefix-matching recurrence.

In particular every entrance from the old graph into the new part is at its
FIRST vertex. Every other new-to-new edge is forward adjacent, except the
endpoint wrap to that same entrance. New mismatch/failure edges return to the
old graph. No query is allowed to reverse these edges.

## 3. Finite diagrams: the exact quantifier bound

Let an input conjunctive query have v variables, a path atoms and observer
sizes s_1,...,s_a. Set sigma=sum s_i and

    T = max(2, 1+v+a+sigma).

Choose a successful path for each atom without repetition of a
(graph-vertex,observer-control) pair. A repeated pair can be cut out. This
preserves both endpoints and every finite-state test; query atoms do not
bind a path's internal vertices. Other vertex variables do not impose a
requirement that this path visit them.

Each path can enter the first new vertex at most s_i times. It can additionally
start elsewhere in the new part. Hence it has at most s_i+1 new forward
excursions. Mark all fresh query variables, the first and last new vertices,
and excursion endpoints. There are at most

    v+2+2*sum(s_i+1) <= 6T

marked positions. Their order and coincidences, observer controls at their
boundaries, core stretches and portal-edge choices form a FINITE diagram.
The bound is independent of B, C and their lengths.

The complete enumerator uses every old/fresh assignment of query variables,
every bounded portal shape, every ordered partition of its fresh marks,
every finite observer-control assignment, and the finite original-state and
colour choices. It prunes only combinations contradicting these stated
conditions. It does not enumerate strings or guess a string-length bound.

Product simplicity is needed only to prove that some bounded diagram exists.
Compiled diagrams do not require paths to remain simple. Allowing a nonsimple
realizing path is harmless: it is still a genuine accepted path.

## 4. Fully explicit compilation of a diagram

### 4.1 Shared finite data

Guess the old endpoint's full colour c_e from the finite colour alphabet and
constrain an old variable e to that colour. Its End flag is true. Also guess
the first generated bit a_1. These guesses make the recoloured old endpoint
known, and make the new endpoint's colour determined by q_L and c_e.

For each distinct fresh mark t introduce ONE old-graph origin variable z_t
and ONE actual reverse state q_t. Its next bit is a shared guess in {0,1},
except the final mark has END. Its colour is computed from q_t, M_(z_t)
and that next bit. The final origin equals e; other origins are not End.

Origins of different fresh marks MAY coincide. They are KMP cursor values,
not physical positions. Distinct physical marks are enforced by positive-length
intervals in the common generator, not by incorrectly requiring unequal origins.
All uses of the same physical mark share its origin, state and next bit.

### 4.2 Core pieces, including the changed old endpoint

On old vertices, recolour e to next=a_1 and End=false; suppress the old
K_(a_1) edge leaving e. Relativize each core observer by this finite colour
map and edge guard. Its control-state count does not change under the
source/target-colour convention above. No other old edge changes.

Original old variables remain existential old variables. Their unary tests
are pulled back through the same colour map; their equalities are retained.
Old/fresh equality is impossible and disequality automatic. Fresh equalities
and disequalities are settled by the ordered partition of marks.

### 4.3 Portal pieces

An entrance must leave e by S or K_(a_1) and land at the first mark. A wrap
must leave the last mark by K_(a_1) and land at the first mark. Their source
colours are known from the finite guesses, so observer compatibility is a
unary colour predicate on the first mark's origin. This avoids introducing
any unexpressible comparison between two unrelated old vertices.

A proper F exit from a mark ends at its origin z_t. Identify its old target
with z_t and check the observer transition by a unary predicate. A proper
mismatch K_b exit, with b different from the mark's next bit, is the actual
one-edge atom K_b(z_t,y), with the appropriate finite endpoint-colour guards.
At the final mark the mismatch bit must differ from a_1 and its origin is e.
Functional K edges prevent different uses of the same mismatch from choosing
different old destinations. Final F exits and L=1 wraps use the same rules.

### 4.4 A finite-state product for each shared interval

Split EVERY forward query piece at EVERY global mark it crosses. Guess and
share its observer control at those internal seams. Between consecutive marks,
the collection of active pieces is fixed. There are at most 2T active pieces;
a path that traverses the interval twice contributes two observer coordinates.

One interval observer has control

    (q, next, seen, t_1,...,t_b),

where q is the actual reverse-run state, next is 0,1 or END, seen records
positive length, and t_j is the control of active observer j. Its initial
and final tuples are the shared guesses at the two marks, with seen=0 and 1.
There are exactly

    6*k*product_j(s_j)

potential controls. Unreachable controls need not be materialized.

At an old origin h of colour c, the produced fresh colour is

    f(q,c,next)=(q, col(q) union c.mask, next, false, next==END).

Require q safe, its diagonal absent, q notin c.mask, and
(next==END) iff c.End. Each active observer must allow f(q,c,next).
A transition reads a base K_b edge h->h' only if next=b and h is not End.
Choose q' satisfying delta(q',b)=q and its safety/mask tests. Guess next'
in {0,1} at a non-End h', or END at an End h'. Every active observer independently
chooses an S or K_b transition, but ALL observe the SAME two fresh colours and
the SAME emitted bit. Set seen=1. These are explicit finite transition rules.

The next-bit guess is checked by the next transition. At marks it is shared
between adjacent interval observers. Thus the apparent one-symbol lookahead
is only finite control, not an extra unknown word or a graph-position register.
END has no outgoing generator move, so an intermediate full return cannot be
hidden inside an interval. The first emission is a separate single K_(a_1)
edge from F(e), with the old endpoint's actual state. If first and last marks
coincide, that one emission is the whole generator.

Each interval is now one regular-path atom between its shared origins.
Positive length makes successive distinct marks genuinely distinct physical
positions, even if their origins coincide. A zero-length query piece at one
mark is checked by equality of its boundary controls and its colour predicate.

This is not multiplying independent existence claims. It constructs one
path for each PHYSICAL interval of a single new reference, with all observations
of that interval present in the product. Different core stretches need not
share their letters, because the original query never required that equality.

## 5. Closure proof and quantitative size

**Proposed closure theorem.** Given I and any query phi of the stated language,
the finite construction Pre_I(phi) satisfies, for every safe reference B,

    P(B) |= Pre_I(phi)
      iff some safe first-return extension C of B satisfies P(C) |= phi.

Forward direction. From C and its successful query paths, choose product-simple
paths, mark their bounded excursion endpoints, and use the actual ordered marks,
origin cursors, original states, next bits and observer controls. Every core,
portal and interval atom is satisfied by its actual path. Thus the enumerator
contains a satisfied diagram.

Reverse direction. From a satisfied compiled diagram, choose a path for each
interval atom. Its endpoints and complete boundary control tuples agree with
the adjacent interval. Concatenate with the first single emission. Positive
length and the End guard give ONE first-return generator, hence one definite
safe C and its exact prefix graph. Place the original fresh variables at its
marks and old variables at their assigned old vertices. The portal predicates
supply real edges; core atoms supply real core paths; products supply all the
required forward observations of the common intervals. Their controls agree at
seams, so every original query atom accepts on P(C). Unary/equality constraints
hold by construction. This proves the two directions without an independent
reference choice for different path atoms.

No claimed operation lies outside the query grammar: all new variables are
vertices, all tests are finite colours, and every new nontrivial atom is a
directed finite-state path test. The proof does not use inverse edges,
negative reachability, equality of path labels, an arbitrary string solver,
or a graph-width theorem. In particular the SAME construction accepts its
own output as the next query input.

For a numerical bound, normalize multiple unary tests on one vertex to one
finite-colour table. Each clause uses at most 11T old variables, 12T path atoms,
core-observer total size at most 2T^2, and at most 6T interval products.
Each interval has at most 2T observer coordinates, each of size at most T.
One-edge atoms contribute at most 4T+4 further states. Therefore every output
clause has weight at most

    U_k(T) = 64*k*T^(2T+2).                                    (A)

The deliberately loose bound includes smaller and empty-piece cases. Finite
colour guesses and the NUMBER of disjuncts can be enormous but do not enlarge
an individual clause's weight. Their enumeration is finite and effective.
A direct fully tabulated implementation is possible; the code instead retains
finite products and colour-map expressions so it does not allocate every
possible product control.

## 6. An explicit unrestricted small-witness bound

The finishing query uses three variables, two path atoms and k+2 observer
states: one F edge from the graph endpoint to its proper failure parent, then
a K0/K1 observer storing the actual original state. The observer forbids End,
checks the new state's Bad/diagonal/mask obligations, and accepts at s. Its
empty path handles a reference that already ends at s. Let T_0=k+10 and set

    T_(j+1) = 64*k*T_j^(2T_j+2).

Define Phi_0=Finish_I and Phi_(h+1)=Phi_h OR Pre_I(Phi_h), distributing finite
unions into clauses. The closure theorem proves by induction that Phi_h means
completion using at most h more first-return promotions. Every clause has
weight at most T_h.

If a compiled clause of weight at most T_j holds on a base graph with m+1
vertices, choose a shortest accepting product path for every interval atom.
Their TOTAL length is at most (m+1)T_j. Endpoint sharing and positive-length
requirements are preserved because they are part of the interval observers.
Adding the first emission produces a new reference with at most

    (m+1)(T_j+2)

vertices. Choosing the individual shortest interval paths is sound ONLY after
all shared marks and finite boundary controls have been fixed; the observer
products still retain every common-word requirement. The closure theorem then
supplies the remaining lower-rank query on that actual new reference.

Starting with a one-letter reference (two vertices), after at most k-2 such
steps and the final k-state finishing observer, a witness exists within

    F(1)=0,
    F(k)=2*(k+1)*product_{j=1,...,k-2}(T_j+2),  k>=2.             (B)

The empty product is one. Bounds (A)-(B) are explicit total computable functions,
not values estimated from a census. They are intentionally enormous; no
polynomial or practical complexity claim is made.

**Proposed terminal conclusion.** Every positive k-state binary terminal
instance has a witness of length at most F(k). Hence exhaustive testing through
F(k) is a finite decision procedure. Alternatively compute Phi_(k-2) and evaluate
it on the finitely many safe one-letter prefix graphs. Both conclusions depend
on the closure proof above, not on the test counts below. There is no remaining
assumed source-visit, phase, marker or reference-length bound in this argument.

The repository's C031 transfers a terminal decider to the original normalized
subtype-entailment problem using C029 and the audited forward characterization.
That implication preserves arbitrary, possibly infinite type trees. Those
prior dependencies retain their recorded evidence status; this continuation
is not a fresh independent audit of the whole subtype bridge. Accordingly the
project should label this a PROPOSED RESOLUTION pending independent review,
not change the original problem's accepted status merely because the code runs.

## 7. Implementation, executed evidence and limits

`rank_preimage.py` implements the finite query grammar, regular-path evaluation,
finite diagram enumeration, exact compilation of one diagram, and lazy unions
of all preimage clauses. Neither `iter_diagrams` nor `compile_diagram` receives
a concrete base graph or word. Predicates/observers use a finite structural
syntax, not arbitrary callbacks into graph reachability or string solving.
`decide` is the resulting research driver; its resource/host limits return
UNKNOWN. YES normally includes a word checked by both original predicates.
A reconstruction cap returns UNKNOWN with a separate positive-query flag.

Run:

    python3 experiments/check_rank_preimage.py
    python3 experiments/run_experiments.py

The deterministic compiler audit records:

* Four COMPLETE preimage-union enumerations, 13,248 emitted branches in all,
  over an infinite first-return language. Two queries are positive and two
  negative by separate all-length graph arguments. These one-state graph tests
  concern the closure lemma, not nonterminal subtype semantics.
* 177 joint syntax queries, 263 compiled diagrams including the terminal and
  nested cases, 971 base evaluations, and 694 reconstructed common-reference
  models; 267 successful substitutions change the BASE length and 416 change
  the new reference length. This is stronger than grafting strings over one
  fixed base while leaving the symbolic compiler untested.
* 65 compilations with actual coloured terminal runs; 5,401 direct word checks;
  two incompatible shared-interval products are rejected.
* 21 SUCCESSIVE symbolic preimage compilations for the modular witnesses of
  ranks two through seven. The final compiled clauses are evaluated on the
  two-vertex initial graphs. These are positive proof/certificate-guided branches,
  NOT exhaustive searches of the enormous full query unions at those ranks.
* 1,152 complete two-state terminal decision oracles: 154 YES, 998 NO. A separate
  unguided promoted query finds the three-state witness 00 after 509 work units.
* 28 unary final-return boundary checks and an explicit UNKNOWN resource cap.

The largest declared product observer in the rank-seven certificate has
531,441,000,000 potential controls. This is a finite PRODUCT DESCRIPTION, not
an assertion that that many states were materialized or explored. Only reachable
controls required by the concrete query evaluation are enumerated.

At 200,000 work units, the generic driver remains UNKNOWN on an infinite
one-flag NO fixture and the positive three-copy modular fixture. Its construction
is exact in the proposed proof but not practical as presently enumerated.
The existing specialized solvers remain valuable. These timed exploratory
observations are not used as mathematical negative evidence.

All these tests were executed by the same research session. The finite graph
semantics and literal suffix constructions serve as differential code checks;
they do not constitute an external mathematical referee. The full query union
has not been benchmarked broadly, the whole repository CI/index has not been
run locally, and Lean verification remains undone.

## 8. Review targets and preservation of earlier results

An independent review should try to invalidate one of these exact implications:

1. Product-simple observer paths imply a graph-size-independent bound on new
   strip entrances, even with shared query endpoints and zero-length pieces.
2. One ordered set of marks and one product per physical interval is sufficient
   for simultaneous realization of every fresh observation. No equality of
   two independent path labels is required or silently introduced.
3. Portal constraints and changed-endpoint colours are all expressible using
   finite unary predicates and ordinary directed one-edge/path atoms.
4. The interval controller's delayed next bit, positive-length bit and End guard
   force a SINGLE first-return reference, including a one-letter extension and
   a return at the ultimate accepting cut.
5. The output syntax satisfies the identical contracts on the next preimage,
   and the quantitative argument really yields (A) and (B).
6. C031's prior semantic transfer has the exact hypotheses needed for the
   original arbitrary-tree entailment question.

The earlier failed state/profile quotients, nonregular/nonsemilinear languages,
large scheme costs, marker barriers and PCP warnings are retained. This proof
does not assert any of the refuted stronger statements. It changes the object
being eliminated to an existential path-query formula and permits enormous
formula/length growth. No new theorem ID is assigned before integration review.
