# Candidate unrestricted decidability proof by positive graph-query preimages

Research date: 2026-09-15. Repository base:
`47adf83c194aa941b525240f6470f3d77a69f81d`.
Workstream A017; implications for A012 and the existing C030/C031 transfer.

**STATUS: CANDIDATE END-TO-END PROOF, NOT AN ESTABLISHED RESULT.**
The argument below proposes a total procedure for every finite binary terminal
BorderAvoid instance. Unlike the preceding rank-two result, it supplies a
specific syntactic preimage lemma meant to discharge iteration at every rank.
The central Lemma 4 needs independent mathematical review. The full symbolic
compiler implementing that lemma has NOT been implemented or run. The code
checks exact graph identities, bounded query diagrams and substitutions of
shared references, not an unrestricted decision procedure. No Lean proof,
independent referee, literature-priority claim or final resolution is asserted.

The central review question is concrete: does the finite-diagram construction
in Sections 5-7 really remain inside existential DIRECTED regular-path queries,
with a single shared generator and a graph-size-independent diagram bound?
A counterexample to that claim would invalidate the proposed unrestricted
conclusion, while leaving the separately checked graph identities intact.

## 1. Exact problem and reversal

Fix a finite partial deterministic binary automaton

    I=(Q,delta,s,F,Bad,G), |Q|=k,

with no outgoing transition from any accepting state in F. A word w has run
c(0),...,c(N), and is a witness precisely when it is defined, avoids Bad,
ends in F, and

    for all 0<=i<=j<=N:
       w[j:] prefix of w[i:]  implies  (c(i),c(j)) not in G.       (1)

The diagonal and the empty suffix are included. Set rho=reverse(w) and
r_j=c(N-j). If b is a border length of rho[:j], including 0 and j, the
corresponding original agreement is forbidden exactly when (r_j,r_b) is in G.
Thus appending a letter to the reversed word requires only the new cut's
border-chain tests, provided the preceding reversed prefix was already safe.

A labelled reference is B=b_0...b_(m-1), m>=1, together with states
r_0,...,r_m, such that r_0 is a safe terminal final,

    delta(r_(j+1),b_j)=r_j,

and all border-chain tests through m are safe. Its last state need not be s.
Every full witness yields safe references; every safe reference ending at s
already reverses to a witness. A nonempty extension may pass through s without
being required to stop there.

For each state q define its incoming flag mask

    col(q)={p in Q : (p,q) in G}.

The mask of prefix j is

    M_j = union { col(r_b) : b is a border length of B[:j] }.

All masks belong to the fixed finite alphabet 2^Q. They are not word variables.
For j>0, with pi(j) the longest proper border,

    M_j=col(r_j) union M_pi(j),       M_0=col(r_0).                (2)

An actual newly chosen reverse state p must be outside Bad, avoid its diagonal
flag, and not belong to the mask for its new longest PROPER border. Testing
these is a finite-state condition; no negative path predicate is required.

### Lemma 1: terminal depth and first-return milestones

Let depth(0)=0, depth(j)=1+depth(pi(j)). Along the border chain of any prefix
of a defined reversed terminal path, the original labels are distinct. If two
border lengths a>b had r_a=r_b, reversing their prefixes gives two accepted
continuations from that same state, with the shorter a prefix of the longer.
The shorter reaches a terminal final before the longer finishes, impossible.
Consequently depth(j)<=k-1.

For each first attained depth h, let m_h be its first position. Then m_1=1 and

    pi(m_(h+1))=m_h.

Indeed any longer parent would contain a positive-position occurrence of the
length-m_h prefix ending earlier, creating depth at least h+1 prematurely.
The same argument proves m_(h+1) is exactly the end of the first new occurrence
of B_h=rho[:m_h]. Occurrences may overlap. After the last attained milestone,
there is no new occurrence of its full reference.

Therefore every nonempty terminal witness consists of a safe one-letter
reference, at most k-2 first-return promotions, then a finishing continuation
with no complete return of its current reference. A return at the very last
input position DOES count as a promotion. This corrects the endpoint mistake
found in the preceding rank-two prototype; the present construction keeps the
full endpoint explicitly.

This lemma alone does not make the infinitely branching hierarchy decidable.
The new proposed ingredient is Lemma 4 below, not another length cutoff.

## 2. Complete coloured prefix graphs

For a reference B of length m define a graph P(B) on vertices 0,...,m.
It has four DIRECTED edge labels:

* F: j -> pi(j), with F(0)=0;
* S: j -> j+1 for j<m, undefined at m;
* K_a for a in {0,1}: j -> kappa_B(j,a), where kappa is the length of the
  longest prefix of B that is a suffix of B[:j]a.

For j=m, kappa uses the usual full-pattern fallback pi(m) before consuming a.
Thus K_0,K_1,F are total functions. S is partial. Edges with distinct labels
may have the same endpoints. No inverse edge relation is made available.

The colour of j is the finite tuple

    (r_j, M_j, next_j, root_j, end_j),

where next_j=b_j for j<m and END otherwise, root is true only at 0, and end
is true only at m. Its alphabet is finite and effectively known from I.
The numerical index j is NOT part of the colour alphabet.

A regular-path observer is a finite automaton reading directed edge labels
and finite unary vertex-colour tests. It can remember an original state q.
The path-word encoding may be taken as

    colour(v0), edge1, colour(v1), ..., edgeL, colour(vL).

Arbitrary finite Boolean predicates on a colour are allowed. In particular,
NOT end is a unary alphabet predicate, not a negated graph-reachability test.
Standard finite-state products and filtering suffice for these observers.

### The finishing query Finish_I

At the reference's endpoint e=m, select its stored original label r_e.
Start a path observer at vertex F(e) with original control r_e. The observer
may traverse only K_a edges. On K_a from a cursor to h, change original
control q to p only when

    delta(p,a)=q, p not in Bad, (p,p) not in G, p not in M_h.

It may not visit the graph endpoint e: doing so would be another full return.
It accepts exactly when the original control is s. The empty walk is allowed.
All these are finite-state and finite-colour conditions. Endpoint and start
cursor are existential graph variables linked by one F edge.

For a safe reference B,

    P(B) satisfies Finish_I
      iff some safe completion without another promotion is a witness. (3)

Until a full return of B, every proper border is a prefix of B. The KMP cursor
and M_h therefore enumerate exactly all new comparisons. This proves both
directions of (3). The accepted walk's bits, appended to B and reversed, give
an actual witness. This is not an approximation discarding internal sources.

## 3. Exact promotion as a walk-guided strip extension

Let C=B a_1...a_L, L>=1, be a safe first-return extension of B. Put n=m+L.
Generate it using one walk in P(B):

    h_0=F(m), h_i=K_(a_i)(h_(i-1)),
    h_i != m for i<L, and h_L=m.                                 (4)

A finite generator control chooses actual reverse states q_i, initially
q_0=r_m, requiring delta(q_i,a_i)=q_(i-1), safety, absence of the diagonal,
and q_i not in M_(h_i). These are precisely the valid first-return transitions.
For every fresh prefix m+i,

    pi_C(m+i)=h_i,
    reference_state(m+i)=q_i,
    mask(m+i)=col(q_i) union M_(h_i).                             (5)

This includes the completed reference: pi_C(n)=m. No prefix before n can
have a proper border of length at least m, since that would finish an earlier
new B occurrence. Equations (4)-(5) establish the exact failure and mask data.

The entire new graph P(C) is obtained as follows. Denote its fresh vertices by
v_1,...,v_L, in order, and retain old vertices 0,...,m.

### Old core

At every j<m all edges and colours are unchanged. At the old endpoint m,
remove its old K_(a_1) edge; install S and K_(a_1) to v_1. Its other K edge
and F edge stay unchanged. Relabel it as non-end with next=a_1. Its reference
state and mask stay unchanged.

### Proper fresh vertices

For i<L, colour v_i by (q_i,col(q_i) union M_(h_i),a_(i+1),false,false).
Install

    F(v_i)=h_i,
    S(v_i)=v_(i+1),
    K_(a_(i+1))(v_i)=v_(i+1),
    K_b(v_i)=K_b(h_i) in the old graph, for b!=a_(i+1).            (6)

The last equation follows by the failure recurrence. Its endpoint belongs to
the old core, possibly old endpoint m.

### Completed fresh endpoint

Colour v_L by (q_L,col(q_L) union M_m,END,false,true). Install

    F(v_L)=m,
    K_(a_1)(v_L)=v_1,
    K_b(v_L)=K_b(m) in the old graph, for b!=a_1.                 (7)

There is no S edge at v_L. The K_(a_1) edge is a genuine wrap; when L=1 it is
a self-loop. Applying the proper-vertex rule here instead would be wrong.

### Lemma 2: exactness and the single entrance

Equations (4)-(7) construct exactly P(C), including overlapping first returns,
all reference-state colours, and all border masks. Conversely every safe
walk of form (4) generates exactly one such labelled C.

The only edges from old vertices into fresh vertices end at v_1. Inside the
fresh set, edges are forward adjacent steps, except for the endpoint wrap
v_L -> v_1. Every other fresh edge goes back to the old core. This is the
specific restriction used below. It is much stronger than bounded failure
depth alone, and does not assert bounded treewidth of the complete graph.

The deterministic test compares these equations with a separate literal
suffix-definition construction. It does not compute pi_C in the extension
constructor.

## 4. The query language that must be closed

Let EP-RPQ be finite unions of formulas of the form

    exists x_1,...,x_v:
       conjunction of finite unary colour tests,
       vertex equalities/disequalities, and
       regular_path_A(x,y).                                     (8)

Every regular path is DIRECTED, with a supplied finite-state observer as in
Section 2. Path witnesses are existential and independent unless coupled by
shared vertex variables. The formula has NO path-label equality predicate,
NO negated reachability atom, NO inverse F/S/K edge, and NO quantification over
arbitrary sets or relations. Empty paths and finite disjunctions are permitted.

On a finite graph this language is decidable: enumerate assignments of its
finitely many vertex variables and use finite product reachability for each
path atom. Queries may be very large; no polynomial complexity claim follows.
Root/end constants can be replaced by variables with their unique unary tests.

Finish_I belongs to this language. The decisive proposed closure is:

### Lemma 4 (candidate promotion-preimage lemma)

Given I and an EP-RPQ formula phi, one can effectively construct another
EP-RPQ formula Pre_I(phi), independent of the concrete reference length, such
that for EVERY safe labelled reference B,

    P(B) |= Pre_I(phi)
      iff there is a safe first-return extension C of B with P(C) |= phi. (9)

Sections 5-7 give the finite syntactic construction and both implications.
There is no appeal to an unproved regularity of arbitrary witness languages or
to a generic MSO/stack decidability theorem. This lemma is the highest-risk
new statement and the primary independent-review target.

## 5. Finite diagrams for positive paths

First fix one conjunctive branch of phi. Let its path observers have s_i
states, after finite normalization of any epsilon/colour-test moves. Every
satisfying path can be chosen simple in its product with its observer: if a
(vertex,control) pair repeats, remove the intervening segment. This preserves
endpoints, all finite-state acceptance conditions and all vertex-colour tests.
Other atoms do not name the interior of a path witness.

### Lemma 3: bounded strip entrances

A simple accepting product path visits v_1 at most s_i times. Every re-entry
to the fresh strip, whether from the old core or by the endpoint wrap, visits
v_1. Its initial vertex may also be a fresh vertex distinct from v_1.
Therefore it has at most s_i+1 fresh forward excursions.

Each excursion is a contiguous forward interval of fresh positions, followed
by an exit to the core, an endpoint wrap, or the query's final position. A
zero-length interval is permitted. Core stretches may be arbitrarily long;
the bound is NOT on their lengths. There can be at most s_i+2 intervening
core stretches.

Mark all fresh query-variable positions, v_1, v_L, and the endpoints of every
fresh excursion. There are at most

    v + 2 + 2*sum_i(s_i+1)                                      (10)

distinct required marks. The bound depends on phi, not |B| or |C|.

One can consequently enumerate a FINITE collection of diagrams. A diagram
specifies:

1. Which vertex variables belong to the old core or the fresh strip.
2. An ordered partition of the fresh variables/marks, allowing coincident
   marks and including v_1 and v_L as the first and last classes.
3. For each path atom, its bounded alternation of core stretches, forward
   fresh stretches, and single entrance/exit/wrap edges; the fresh positions
   at their endpoints; and observer controls at every piece boundary.
4. The first generated bit a_1 and all finite controls/colours needed at marks.

Inconsistent orderings, edge types, equality atoms or control assignments are
discarded. A diagram need not enforce product simplicity: simplicity proves
that some bounded diagram exists. Allowing a non-simple realization in a
bounded diagram cannot create a false positive, since it is still a genuine
accepted path. Thus the compiler does not need a global path-simplicity atom.

This is the source of finiteness. It is not choosing one concrete word per
state or per agreement profile. Unbounded reference strings remain quantified
through regular path atoms in the next section.

## 6. Compile ONE diagram into a query on the old graph

This section makes the proposed elimination effective rather than assuming
that a bounded number of marks somehow bounds the intervals between them.
There are three sorts of constraints, all expressible in (8).

### 6.1 Core stretches and old colours

For a fixed first bit a=a_1, the old-core induced subgraph of P(C) is exactly
P(B) with the K_a edge from its unique endpoint suppressed and that endpoint's
next/end fields relabelled to (a,false). No other old edge or colour changes.

The inverse image of a path observer under this change is computed by a finite
observer: on a base path, transform endpoint colour tests by this fixed colour
map and reject any K_a edge whose source has the base End bit. All tests are
on finite colours. This handles arbitrary core stretches, including visits
to the old endpoint, with an ordinary regular-path atom on P(B).

Old query variables are retained as base variables. Their colour tests use the
same finite relabelling. Their equality/disequality atoms remain unchanged.
Old/fresh equality is impossible, and old/fresh disequality is automatic.
Fresh equalities/disequalities were settled by the ordered mark partition.

### 6.2 Portal edges and attachments at marks

For each marked fresh position v_i introduce one shared old-graph variable
z_i for its generator origin h_i. All uses of that same fresh position use
that same z_i and the same guessed finite generator control q_i. No independent
reference is chosen for different query paths.

A proper fresh F exit ends at z_i. A proper fresh K_b mismatch exit is linked
to its old target y by the one-edge atom K_b(z_i,y); its label b must differ
from the guessed next bit of that mark. Since K_b is functional on P(B), two
uses of the same physical mismatch edge cannot select different targets.
The source colour is determined by q_i and M_(z_i); the destination colour is
the relabelled base colour of y. Observer-transition compatibility is a finite
choice of controls plus finite unary tests at z_i and y.

Endpoint exits use (7): F ends at old endpoint m; a mismatching K_b exit is
K_b(m,y); the matching K_a edge wraps to the first fresh mark. Entrance edges
start at old endpoint m and end at the first fresh mark, with label S or K_a.
The wrap and entrance cases have no unbounded path hidden inside them.

The final mark's origin is constrained to equal old endpoint m. Its original
state and mask are checked by the same rule (5), not by separate assignments.
When first and last mark coincide, use the L=1 case, including its self-loop.

### 6.3 ONE shared generator split at the marks

Let the distinct fresh mark classes be v_(i_1),...,v_(i_t), in increasing
order. They satisfy i_1=1 and i_t=L. Quantify their origins z_1,...,z_t and
finite generator controls/colours. The first emission is exactly one K_a edge
from F(m) to z_1, with the initial control r_m and the chosen first bit a.
If t>1, consecutive distinct marks are connected by a POSITIVE-length generator
path; if t=1, first emission is also final. No unmarked leading/trailing strip
is omitted because the first and last fresh vertices themselves were marked.

The concatenation of these generator segments must satisfy (4), the original
reverse transition rule, and all finite mask/diagonal/Bad tests. Every origin
except the last must avoid base End; the last equals base End. State/control
choices at each mark are shared between its two adjacent segments. Reading a
base K_b edge supplies the generated bit b. The next-bit field of a fresh node
is the NEXT generated bit; it is handled with one-symbol delay. At the final
mark it is END. This is a finite-state transduction, not a lookup into an unknown
word. Its finite control stores the current actual reverse state, first bit,
and a bounded amount of delayed colour information. All mask values are finite
alphabet values read at the corresponding base origins.

Now superimpose the diagram's fresh forward pieces on that SAME ordered strip.
Their endpoints are marks, so on each interval between consecutive marks the
set of active pieces is fixed. A forward step in the strip has two possible
edge labels for an observer: S or K_b, where b is the next generated bit.
Its vertex colours are exactly the finite output colours of the generator.
For each active piece, run its supplied observer from its guessed entry control
to its guessed exit control. Take the finite product of all active observers
with the generator transducer. Each observer may choose its own edge/NFA moves,
but all of them read the SAME generated vertices and bits on a shared interval.

A finite product plus inverse image under a finite-state transducer yields an
explicit finite regular-path observer over the base graph. Concretely its
states are tuples of generator control, delayed colour/bit, and the current
controls of all active forward-piece observers. Its transitions read a base
K edge and its finite endpoint colours; choose the next reverse state; perform
the reference-safety tests; compute the new output colour; and update every
active observer on the one common output step. Boundary control tuples are
finitely guessed in the diagram and shared across adjacent intervals. Zero-
length forward pieces require their appropriate empty-walk acceptance.

Thus each interval becomes one regular_path_A(z_j,z_(j+1)) atom, with shared
endpoint variables and shared finite boundary data. All required colour and
attachment tests at marks are unary predicates and one-edge atoms. Their
conjunction says that ONE complete labelled generator path realizes every
forward observation jointly.

This last product is the part that would be lost by choosing separate
reference words for different paths. Incompatible observations must reject;
the implementation includes an explicit shared-strip regression.

### Effective output

For each finite diagram, conjoin these atoms, introduce the finitely many
base variables, and existentially quantify them. Disjoin over all diagrams and
all original conjunctive branches. The result is Pre_I(phi) in exactly (8).

No concrete base length is used by the compiler. Bounds (10), the observer
state sets, the finite original automaton and the finite colour alphabet
control all enumeration. Automata may grow enormously under products and
repeated preimages; they are finite and effectively constructible. No useful
complexity bound is claimed here.

## 7. Both directions of the candidate preimage lemma

### From a promoted model to a base model

Suppose a safe C satisfies phi. Choose its variable assignment and, for every
path atom, an accepting product-simple path. Lemma 3 supplies a bounded diagram.
Order all its marks by their actual positions in the one C strip. Assign each
origin variable to the actual KMP generator position at that mark; assign its
actual reverse state and finite colours. Use the actual core stretches, exits,
wraps, and forward pieces to satisfy 6.1-6.2. Split the actual generator walk
at the marks. It satisfies the products in 6.3 because every active observation
is an actual path on those same physical vertices. Hence the compiled base
query is true.

### From a base model to a promoted model

Suppose one compiled diagram is satisfied in P(B). Choose witnessing base paths
for its generator-interval atoms. Their shared endpoints and shared finite
control states concatenate, together with the first single emission, into ONE
safe walk of (4). Positivity between distinct marks places them at distinct
ordered fresh positions. The endpoint restrictions make its last emission the
first full B return. By Lemma 2 it constructs a definite safe reference C and
its exact graph P(C).

Place every fresh query variable at its common marked position; place old ones
at their base assignment. The local tests ensure exactly the required portal
edges and colours. Each observer product supplies actual forward paths over
its shared strip intervals. Concatenate adjacent intervals for each forward
piece, then concatenate that piece with the core paths and portal edges of
its diagram. Controls agree at seams, so every original path atom accepts.
Equalities and unary tests hold by the chosen partition/colour constraints.
Therefore P(C) satisfies the original phi.

No requirement says the different core-path witnesses use the same letters:
the original query language does not impose path-label equality. Whenever
letters DO have to be shared because two pieces traverse the same physical
strip interval, Section 6.3 uses one common generator and an observer product.
This precise distinction must be checked in independent review.

## 8. Proposed unrestricted decision algorithm

If Lemma 4 is correct, define finite queries

    Phi_0 = Finish_I,
    Phi_(h+1) = Phi_h OR Pre_I(Phi_h).                            (11)

Induction using (9) shows P(B) satisfies Phi_h exactly when some witness
completion of the safe B uses at most h further first-return promotions.
This induction changes a FORMULA, not a concrete reference summary. It does
not reuse the rank-two reachability matrix when its old hidden vertices become
addressable. All positions of B remain variables/vertices of the graph against
which the new query is eventually evaluated.

Handle an empty witness directly. For a nonempty witness, enumerate all safe
one-letter references: f in F and p in Q with delta(p,a)=f, retaining the
boundary-safe pairs (f,p). There are finitely many. For k>=2 build Phi_(k-2)
and evaluate it on each finite two-vertex P(a). Return YES iff one evaluation
succeeds. For k=1 there is only the empty-word case under terminality.

Soundness: every successful query model reconstructs a sequence of safe
promotions and a safe finishing walk, hence an original witness by (1)-(3).
Completeness: Lemma 1 places any original nonempty witness in at most k-1
reference levels, so it supplies a successful model of one Phi_(k-2) query.
Termination: (11) uses finitely many calls to the explicit finite syntactic
construction of Section 6, followed by finitely many finite-graph query tests.
It does not depend on finding a word-length bound by search. A concrete witness
can be reconstructed from query/path models, or after a proved YES found by
ordinary exhaustive witness enumeration, which then terminates.

**Candidate conclusion:** finite binary terminal BorderAvoid is decidable.
Combining that proposed conclusion with the repository's C031/C029/forward
bridge would decide normalized Problem 1.7 for bottom and one covariant binary
product over arbitrary, possibly infinite trees. Those existing semantic
reductions retain their recorded proof status and have not been independently
re-certified by this work. This note does NOT silently assume finite trees.

This is the intended full proof, not a claim that its highest-risk lemma has
already survived outside review. The repository should not mark Problem 1.7
settled merely because this candidate outline and tests have been produced.

## 9. Why the known barriers do not immediately refute this attempt

* Large modular witnesses, nonsemilinear lengths and nonrational raw counts:
  no polynomial length bound, rational witness series or bounded run count is
  asserted. Formula sizes may grow non-elementarily with k.
* Full-profile residual collisions: references are not substituted by endpoint,
  action or profile. The computed object is a query preimage that retains all
  future existential path observations permitted by the grammar.
* Unbounded graph width: the proof uses bounded entry PORTS of one added strip,
  not bounded treewidth of the whole reference graph.
* Generic PCP-capable iteration: there is no arbitrary two-output append
  relation and no equality of independent path labels. Only the exact prefix
  graph transformation of Section 3 is eliminated.
* Universal-safety versus mixed-family synthesis: (9) existentially chooses one
  shared safe C and path models. It is not a universal-family validator.
* Unbounded source visits: generator paths are not bounded in length or visits.
  Termination comes from syntactic elimination, if Lemma 4 holds.

### A non-negotiable scope boundary: no converse

If inverse F edges are added, the entrance lemma is false. For B=0 and
C=0 1^n 0, every internal new one-prefix has failure parent 0. Inverse F gives
n different edges from the core root to different fresh vertices. The finite
single-entrance bound disappears. The present query grammar never introduces
such an inverse relation. Likewise it does not introduce negated reachability,
full MSO set quantification, or path-label equality.

These restrictions are substantive. A shortcut invoking a richer closure
theorem would require a different proof. The previous matching-graph counter-
examples are not being erased or promoted into proof of this attempt.

## 10. Executed checks and remaining verification work

Commands:

    python3 experiments/check_rank_query_graphs.py
    python3 experiments/check_query_grafting.py
    python3 experiments/run_experiments.py

The first suite checks 4,094 complete direct/literal prefix graphs; every one
of the 826 first-return extensions within its exhaustive word range; 34,702
classified edges; 826 exact old-core restrictions; 10,080 arbitrary finite
regular-path queries with 6,419 extracted accepting diagrams; 1,260 independent
forward-observer products; 122,640 original word-predicate comparisons; 714
accepted witness hierarchies; and 45 full-endpoint rank-boundary cases.
Higher-rank modular fixtures explicitly traverse all their reference levels
through rank seven. This checks concrete constructions, NOT a general search.

The second suite extracts 308 jointly satisfying diagrams with 685 total path
atoms. It tries 12,499 substitutions using one common alternative reference
and one monotone map of every physical mark. All 2,108 passing substitutions
preserve the queries when independently rechecked; 1,598 change the reference
and 1,484 change its length. In total 4,758 resulting path atoms are rechecked.
It is a finite conditional-substitution audit, not an implementation or proof
of the unbounded diagram-enumeration compiler.

The expected next work is NOT another restricted solver. It is independent
review and preferably implementation of Sections 5-7, specifically:

1. Check the diagram bound for normalized regular-path observers, including
   empty walks, shared variables, endpoint wraps and coincident first/last.
2. Check that the generator/observer product needs only finite local colour
   data and no unrecorded equality of two base-path labels.
3. Check the exact old-endpoint rewrite in every inherited path atom.
4. Implement the finite symbolic compiler, or exhibit a precise query whose
   preimage cannot be expressed by the construction as written.
5. Only after that audit, run original-problem semantic transfer checks and
   consider stable claim IDs or selective formalization.

No full compiler, independent mathematical review, Lean theorem or repository-
wide CI is claimed. This is a candidate complete proof with tested kernel
lemmas, not a certified final solution. Remote GitHub publication also requires
a working write path; the session's connector is read-only and CLI DNS failed.
