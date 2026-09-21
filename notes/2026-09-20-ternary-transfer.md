# Ternary covariant entailment: an automata-mediated binary transfer

> Current status, 21 September 2026: the ordinary result was independently
> accepted in the [submission review](2026-09-20-submission-review.md).
> Its exact integrated scope is [C089](../research/claims.md#c089).
> [Current integration and reproduction](2026-09-21-publication-candidate.md).
> The dated author record below is preserved, including its original pending
> review status and execution limits.

Date: 2026-09-20. Session: ternary-transfer-20260920. Issue #72, coordination #37.
Approaches: A010/A011/A018. Base: 19b06d4fed9da635d9b911f0e908d04e4fc4b099.
Status at outline creation: ordinary-proof route; independent mathematical review pending.
The binary core, shared ledgers, imports, toolchain and workflows are unchanged.

## End-to-end outline (written before supporting implementation)

Input: finite inequalities and one finite-expression query over variables,
bottom and one ternary covariant constructor. Values are arbitrary prefix-closed
subsets of {0,1,2}*, with inclusion as subtyping. The objective is a total,
effective, query-dependent many-one reduction to binary bottom/product
entailment. A polynomial preprocessing bound or a homomorphic type encoding is
not part of the claim.

1. Normalize every premise and query subexpression by exact fresh naming.
   Record model extension/restriction, including bottom and query-only names.
2. Define the finite push/pop/epsilon system, forced roots and denials. Prove
   the prefix-closed least closure and minimum-stack factorization over this
   finite alphabet. Construct an explicit absorbing subset-pair automaton.
3. Encode that ternary automaton into a binary absorbing automaton using the
   prefix code 0,10,11. Prove complete-word Witness equivalence. Incomplete
   codewords may be witnesses: inherit finality at internal code states and
   exclude those without a safe completion. Prove completion, not truncation,
   transfers every binary witness back to a source witness.
4. Use the EXISTING binary C029 total infinite-witness check. If it is true,
   output a fixed negative binary entailment instance. Otherwise terminalize
   and apply the EXISTING C030 direct terminal realization. A source UNSAT
   check instead outputs a fixed inconsistent target.
5. Prove both non-entailment directions through actual separating words and
   canonical models. No target valuation is assumed to be in an encoded image.
   Give a finite output bound separately from the C029 preprocessing cost.

Imported contracts: Basic.Witness (ordered i<=j suffix-prefix tests);
AbsorbingTerminal.Absorbing (successors of finals are final AND have empty
incoming flag columns); InfiniteDecision.infiniteWitnessCheck_correct (C029);
AbsorbingTerminal.c031; TerminalRealization.witness_iff_separating and
realization_satisfiable (C030); EntailmentDecision.entailsCheck_correct (C081).
All are the pinned binary contracts, not an assumed generic-alphabet theorem.

Falsification: preserve the failed homomorphism y<=H entails y<=T(y,y,y), with
H=T(M,M,M), M=T(bottom,bottom,bottom), and binary countervalue {epsilon,0,01}.
Compare the new summary predicate against independently saturated P-automata
and literal finite-graph models. Check binary absorption on every physical
state, complete words, incomplete words, diagonal/empty suffixes, infinite
regular values, bottom children, mixed constraints and fresh naming.
Bounded tests cannot establish an all-input decision result.

Opposing route: the naive encoding obstruction does not exclude another
homomorphic encoding. If this route is correct, undecidability in this exact
signature is excluded by the reduction and C081, but no conclusion follows
for labels, variance, explicit top or finite-valued semantics.

Review: separate algorithmic checks will be run; independent mathematical
review has been requested in #72 and is pending. There is no installed Lean
or Lake and no complete local checkout. Do not count inherited receipts as a
new Lean run. The most useful selective formalization target is the binary
coding/completion theorem with its exact strong-absorption hypothesis.

## 1. Exact theorem and what kind of translation this is

**Ordinary theorem.** There is a total computable map R from finite ternary
bottom/constructor entailment instances (C,s,t) to finite binary
bottom/product entailment instances (D,a,b) such that

    C entails_3 s <= t    iff    D entails_2 a <= b.

Both sides quantify over ALL arbitrary prefix-closed constructor-address
sets, not just finite or regular trees. The map also preserves existence of
models. It has explicit countermodel maps in both directions. For each fixed
positive arity r, the same construction works with the code specified in
Section 10.

This is an automata-mediated, QUERY-DEPENDENT computable many-one reduction.
Its preprocessing invokes the already proved total BINARY C029 decision for
infinitely extendable witnesses. It does not invoke a ternary entailment
oracle or decide the remaining terminal branch. It is NOT a homomorphism of
individual type expressions, a polynomial-time reduction, a new complexity
bound, or a preservation of the values of every expression in every model.
The distinction is substantive: the naive homomorphic map below is false.

Status: full ordinary argument below, executable component evidence, independent
mathematical review PENDING. This note is not a new checked Lean theorem or an
integrated/established claim in the shared ledger.

## 2. Source domain and exact finite normalization

For A={0,1,2}, a value is any prefix-closed subset X of A*. An address records
a ternary CONSTRUCTOR node; absent nodes denote bottom. The empty value is
bottom, and

    T(X0,X1,X2) = {epsilon} union 0.X0 union 1.X1 union 2.X2.
    X <= Y iff X is a subset of Y.

The sets can be infinite and nonregular. Every nonempty such set decomposes
uniquely into a root constructor and three prefix-closed child sets. Finite
expressions use variables, bottom and T. A single valuation interprets all
premises and the query. Entailment means every valuation satisfying all
premises satisfies the query; inconsistent premises entail it vacuously.
The binary target replaces A by {0,1}, T by the binary product P, and has
exactly the same node-set convention. No explicit top or additional label is
introduced.

Densely rename the v actually occurring variables, including query-only
variables. Introduce one shared name z with z<=bottom. Introduce one fresh
name p for every constructor occurrence T(e0,e1,e2), recursively name its
children p0,p1,p2, and insert BOTH inequalities

    p <= T(p0,p1,p2),       T(p0,p1,p2) <= p.

Use z as the name of every bottom occurrence and the original name for every
variable occurrence. Replace each original inequality by the inequality of
its two names. Name the query as a<=b but do not insert it as a premise.
The resulting clauses have the four forms x<=y, x<=T(y0,y1,y2),
T(y0,y1,y2)<=x, and x<=bottom.

**Naming lemma.** Any original model extends by assigning the interpretation
of each named expression to its new name. Conversely any normalized model
restricts to the original variables, and structural induction identifies the
value of EACH fresh name with the corresponding expression. For bottom, the
single denial makes z empty. At a constructor the two inequalities give
literal equality. This works simultaneously for all occurrences, including
repeated variables, duplicated expressions and query-only names. It preserves
query truth and every separating address. It also preserves finiteness for
THIS normalization step, but that is not a finite-tree claim about R.

If t is the number of constructor occurrences across the input and query,
normalization uses n=v+t+1 names and m+2t+1 clauses, where m is the number of
original premises. In a tree-syntax encoding of length L, n<=L+1. Sparse
binary variable identifiers are renamed rather than enumerating unused IDs.

## 3. Canonical closure over the ternary alphabet

Use n controls, one per normalized name, and configurations (q,u), u in A*.
The first letter is the top of the stack. Define a finite system W as follows:

- x<=y gives (x,u)->(y,u) for all u (an epsilon rule).
- x<=T(y0,y1,y2) gives (x,i.u)->(yi,u) (a pop-i rule).
- T(y0,y1,y2)<=x gives (yi,u)->(x,i.u) (a push-i rule), and forces
  the root (x,epsilon).
- x<=bottom declares x a denied control.

Let F be the forced controls and D the denied controls. Every push targets a
member of F. Write W^op for the exact reversed configuration relation;
reversing a push gives a pop and reversing an epsilon rule reverses its edge.

For a finite seed set S containing all (f,epsilon), f in F, put

    L_S(q) = {u : some seed in S reaches (q,u) by a finite W path}.

Assume the seeds are prefix-closed within each control. Then every L_S(q)
is prefix-closed. Proof by induction on the length of a deriving path: an
epsilon rule carries each prefix unchanged; a pop from i.u carries any
prefix i.v to v; a push to i.u carries nonempty prefixes from prefixes of u,
while its empty prefix is a forced root at the push target. This last root
condition is essential. It is not an arbitrary-PDS prefix-closure assertion.

The valuation L_S satisfies every positive normalized clause, by closure
under its corresponding rule and the forced-root condition. It satisfies
the denials exactly when L_S(d) is empty for every d in D. Every model
containing the seeds contains L_S, by induction on reachability paths.

Consequently the premises are satisfiable exactly when the forced-root
closure L_F avoids D. For a word w, define

    S_w = {(f,epsilon):f in F} union {(a,u):u is a prefix of w}.

A model separates a from b at w exactly when L_(S_w) avoids every denied
control and omits (b,w). For the forward direction a separating model contains
ALL the seeds, hence their closure, so safety and omission follow. For the
reverse direction L_(S_w) itself is the required model and contains (a,w).
No finite-height or regularity assumption is used.

### 3.1 Effective balanced and Pop relations

Balanced E_W(p,q) is the least relation generated by identities, epsilon
rules, transitivity, and

    push_i(p,p'), E_W(p',q'), pop_i(q',q) => E_W(p,q).

It is computable by finite saturation of n*n pairs. Its exact meaning is a
path from (p,epsilon) to (q,epsilon); equivalently a path from (p,z) to (q,z)
which does not pop the protected suffix z. Soundness follows by lifting
paths. For completeness split a nonempty empty-to-empty path at its initial
epsilon step, or at the pop matching its first push; the interior and
remaining path give the induction. Transitivity handles their concatenation.
Reversal gives E_(W^op)=transpose(E_W).

Pop_W(p,x,q) is the language recognized by the epsilon-NFA on the n controls
with E_W as epsilon edges, the W pop-i rules as i-labelled edges, initial p
and accepting q. Thus it allows balanced segments before, between AND after
pops. It consumes x and removes precisely x above any protected suffix.

**Minimum-stack factorization.**

    (p,u) reaches_W (q,v)
      iff exists x,y,z,h:
        u=x.z, v=y.z, Pop_W(p,x,h), Pop_(W^op)(q,y,h).

For a finite path choose a point of minimum stack height. The suffix z below
that height is never touched. The first half consists of balanced segments
and unmatched pops of x, split at each new minimum height. Reverse the second
half to obtain the corresponding decomposition consuming y. Conversely lift
the two Pop paths above z and reverse the second. This proves BOTH directions
and works for the empty word and repeated visits to the minimum height.
It is an ordinary finite-alphabet proof, not an assumed Lean generalization.

### 3.2 The exact SAT test

Let R=E_W(F), the epsilon closure of forced controls. Let H contain h whenever
Pop_(W^op)(d,y,h) holds for some d in D and some word y. Compute H by ordinary
finite reachability from D in the reverse Pop NFA, forgetting edge labels.
By factorization with the initial stack empty,

    source SAT iff R intersect H is empty.

This is a terminating finite-graph computation. Its use cannot be dropped:
an unrelated forced denial can make the source inconsistent even when the
query's seed-summary automaton has witnesses (the regression preserves this).

## 4. A fully specified absorbing ternary summary

States are ALL pairs (A,B) of control subsets, K=4^n states. The initial state
is (E_W({a}), E_(W^op)({b})). For letter i, define

    next_W(A,i) = E_W(pop_i(E_W(A))),
    next_rev(B,i) = E_(W^op)(pop_i_rev(E_(W^op)(B))).

The transition sends (A,B) to (next_W(A,i),next_rev(B,i)); it is total.
Epsilon closure before as well as after the pop makes the definition valid
on unreachable physical states too. Define

    Bad(A,B)       iff A intersects H,
    Final(A,B)     iff B is disjoint from R,
    G((A,B),(A',B')) iff A intersects B'.

G is ORDERED. On the run for w, the components at cut i are exactly

    A_i = {h:Pop_W(a,w[:i],h)},
    B_i = {h:Pop_(W^op)(b,w[:i],h)}.

For any finite-alphabet instance, Witness(w) means: the run is defined at
every cut, no cut is Bad, the last state is final, and

    for every 0<=i<=j<=|w|,
    if w[j:] is a prefix of w[i:], then not G(q_i,q_j).

This is precisely [Basic.Witness](../lean/Subtail/Basic.lean), with the
alphabet changed and nothing else. It includes i=j, j=|w|, w=epsilon, every
prefix, every ordered flag and overlapping occurrences. In particular every
visited state is safe: not Bad and not diagonally flagged.

**Summary lemma (WITH source SAT).** A word w is a summary witness iff some
source model separates a from b at w.

Proof: factorization says a query seed prefix can reach a denial iff some
A_i intersects H; the fact that every prefix of w is itself a seed removes
the unused suffix in this test. Forced-root reachability of (b,w) is exactly
B_|w| intersect R nonempty. Finally a query seed x.z that is a prefix of w
reaches (b,w) iff w=y.z and Pop_W(a,x,h), Pop_rev(b,y,h) for some h. Set
|x|=i, |y|=j. The condition x.z prefix w is exactly i<=j and
w[j:] prefix w[i:], and the common h is exactly G(q_i,q_j). Conversely each
such flagged pair reconstructs that seed and path. The SAT hypothesis handles
forced-root denial safety, not merely query-seed safety. Combine with the
canonical model lemma. This is a single model for the whole conjunction, not
independently chosen models for individual clauses.

**Strong absorption on ALL physical states.** If (A,B) is final, its successor
has second component empty. Indeed a reverse pop starts at a target f of an
original push, hence f in F. If E_rev(B) contained such an f, some b in B
would satisfy E_W(f,b), so b in R, contradicting finality. Thus no reverse
pop can occur. An empty second component is final and its entire incoming
flag column is empty. This is the exact strong hypothesis in
[AbsorbingTerminal.Absorbing](../lean/Subtail/AbsorbingTerminal.lean), not just
closure of final states or safety along reachable runs.

## 5. Binary coding with safe completion

This section takes ANY finite ternary absorbing instance I, not necessarily
a summary. Use the complete prefix code

    c(0)=0, c(1)=10, c(2)=11,

extended by concatenation. Create two states B_q and M_q per state q. B means
a code boundary and M means the unfinished code prefix 1. The binary initial
state is B_s. Define all transitions, allowing undefined originals:

    B_q --0--> B_delta(q,0)      if delta(q,0) is defined,
    B_q --1--> M_q               always,
    M_q --0--> B_delta(q,1)      if defined,
    M_q --1--> B_delta(q,2)      if defined.

At boundaries, copy Bad and Final. Copy flags ONLY between boundaries:
G'(B_p,B_q)=G(p,q); every flag involving an M state is false. At M_q put

    Final'(M_q) iff Final(q),
    Bad'(M_q) iff neither delta(q,1) nor delta(q,2)
                  is a defined safe original state.

Safe means neither Bad nor diagonally flagged. The target J has k=2K states.

**Lemma 5.1 (strong absorption).** If B_q is final, its 0-successor is a final
boundary with an empty incoming flag column by original absorption; its
1-successor M_q is final and has no incoming flags by definition. If M_q is
final, q was final, so its defined boundary successors are final with empty
columns by original absorption. This argument includes bad and unreachable
final states. Making intermediate states nonfinal would FAIL this hypothesis.

**Lemma 5.2 (complete words).** For EVERY word w,

    Witness_I(w) iff Witness_J(c(w)).

At boundary cuts the run and Bad/final tests agree. If w is a witness, an
intermediate state has the actual next safe boundary as a completion, so it
is not Bad. Conversely boundary cuts of a binary witness are safe original
cuts. The only nontrivial flags are between boundaries. Since the code is
prefix-free, c(v) prefix c(u) iff v prefix u: parsing a complete coded prefix
recovers exactly its source letters. Consequently every relevant ordered
suffix-prefix comparison is equivalent. Intermediate cuts impose no extra
flag conditions. Empty source/binary words and empty suffixes are included.

The lemma alone is insufficient: J also permits witnesses ending between
code boundaries.

**Lemma 5.3 (safe extension).** In any absorbing instance, appending a
transition to a safe state preserves Witness. The new final state and its
empty incoming flag column come from absorption. For old cuts i<=j, agreement
of the new LONGER suffix implies agreement of the old suffix, by truncating
to |w|-j symbols; hence no formerly safe comparison becomes forbidden. The
new terminal cut has an empty incoming column, and its safety is stipulated.
Induction gives preservation along any finite safe continuation.

**Lemma 5.4 (ALL binary witnesses decode after completion).** Every binary
word with a defined J run has the unique form c(w) or c(w).1. In the latter
case its endpoint M_q is final and not Bad. Therefore q is final and there
is a bit b completing the prefix to a safe boundary successor. Appending b
preserves Witness by Lemmas 5.1 and 5.3. The result is c(wi) for i=1 or 2,
and Lemma 5.2 makes wi an original witness. Thus

    exists u Witness_J(u) iff exists w Witness_I(w).

This is NOT a truncation argument. For example take source states 0,1,2,
initial 0, finals {1,2}, no Bad states, only flag (0,1), transitions
0--0-->1 and 1--1-->2, and all other transitions undefined. It is absorbing.
The binary partial word 01 is a witness, but its truncated source word 0 is
not (the flagged empty suffix blocks it). Completing to 010 gives source
word 01, which IS a witness. This fixture is independently executed.

Finally no safe M_q can be a terminal final of terminalize(J): its safe
completion is still an outgoing edge. Therefore terminalized witness words
end at boundaries. The general completion lemma is nevertheless needed for
the unterminalized J and the C029 preprocessing branch.

## 6. Exact target constraints and total reduction

Use the following EXISTING binary results at the pinned source revision:

1. C029, `InfiniteDecision.infiniteWitnessCheck_correct`: for an absorbing J,
   the total Boolean h(J) is true exactly when J has an original witness
   followed by a safe finite stem and a nonempty safe cycle (InfWitness).
   No bound on the original prefix is supplied by the caller.
2. C031, `AbsorbingTerminal.c031`: for absorbing J, original witness existence
   is equivalent to InfWitness(J) OR witness existence in terminalize(J).
   The latter retains original flags/Bad/initial, prunes edges with unsafe
   source or target, and marks only safe ORIGINAL finals with no retained edge.
3. C030, `TerminalRealization.witness_iff_separating` and
   `realization_satisfiable`: the direct binary terminal realization is always
   satisfiable and has exactly the same separating words as the terminal
   instance. Every final must be terminal; ordered flags and Bad are unrestricted.
4. C081, `EntailmentDecision.entailsCheck_correct`: the resulting finite
   binary-expression instance is decidable over arbitrary binary trees.

The first three are [recorded exactly in the ledger](../research/claims.md#c029).
The [C030 construction](2026-09-05-terminal-realization.md) is used literally;
its historical header predates the later checked satisfiability/separation
proof. Budget preservation and arbitrary-final realization are NOT imported.

Here is the complete reduction R(C,s,t):

    N,a,b := exact ternary normalization(C,s,t)
    if the finite forced-closure SAT test fails:
        return ({ P(bottom,bottom) <= bottom }, bottom <= bottom)
    I := the ternary subset-pair summary(N,a,b)
    J := binary coding(I)
    if InfiniteDecision.infiniteWitnessCheck(J) = true:
        return (empty premises, P(bottom,bottom) <= bottom)
    T := AbsorbingTerminal.terminalize(J)
    return (C030_constraints(T), a_initial <= v_initial)

Both fixed outputs have no variables. The first has no model, retaining
vacuous entailment; the second has a model and its query fails at epsilon.
The preprocessor does NOT consult the binary terminal decision or a source
entailment decision. C029 is part of the reduction's runtime, not an external
unproved oracle. All its hypotheses were proved in Sections 4 and 5.

For completeness the last line's finite constraints are as follows. Let T
have k states, initial s, terminal finals Fin, partial transitions delta,
flags G and Bad set. Use 2k+1 variables a_q,v_q (q in Q) and b0. Add:

    b0 <= bottom;
    a_q <= A(delta(q,0)) x A(delta(q,1))           for every q;
    V(delta(q,0)) x V(delta(q,1)) <= v_q          for q not in Fin;
    a_p <= v_q                                   for (p,q) in G;
    a_q <= bottom                                for q in Bad.

A(undefined)=V(undefined)=b0; A(q)=a_q and V(q)=v_q. The query is a_s<=v_s.
All these expressions are binary bottom/product expressions accepted by C081.
The auxiliaries are NOT constrained to be images of ternary trees. C030's
universal model statement is exactly what handles their unrestricted values.

## 7. Entailment proof and ordinary model maps

If N is inconsistent, exact naming makes C inconsistent and the selected
binary output is inconsistent, so both entailments hold. Suppose N is
satisfiable. Sections 3--5 give

    not Entails_3(C,s,t)
      iff exists w Witness_I(w)
      iff exists u Witness_J(u).

If h(J)=true, C029 supplies the rightmost witness, so source entailment fails;
the fixed output's query also fails. If h(J)=false, C031 and C030 give

    exists u Witness_J(u)
      iff exists u Witness_terminalize(J)(u)
      iff not Entails_2(C030(T),a_s,v_s).

These equivalences prove the theorem by classical negation. They include
inconsistent-premise vacuity; the SAT branch cannot be omitted. Source SAT
also implies target SAT, by the fixed negative instance or C030. Target SAT
implies source SAT because the only output for source inconsistency has no
model. Thus satisfiability is preserved too.

Here are the maps behind the existential equivalences. They transform
MODELS/COUNTERMODELS, not just answer bits. Arbitrary uncomputable tree values
are treated set-theoretically. The procedures are effective when a finite
separating address is supplied and the remaining objects are finitely given.

### Source countermodel to a target countermodel

Extend a source countermodel by naming and choose a separating address w.
The summary lemma gives Witness_I(w), and coding gives Witness_J(c(w)).
If h(J)=true, use the unique empty-variable valuation of the fixed negative
output, whose query fails at epsilon.

If h(J)=false, no safe cycle can be reached from the endpoint of this witness:
otherwise that same witness, a path to the cycle and the cycle would be
InfWitness(J). The reachable safe graph is therefore acyclic. Follow a safe
path to a sink, of length at most k-1. Absorption keeps it final and Lemma 5.3
preserves Witness. The resulting word u is a witness of T. C030 supplies its
canonical binary countermodel separating a_s from v_s at exactly u. The
binary separating word has length at most 2|w|+k-1; this is a map-specific
estimate, not a bound on the shortest source witness.

### EVERY target countermodel to a source countermodel

There are no countermodels for the inconsistent output. In the fixed negative
branch, h(J)=true supplies some J witness. One can find one effectively by
shortlex enumeration, testing Witness and reachability of a safe cycle from
its endpoint; C029 proves termination. Complete an unfinished codeword as in
Lemma 5.4 and decode it to a source witness w. In the C030 branch, take ANY
binary valuation satisfying the generated constraints and failing a_s<=v_s.
Choose ANY finite separating address u. The exact C030 theorem gives
Witness_T(u), hence Witness_J(u). Terminalized witnesses actually end at a
code boundary; alternatively the general completion lemma suffices. Decode
to w and build L_(S_w). Sections 3 and 4 prove that this ONE valuation
satisfies every normalized premise and separates a,b at w. Restriction gives
a model of every original premise and falsifies the original query.

This argument applies regardless of the shapes of the target auxiliary
values, including infinite nonregular values and incomplete binary-node
patterns. No encoded-image assumption or hidden shape guard is used. Different
target values may map to the same canonical source countermodel; injectivity
and a valuation-level inverse are not claimed or needed.

### Maps on non-countermodels and regular representations

When the source is satisfiable its forced closure is a fixed baseline source
model. C030 has a baseline target model: all a_q and b0 empty, v_q the least
solution of its lower-product constraints. In the fixed negative branch the
empty-variable valuation is the baseline. Extend the two countermodel maps to
all premise models by using these baselines in the non-countermodel case.
Thus the maps preserve premises and map countermodels to countermodels.
They do NOT necessarily preserve the truth of the query on every other
valuation (in particular the fixed negative target always falsifies it).
This is explicit; no pointwise semantic interpretation is being asserted.

Each canonical model used here has an effective regular representation. For
control q and a finite seed (p,u), factorization gives the exact language

    union over u=x.z and h with Pop_W(p,x,h)
       {y: Pop_(W^op)(q,y,h)} . {z}.

Each term is an n-state Pop epsilon-NFA followed by a finite suffix path.
There are finitely many seeds/splits/controls. Take their union and determinize.
Prefix closure was already proved semantically; turn accepting DFA states
into constructor nodes and rejecting successors into bottom. This finite
graph has exactly the canonical constructor-address language, including all
cycles. The same construction applies on the binary C030 side. It supplies
regular countermodels even when the initial source/target valuation was
nonregular; it does not assume all valuations are regular.

## 8. Effectiveness, output size and limits

All normalizations, finite relation closures, subset enumerations, coding,
terminalization and final constraint emission terminate. C029 is a total
computable binary function on these finite instances. Therefore R is total.
An operational timeout in an implementation would be UNKNOWN, not a Boolean
answer and not a step in the mathematical reduction.

For ternary inputs normalized to n names, K=4^n and k=2K. The nonconstant
output has exactly 2k+1=4*4^n+1 variables, and

    1 + k + (k-|Fin|) + |G| + |Bad| <= 1+3k+k^2

constraints. Each has a constant number of binary-expression nodes. With
dense binary variable indices its serialized length is O(k^2 log k), hence
O(n*16^n). The fixed branches have constant size. These are conservative
OUTPUT bounds, not bounds on C029's preprocessing time or memory. They do
not establish a PSPACE reduction, a matching complexity class, a practical
solver, or a source witness-length bound. Reachable-state restriction could
reduce a concrete output, but is not used in this stated full-carrier bound.

## 9. Failed homomorphic encoding and small examples

The natural candidate replaces T(x,y,z) by x x (y x z), with variables and
bottom unchanged (the infix x here denotes binary product). More unambiguously:

    E(T(X,Y,Z)) = P(E(X),P(E(Y),E(Z))).

On source values its address-set map is

    E(X) = {c(w).d : w in X, d in {epsilon,1}}.

Prefix-free parsing proves that this map preserves and reflects inclusion
on its image and commutes with the constructors. This does NOT prove
entailment, because target variables need not lie in that image.

Let M=T(bottom,bottom,bottom), H=T(M,M,M). The source input

    premise y<=H; query y<=T(y,y,y)

is entailed. Every y<=H is either empty or contains epsilon; all its other
possible addresses have length one, and hence belong to the corresponding
child copy of y. Equivalently there are exactly nine such source values.
The binary value Y={epsilon,0,01} satisfies Y<=E(H) but not
Y<=P(Y,P(Y,Y)): address 01 is missing on the right because 1 is missing in Y.
This is a finite countermodel, with three product nodes. The only
prefix-closed binary values with at most two product nodes are empty,
{epsilon}, {epsilon,0}, {epsilon,1}; all satisfy Y<=P(Y,P(Y,Y)). Three nodes
are therefore minimal for THIS instance, not globally across all encodings.

Independent infinite graph fixtures include x=T(x,bottom,bottom), its other
two spines, x=T(x,x,x), and mixed inequalities with a bottom-valued auxiliary.
They are checked by finite graph-pair reachability at all depths, including
non-root separating addresses 0, 1 and 22. Query-only expression names and
an inconsistent forced-constructor/bottom conjunction are also checked.
A nonregular value is equally admissible, for example
{0^n:n>=0} union {0^n1:n is a square}; the ordinary set proof applies without
requiring any graph representation of that input value. This last example is
an explanatory mathematical example, not an executed all-depth graph test.
It is nonregular because finitely many distinct subtrees on the zero spine
would make the square-indexed side branches eventually periodic, whereas
the gaps between squares are unbounded.

Finite-tree claims are deliberately separate. The spine equation has no
finite solution, whereas it has the infinite countermodel above. C030's
baseline and reconstructed models may be infinite even for finite source
countermodels. No reduction of finite-valued entailment is claimed. The
naive counterexample, in contrast, is already finite on both sides.

## 10. The same proof for each fixed positive arity

For r>=2 use the binary comb code

    c(i)=1^i.0 for 0<=i<r-1; c(r-1)=1^(r-1).

There are r leaves and r-1 proper-prefix states, including epsilon. Use
(q,p) for every original state q and every proper code prefix p. Boundary
states have the original Bad/final/flags. At nonempty proper prefixes inherit
final(q), have no incident flags, and mark Bad exactly when no descendant
code leaf leads to a defined safe source successor. A bit either extends
p to another proper prefix or finishes a leaf and makes the corresponding
source transition. Unavailable transitions are undefined.

Strong absorption follows as before: within a codeword finality is inherited,
and at a leaf it follows from source absorption. A complete encoded source
witness has safe intermediate prefixes because its actual boundary successor
is a safe completion. Any target witness ending within a codeword has some
safe descendant leaf. Along that completion every intervening prefix also
has that leaf as a safe completion; every new internal flag column is empty,
and the final boundary column is empty by absorption. Lemma 5.3 repeatedly
preserves Witness. Prefix-free parsing gives the same agreement equivalence.
The generic finite-alphabet canonical proof in Sections 2--4 used no ternary-
specific identity. This proves, rather than merely suggests, the corollary.

For r=1 use c(0)=0, one boundary state per source state, and undefined binary
1-transitions; there are no intermediate states. The same conclusions follow
directly. Thus k=max(1,r-1)*4^n and output variables are at most 2k+1, with
the same 1+3k+k^2 constraint bound. The input arity is fixed in each theorem.
No nullary extension, multiple labels, top or contravariance is covered.

## 11. Evidence, review boundary and selective formalization

Run from the repository root:

    python3 experiments/ternary_transfer.py --output results/ternary-transfer.json

The [receipt](../results/ternary-transfer.json) pins the script hash, upstream
base, seed, bounds, environment, exact counts and NOT RUN items. The script
compares the subset-pair construction with a DIFFERENT Post* NFA saturation:
epsilon rules add reversed epsilon edges, pushes add reversed labelled edges,
and pops add epsilon successor-copy edges until a finite fixed point. It then
checks produced regular trees using graph-pair reachability, not word-depth
sampling. The two algorithms share the intended normalized clauses, but not
the balanced/minimum-stack summary implementation.

The binary coding tests include all one-state absorbing encodings at arities
1--4 and seeded multi-state examples through arity 5; complete words and
partial binary witnesses have separate checks. These are bounded finite
families, not an all-instance mathematical review. The nine bounded source
values for the naive counterexample form a COMPLETE corpus only because H
is an explicit finite upper bound. A generic depth-bound census has no such
completeness status.

[Review record](2026-09-20-ternary-transfer-review.md) distinguishes same-author
adversarial readback, independent-algorithm checks, pending external review,
and unexecuted Lean validation. No additional reviewer was launched. No Lean
build/kernel replay or actual C029 execution occurred in this environment.
The test harness is not advertised as a complete command-line translator;
Section 6 is the total algorithm, using the existing C029 executable.

The narrow useful formalization target is a new isolated finite-alphabet
instance/coding module, with declarations equivalent to:

    encode_absorbing : Absorbing3 I -> Absorbing (encode I)
    witness_code_iff : Witness (encode I) (code w) <-> Witness3 I w
    witness_complete_decode : Absorbing3 I -> Witness (encode I) u ->
      exists w, Witness3 I w and
        (u=code w or exists bit, u++[bit]=code w)

The second lemma does not require absorption; the first and third do. Do not
weaken strong absorption or silently generalize Basic.Word. The existing
binary core stays unchanged. A later full formalization must additionally
connect the generic canonical bridge, SAT branch and C030 composition; coding
lemmas alone would not certify the full theorem.

## 12. Source mapping and next acceptance step

The new mathematical work here is the explicit finite-alphabet bridge,
absorption-preserving binary coding with completion, and its composition as a
query-dependent reduction. Normalization/canonical reachability ideas and all
binary C029/C030/C031/C081 results are inherited and credited. The existing
[extension study](2026-09-19-post-c081-extensions.md#4-other-signatures-separate-obligations)
listed generic-arity proof obligations but did not prove this reduction.
The pinned A010/A011/A018 histories and C081 ledger were read.

A public primary-source metadata search also located Niehren--Priesnitz,
*Entailment of Non-Structural Subtype Constraints* (ASIAN 1999), publication
record https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment%3A99.html .
Its abstract concerns a restricted PSPACE-complete subproblem; no theorem
from that paper is imported here, and the search/abstract is NOT a global
priority audit or evidence of a prior arity transfer. This note asserts no
novelty or new hardness/complexity classification.

Next acceptance obligation: an independent reader should audit the all-target
countermodel direction, source SAT guard, and strong-absorption/partial-code
lemmas against the exact binary definitions. Shared-state promotion and any
new claim ID remain the integrator's decision after that review. Issue #72
continues to contain other, untouched extension problems.

### Executed full-carrier off-image reconstruction fixture

For y<=T(bottom,bottom,bottom), query y<=bottom, the checker constructs the
full 64-state source summary and 128-state binary coding, then emits all
257 C030 variables and 2,697 constraints. Its exact binary graph satisfies
every emitted constraint; the left query tree has epsilon but not address 1,
so it is outside the naive encoding image. Decoding its separating address
and rebuilding the source closure gives a genuine original countermodel.
Here C029's false outcome is independently justified by the safe initial
sink; the general C029 executable was not run. A separate explicit safe
lasso exercises the true branch, and a forced denial exercises the UNSAT
branch. These are full pipeline FIXTURES, not an all-input native run.
