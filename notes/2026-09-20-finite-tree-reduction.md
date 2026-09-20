# Finite-tree entailment by excluding unbounded growth

Date/author: 2026-09-20, finite-trees-20260920. A010/A018; #58/#37.
Base: bb9295429ccdeb0cdbad5655e30582eaf77f6361.
Status: ordinary proof independently reviewed; formal and executable evidence
are recorded separately in the accompanying readback.

## 1. Exact statement

Let C be a finite list of normalized constraints over n variables, bottom and
one covariant binary product. A tree is a prefix-closed set of product
addresses in {0,1}*. It is finite exactly when its product-address lengths are
bounded. Write FinModels(C) for satisfying valuations assigning a finite tree
to every variable, and FinEntails(C,a,b) for universal inclusion over these
valuations. The arbitrary-tree predicates have their existing meanings.

Let W=systemOf(C). It has epsilon, push and pop rules on n controls, with the
stack's first letter on the left. A lower clause (x_l × x_r <= x_p) forces a
product root at p and gives pushes l -0-> p and r -1-> p. An upper clause gives
the corresponding pops; a variable inequality gives an epsilon rule. Denials
constrain trees to bottom but add no propagation rule. Let W^op reverse each
rule, exchanging push with pop.

Define L(q,m) = {w : Pop_(W^op)(q,w,m)}, where Pop means reachability from
(q,w) to (m,epsilon). Construct the epsilon NFA described below. Let Growth(C)
mean it has a cycle that consumes at least one letter. Then

**Theorem (finite-tree reduction).**

    FinEntails(C,a,b) iff Growth(C) or Entails(C,a,b).
    FinSatisfiable(C) iff not Growth(C) and Satisfiable(C).

Both equivalences are unconditional. In particular, no satisfiability promise
is required. If Growth(C) is false and C fails to entail a<=b, its canonical
countermodel from any separating address is finite. The equivalences extend
to every finite-expression input under exact definitional normalization.

This does not say that every arbitrary model is finite when Growth(C) is
false. For example, an unconstrained variable may still denote an infinite
tree. It says finite canonical replacements suffice for failed queries and
satisfiable inputs in that case.

## 2. Effective finite growth test

The NFA has state set {0,...,n-1}, alphabet {0,1}, epsilon edges equal to the
least balanced relation of W^op, and an a-edge p->r for every pop-a rule of
W^op. For L(q,m), q is the initial state and m the only accepting state.
Balanced means a run that starts and finishes at the same stack suffix without
popping below it. Finite balanced saturation computes the epsilon relation.
The Pop induction shows that the NFA accepts exactly L(q,m).

Let T be reflexive transitive reachability ignoring letters in this NFA.
Compute T by finite graph closure. Growth(C) holds exactly when some letter
edge p -a-> r satisfies T(r,p). This test terminates and is effective from C.
An epsilon-only cycle is insufficient. Balanced stack excursions may grow and
shrink the stack internally, but they consume no letters in this NFA.

If no consuming cycle exists, every accepted word has length less than n.
Indeed, an accepting run consuming n letters has n+1 boundary states: its
initial state and a state after each consumed letter and the following epsilon
segment. Two boundaries coincide, producing a subrun that consumes at least
one letter. Conversely, a consuming cycle can be repeated arbitrarily often.
This also covers n=0 vacuously, since there are no states or accepted words.

The implementation returns a witness p and nonempty word w for a positive
test. It records the first letter edge, finds a return path from r to p, drops
that path's epsilon labels, and prefixes a. A separate Pop evaluation checks
Pop_(W^op)(p,w,p). The finite graph argument establishes completeness; this
extra evaluation only validates the supplied loop.

## 3. A consuming cycle excludes all finite models

Choose a letter edge p -a-> r on a consuming NFA cycle. It is a pop of W^op,
so it reverses a push into p in W. Every such push comes from a lower product
clause. Thus p is a forced product root: every C-model contains (p,epsilon).
This property is specific to the normalized bottom/product propagation system;
an arbitrary pushdown system need not have it.

The entire cycle supplies a nonempty w with Pop_(W^op)(p,w,p). Reversal and
suffix lifting give, for every suffix z, a W-run

    (p,z) ->* (p,w z).

Propagation preserves membership in every C-model. Repeated application at
the forced root therefore makes w^k a product address at p for every k>=0.
These addresses have unbounded length, contradicting finiteness of p's tree.
Hence Growth(C) implies there is no finite C-model. Every finite-tree query is
then entailed vacuously, whether or not C has an arbitrary model.

## 4. No consuming cycle bounds finite-seed closures

For a finite seed family S of configurations, let cl_W(S) be all configurations
reachable from S. Suppose every seed word has length at most d. The existing
minimum-stack factorization says a run (p,u) ->* (q,v) has witnesses x,y,z,m
such that

    u = x z,    v = y z,
    Pop_W(p,x,m),    Pop_(W^op)(q,y,m).

Here z is a suffix of u; its orientation is important. In the no-growth case,
Section 2 gives |y|<n. Consequently |v|=|y|+|z|<n+d. There are only finitely
many binary words below that length and finitely many controls, so cl_W(S) is
finite. With no seeds its closure is empty. No numerical bound on the length
of a separating query address is needed for this argument.

For forced-root seeds alone, d=0: the least model, when safe, has tree height
at most n. For a prefix-seeded countermodel at address pi, d=|pi|: the
canonical trees have height at most n+|pi|. These are bounds in terms of the
supplied seed, not a new global shortest-counterexample bound.

## 5. Model and entailment transfer

If C has an arbitrary model, the reachability closure of its forced-root
seeds is prefix closed, satisfies the propagation clauses, and avoids all
denials. These are the existing canonical-model lemmas. Its trees are subsets
of every C-model. When Growth(C) is false, Section 4 makes this least model
finite. Conversely, a finite model is an arbitrary model. Together with
Section 3 this proves the satisfiability equivalence.

Suppose C fails to entail a<=b over arbitrary trees. Choose an address pi in
a's tree but not in b's tree in a countermodel. Seed every forced root and
all prefixes of pi at a. The original countermodel contains all these seeds.
By propagation soundness it contains their canonical closure. This closure
is therefore safe, contains pi at a, and omits pi at b. It is a C-model and
still refutes the query. If Growth(C) is false, Section 4 makes it finite.
Thus arbitrary non-entailment implies finite non-entailment in this case.
The converse follows because finite valuations are arbitrary valuations.
Together with Section 3 this proves the entailment equivalence.

## 6. Finite-expression normalization

For a finite syntax input, retain its original variables and give each named
subexpression its exact value. A bottom name is constrained by a denial.
A product name is constrained by both product directions. Premises become
inequalities between their names; the query names are not an extra premise.
The current Lean occurrence-table normalization and Python DAG normalization
use different indices but express these same definitional conditions.

An extension of a finite original valuation is finite: bottom has no product
addresses, and product of two finite trees has one new root and finite tagged
child address sets. Structural induction proves this for all subexpressions.
Conversely, restriction of a finite normalized valuation is finite, and its
definitional equations make each name equal to the corresponding evaluated
expression. Premise satisfaction and query truth are preserved both ways.
Thus the normalized theorem applies to original finite-expression semantics.
The finite preservation refinement for the existing Lean naming construction
is checked by `normalize_finite_entails_iff` in the new module. Correspondence
of the separate Python DAG implementation remains an ordinary proof.

## 7. The original hot-control route and its simplification

The initial target appended denials at H={m : some L(q,m) is infinite}.
For any finite S one has the more general, pushdown-level criterion

    cl_W(S) is finite iff it reaches no control in H.

If (m,z) is reached and m is hot, infinitely many words c in some L(q,m)
reverse to runs from (m,z) to (q,c z); these words remain distinct. Conversely,
minimum-stack factorization expresses the target language as a finite union
of L(q,m){z}, over seed suffixes and intermediate controls that are reached.
If none is hot, this union is finite. This is the selective formal target.

A finite C-model must satisfy x_m<=bottom for all m in H, since any product
occurrence there would produce infinitely many addresses. In the original
proposal, the augmented constraint list C_fin therefore has the same finite
models, and every arbitrary counterexample for C_fin has a finite canonical
replacement. Hence FinEntails(C,a,b) iff Entails(C_fin,a,b).

The signature gives more: H is nonempty exactly when a consuming cycle exists.
Such a cycle passes through a forced root p, and p itself is in H. Thus C_fin
is inconsistent when H is nonempty; otherwise C_fin=C. The original reduction
therefore collapses to the cycle gate of Section 1. The general closure
criterion remains useful independently of this signature-specific collapse.

## 8. Decision, examples and limits

Compute Growth(C). If true, answer ENTAILED with reason no_finite_model.
Otherwise call the existing C081 arbitrary-tree decision. Both stages are
finite effective algorithms, so this decides finite-tree entailment. A
negative result supports the existing canonical extractor; its output now
unfolds to finite trees. Check graph acyclicity only from original variable
roots: unused cyclic scratch nodes do not affect the valuation. Bottom has
height zero; an acyclic product node has one plus its maximum child height.

- Under x×bottom<=x, arbitrary entailment x<=bottom is false: the infinite
  left spine is a countermodel. A consuming reverse-pop loop forces that
  spine in every model, so the finite-tree answer is ENTAILED vacuously.
- Under x<=y, the query y<=x is false under both semantics. Assign bottom to
  x and bottom×bottom to y; the separating address is epsilon and height is 1.
- Under x×x<=bottom there is no model under either semantics, but the
  normalized system has no consuming cycle. Absence of growth alone therefore
  does not establish satisfiability.
- The ground query bottom×bottom<=bottom with no premises is false even with
  zero original variables. Its expression values are finite automatically.

The cycle test adds a finite polynomial graph calculation to the existing
arbitrary-tree decision; this is not a tighter classification of that
procedure's worst-case complexity. Operational time/memory caps still return
UNKNOWN. The C081 branch is Lean-checked; the whole finite-tree procedure,
Python normalization, growth classifier and graph-finiteness checker are not
yet Lean-verified. A C084 graph certificate proves arbitrary non-entailment;
the present extra acyclicity check is ordinary Python, not a kernel proof of
finite non-entailment. No explicit-top, multiple-constructor or variance
transfer follows. No novelty or publication-priority claim is made.

## 9. Evidence and next formal obligation

The read-only reviewer inspected the original route independently and then
reviewed the proposed cycle simplification, including the forced-root and
reversal arguments. The report is retained in the accompanying readback and
#58. This is independent mathematical review, not independent rediscovery.

E056 compares Hot with a separate predecessor-saturation language oracle and
compares finite satisfiability with exhaustive finite valuations on complete
small-input families. Its height cutoff is complete only for satisfiability
by Section 4. Unit tests also cover epsilon/balanced cycles, generic unforced
push systems, actual loop powers, graph cycles, vacuity and interrupted runs.
None of these finite checks proves the all-input theorem.

The new isolated Lean module targets the general closure criterion and finite
semantic corollaries. Its exact checked declarations, bounds and remaining
hypotheses are read back separately after compilation and kernel replay. The
next formal obligation is the finite graph classifier's connection to these
semantic predicates. Finite-preserving syntax normalization is already checked
for the existing Lean normalization, but the separate Python DAG naming still
has its ordinary implementation boundary. A conditional closure theorem does
not discharge the classifier obligation.
