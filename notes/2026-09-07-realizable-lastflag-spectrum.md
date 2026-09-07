# Exact realizable last-flag length spectra

Date: 2026-09-07. Base main: `8e6c2e6c13754436871ff440cd52cd3e60294a74`.
Workstream: A017, with an A012 limitation. No additional agents were launched.

**Status: written all-length proofs and executed independent-predicate checks;
independent mathematical review pending; not Lean-checked.** This is not a
resolution of unrestricted Problem 1.7. It gives a complete decision of one
structural property and a stronger sound partial witness decider. No literature
priority claim is made.

## 1. Target, dependencies, and the important quantifier distinction

The terminal model is the repository's partial deterministic automaton, with
ordered flags G, Bad states, and accepting states having no outgoing edges.
The proof works over any fixed finite alphabet; the reproduction is binary.
For each final f remove Bad, diagonally flagged states, and every p with
G(p,f), then trim to reachable/co-reachable states. This is C016 boundary
normalization. Different finals are separate slices, without adding a marker.

Fix one nonempty normalized slice J with k states and sole final f. For an
accepted word w with run c and length n, call i<j<n a **last-aligned-flag
comparison** when

    G(c(i),c(j)),
    w[j:] is a prefix of w[i:],
    not G(c(i+t),c(j+t)) for every 1 <= t <= n-j.          (1)

Define its realizable length spectrum

    Lambda(J) = {n-j : an accepted w and cuts i<j<n satisfy (1)}.

All cuts belong to ONE word w. In particular, two compatible-looking paths in
a synchronized graph are not automatically a member of this spectrum.

Every boundary-safe non-witness has such a comparison: choose a violation of
minimum target-suffix length; a later aligned flag would contradict minimality.
But a last-aligned-flag comparison need not be a globally shortest violation.
Other gaps in the SAME word may give much shorter violations. Section 6 gives
an explicit counterexample separating these notions.

Dependencies are the written terminal nonmerging/period argument C036/C038,
the C037 shortest-violation observation, the audited direct predicates, and
the exact periodic identity already used by the main-branch regular-family
checker. The proof below restates the relevant arguments. It does not use the
refuted sharp-budget/profile-descent hypotheses or any external word-equation
solver.

## 2. A finite exact template cover of ONE marked violation

Let d=w[i:j] be the nonempty gap word, z=w[j:] the nonempty target suffix,
and x=w[:i]. Agreement says z is a prefix of d z, equivalently z is a prefix
of d^omega. Divide |z| by |d|:

    d = u v,       v != epsilon,
    z = (u v)^(e-1) u,
    w = x (u v)^e u,        e >= 1.                     (2)

Here u is the possibly empty proper prefix remainder of d. The condition
v!=epsilon enforces |u|<|uv| without extra arithmetic. Conversely every
factorization (2), with z nonempty, provides the required suffix agreement.
It includes disjoint copies, overlap, and u=epsilon; no delimiter is inserted.

The states at positions |x|+h|uv|, h=0,...,e, are pairwise distinct. If the
states at h<h' agreed, determinism on (uv)^(e-h')u would reach terminal f
strictly before the complete word ended. Thus

    1 <= e <= k-1.                                      (3)

The head x needs only reach its chosen state in the safe slice. Shortening x
to another safe path to that state preserves the marked comparison. It may
change OTHER comparisons; preserving one bad comparison is all that is claimed.

### A joint finite action, not two independently chosen word values

Build one complete finite machine containing:

* the k single states of J, preserving its transitions;
* pairs (p,q) with p!=q and p!=f;
* one absorbing failure state.

A letter on a pair follows both transitions, but goes to failure if either
transition is undefined, the new left state is f, the two states merge, or
the destination pair belongs to G. A flagged pair may be a root; it may not
be entered after reading a positive number of letters. Endpoints (r,f) with
r!=f are allowed. Empty words leave their initial pair unchanged.

This machine has N=k+(k-1)^2+1 states. Let M be its finite transition monoid.
For each action A let

    U_A = {u : action(u)=A},
    V_A = U_A intersect Sigma^+.

These are regular languages recognized by the monoid's right Cayley graph.
Keep positive representatives separately, since a nonempty word can have the
identity action. Both the single-state and pair-state effects are computed
from the SAME word. This is the synchronization that independent residual
summaries would lose.

### Exact action test

For each reachable head state p, actions A,B with V_B nonempty, and
1<=e<=k-1, put q=delta(p,uv) using the single-state actions of u then v.
Require G(p,q), with q nonfinal and p!=q. From the pair root (p,q), apply the
action of (uv)^(e-1)u, using the SAME A and B at every occurrence. Accept the
template precisely when the result is some (r,f).

This test is necessary by (1)-(3) and the pair machine's definition. It is
sufficient because any u in U_A and v in V_B, substituted consistently into
(2), give a defined safe accepted word with the selected last-aligned flag.
The single action ensures that the first gap reaches q; the pair action ensures
that both copies match all the way to f and encounter no later aligned flag.
The terminal endpoint implies z!=epsilon. This proves both directions.

This is an exact finite cover of **marked bad comparisons**, not of all good
words, all residuals, or all minimum violations. It does not imply an
existence-preserving finite quotient of witness languages.

## 3. The spectrum is effectively unary regular

For an accepted action template (p,A,B,e), its exact set of target lengths is

    { e*m + (e-1)*n : m in Len(U_A), n in Len(V_B) }.     (4)

The two length variables are independent choices of factors; copies of each
factor subsequently use that one common choice. The coefficients are fixed
integers because e belongs to the finite range (3).

Each length set is unary regular: erase letter distinctions in its Cayley-graph
automaton. Multiplication of lengths by a fixed positive integer subdivides
each edge into that many unary edges; addition is concatenation. For e=1 the
second coefficient is zero, so only nonemptiness of V_B matters. Taking the
finite union of (4) yields an effective unary automaton for Lambda(J).
Equivalently the spectrum is effectively ultimately periodic (semilinear in
one dimension). This argument is specific to the displayed independent
regular fibres; it is NOT a claim that arbitrary word-equation length sets
are semilinear.

`length_schema` implements the finite Cayley-graph presentation and template
list. `spectrum_prefix` evaluates its exact intersection with [1,h]. This is
not a cutoff on candidate-word length or on the gap: when e=1, arbitrarily
long v still contribute if V_B is nonempty. The implementation does not
materialize a potentially much larger determinized unary automaton.

### Complete boundedness and exact maximum

An action fibre has unbounded word lengths exactly when a reachable directed
cycle can reach its vertex in the Cayley graph. The code computes this by
Kahn deletion: all vertices are already reachable from the identity, so the
survivors are exactly the vertices with cyclic ancestors. Finite fibres have
exact maximum lengths given by longest DAG paths.

Thus (4) is unbounded iff U_A is infinite, or e>1 and V_B is infinite. An
infinite V_B with e=1 does NOT make the target suffix unbounded. This zero
coefficient is a necessary implementation detail.

If every accepted template is bounded, their maxima give

    H = max Lambda(J), with H=0 when Lambda(J) is empty.

If M has m elements, a finite action fibre has maximum length <=m-1. Hence
for k>=2, whenever the spectrum is bounded,

    H <= (2k-3)(m-1) <= (2k-3)(N^N-1).                 (5)

This bound concerns the bounded comparison spectrum, not a universal
successful witness budget or a shortest good word. No polynomial complexity
claim is made.

For an unbounded term, a Cayley-graph lasso supplies
u=a b^t c or v=a b^t c, with b nonempty and t>=1. Its coefficient in (4) is
positive. Substitution in (2) produces actual accepted bad words with strictly
increasing marked suffix lengths. These are independently checkable pumping
certificates, not NO certificates for the original instance.

All the constructions are finite. With resource caps removed, boundedness,
maximum computation, and the schema construction terminate on every valid
terminal input. Caps return UNKNOWN; nonterminal finals are unsupported.

## 4. A strictly stronger partial witness decision

If Lambda(J) is bounded by H, then for every word w,

    Witness_J(w) iff Necessary_J(w,H,0).                (6)

The forward implication is the existing necessary-predicate theorem. For the
reverse, a boundary-safe non-witness has a globally shortest proper violation;
that violation satisfies (1), so its length is at most H and Necessary detects
it. Boundary failures already fail the necessary predicate.

The existing finite Necessary automaton therefore decides the entire slice.
Union over normalized finals is exact when all remaining slices are covered;
one positive slice suffices for YES, and an unresolved slice prevents NO.
Finite-graph exhaustion yields NO, while every cap remains UNKNOWN. Returned
positive words are checked by both the direct and reversed witness predicates.

C037's acyclic graph always bounds this realizable spectrum, so the new
criterion subsumes that criterion. It can be strictly stronger because it
checks the common-word constraint rather than only a pair path.

### Five-state strict example

Start 0, terminal final 4, no Bad states, and G={(0,1)}:

| State | 0 | 1 |
|---|---|---|
| 0 | 2 | 1 |
| 1 | 3 | 4 |
| 2 | 3 | 2 |
| 3 | 4 | 3 |
| 4 | undefined | undefined |

The old last-flag graph contains the productive cycle

    (0,1) --0--> (2,3) --1--> (2,3) --0--> (3,4),

so the acyclicity certificate is unavailable. State 1 is reachable from 0,
so its existing coarse occurrence-order filter does not remove this root.

Nevertheless any actual visit to target state 1 uses the INITIAL letter 1;
there is no other incoming edge to 1. Its nonempty suffix matches the whole
word's initial 1 only when the suffix itself is 1. Consequently 11 is the
only bad accepted word, and

    Lambda = {1};        H = 1.

All other accepted words are witnesses. The implementation returns the
three-letter witness 100. The long pair paths above follow the alternative
initial 0 branch, which never visits state 1 at all. This explains concretely
why they cannot realize the marked comparison in one word.

The original nonflat example is also decided YES with 0001101 and H=2; adding
its third flag yields NO with H=2. Those fixtures reproduce earlier results,
not new lower bounds.

## 5. What the implementation and finite checks establish

Commands, from the repository root:

    python3 experiments/check_lastflag_spectrum.py
    python3 experiments/run_experiments.py

The new deterministic result is `results/lastflag-spectrum.json`, seed
2026090719. It records:

* All 1,034 binary terminal transition tables/flag combinations through three
  states with fixed start 0, sole final k-1, and every effective off-diagonal
  nonfinal flag subset: 570 YES and 464 NO. There are 263,670 raw-word checks
  through length seven. Diagonal/Bad/multiple-final cases are tested separately.
* 240 complete acyclic-language oracles, including arbitrary boundary flags,
  Bad annotations, empty final sets, and multiple terminal finals. All 449
  accepted words are enumerated without a cutoff; exact maxima, exact spectra,
  and 126 YES/114 NO answers agree.
* 600 seeded additional terminal instances: 595 finite spectra and 5 unbounded
  spectra, with 153,000 raw-word comparisons through length seven and 248
  comparisons with the old graph certificate. The stated caps were not reached
  in this sample; this is not an all-instance census.
* All 746 pairs of total transformation generators on one through three
  points: 5,617 action-class classifications against a separate ancestor/DFS
  cycle oracle, and 15,354 lasso checks. This tests the finite/infinite fibre
  computation, including nonempty identity words.
* 133 directly attained maximum certificates, 40 instantiated pumping
  certificates, six analytic fixtures with 24,570 raw-word checks, 40 members
  of the Section 6 family, and nine scope/cap regressions.

The original border regression reproduces Git blob
`aa6d1680b5442493744c667024d2df77a1bd8e78` byte-for-byte: 10,160 word checks,
121,920 automaton comparisons, and its other recorded tests. The recovered
`border_lab.py` and `run_experiments.py` were verified against their original
Git blob hashes before execution; neither is changed by this contribution.

The new proof is a written argument, not established by these finite counts.
The reversed-border and finite-language oracles are independent algorithms,
not an independent human proof review. Work used a partial local snapshot;
no full repository CI, global link scan, or Lean build is claimed.

## 6. Preserved limitation: unbounded last flags need not defeat small detection

Start 0, sole terminal final 6, no Bad states, G={(0,3),(4,5)}:

| State | 0 | 1 |
|---|---|---|
| 0 | undefined | 1 |
| 1 | 2 | 1 |
| 2 | 3 | undefined |
| 3 | undefined | 4 |
| 4 | 5 | 4 |
| 5 | 6 | undefined |
| 6 | undefined | undefined |

The accepted language is exactly

    1^n 00 1^m 00,       n,m>=1.

Every candidate has the one-letter violation (4,5) between its final two zeros.
Thus Necessary(1,0) is empty and the instance is NO.

For n=m, however, the comparison (0,3) has target length n+2 and no later
ALIGNED flag. Its later aligned states are (1,4), then (2,5), then (3,6), none
of which is flagged. It is a genuine last-aligned-flag comparison of arbitrarily
large length, while a DIFFERENT gap already gives the one-letter violation.
In fact its full spectrum is {1} union {3,4,5,...}.

Therefore the proposed implication

    Lambda unbounded => no finite exact necessary bound exists

is false. The new partial decider correctly returns UNKNOWN for this instance,
not NO on the basis of unboundedness; the separate Necessary(1,0) computation
proves NO. The earlier five-state example that defeats EVERY finite necessary
budget and the nonregular positive terminal fixture also have unbounded
spectra. Their different global answers cannot be read from this property.

## 7. Remaining frontier and next discriminating action

For a boundary-safe bad word define

    mu(w) = min { n-j : i<j<n is a forbidden agreement }.

Bounded Lambda implies bounded mu, but the converse is false by Section 6.
The next precise question is whether boundedness of these GLOBAL MINIMA can
be decided while preserving the SAME word across comparisons with different
gaps. A candidate abstraction must distinguish the seven-state family above
from the five-state necessary-budget counterexample, rather than incorrectly
equating their unbounded last-aligned spectra.

Even a complete decision of that bounded-minimum property would not by itself
settle every instance: the known NO example has unbounded mu, so an additional
complete negative method or a general witness-existence invariant is still
needed. Numerical spectra forget which comparisons coexist in a word. Do not
use regularity of these unary length sets as a finite quotient of witness words.

References within the repository:
[prior exact periodic identity](2026-09-06-shared-word-composition.md),
[C037 graph proof](2026-09-05-nonflat-overlap.md),
[C038 terminal exponent](2026-09-05-terminal-period-bound.md),
[September 7 decomposition](2026-09-07-terminal-bad-language-decomposition.md),
[scientific-branch negative-budget proof](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/notes/2026-09-06-delimited-convolution.md).
The scientific branch is not merged or promoted by this contribution.
