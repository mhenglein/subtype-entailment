# Source-sensitive target-return elimination

Date: 2026-09-13. Research base: `b79bc02d5a669fde60484a463941b16e03805050`.
Workstream A017; C079 / E051.

**WRITTEN PROOF + REPRO. Independent mathematical review pending, not Lean-checked.
This is a complete decision for the explicitly certified class, not unrestricted
Problem 1.7. The positive modular instance and negative marking barrier remain
UNKNOWN for this method. No proximity-to-solution claim is made.**

## 1. Exact model, objective and change from C077

Start with a boundary-normalized, trimmed, finite partial deterministic automaton
I=(Q,delta,s,f,G) over a finite alphabet. Its sole accepting state f is terminal.
There are no Bad states, diagonal flags, final-column flags or flags sourced at
f. These cases are removed by the existing exact final-slice normalization.
For an accepted word w of length n let c(i) be the state at cut i. Witnesshood is

    for every 0<=i<=j<=n:
        (c(i),c(j)) in G  implies  w[i:i+n-j] != w[j:n].

The original task remains binary terminal BorderAvoid and, through the existing
C030/C031 bridge, subtype entailment for arbitrary, possibly infinite trees over
bottom and covariant binary product. No finite-tree replacement is made here.
The bridge retains its prior evidence status and is not re-certified by this work.

C077's last-target theorem requires a unique suffix at the last target, or an
exactly justified completion of incoming flag columns. This work permits legal
repetitions: the final suffix of a target is forbidden only at that target's
actual forbidden SOURCE states. Different target labels retain different,
possibly overlapping suffix patterns in one common candidate word.

The new assumption is that synchronized returns preserve the relevant incoming
flag column. It is a finite, checkable condition, not a presumed theorem for
all automata. The main result is a terminating recursive elimination and the
explicit bound 2*k^(2^r), where k is the original normalized state count and r
its number of target labels. The bound is not claimed sharp.

## 2. Regular restrictions retain original labels

A candidate domain A=(P,eta,a,z,lambda) has a terminal final z and an original
state label lambda(p) in Q for every p in P. All defined transitions project:

    lambda(a)=s, lambda(z)=f,
    lambda(eta(p,b))=delta(lambda(p),b).

A is trimmed. Hence no nonfinal productive state has original label f. Its
language is a regular restriction of the SAME original binary-word language.
When B is called a restriction OF A below, it also has a state map mu to A
preserving start, final, every defined transition and original labels. Mere
language inclusion without this state map is not the inheritance hypothesis.
All constructed filters have such a map: (ell,p) maps to eta(p,Y[:ell]), and
the merged final maps to A's sole final. Trimming restricts this map.
The current flag set retains some whole original target columns. If R is the
set of remaining original target labels, a current comparison is forbidden iff

    lambda(c_A(j)) in R and
    (lambda(c_A(i)),lambda(c_A(j))) in G.

Monitor states with one original label must remain grouped. The termination
measure is |R|, NOT the number of target-state copies in a product automaton.
There is exactly one shared full word and its one deterministic run at every
stage. There is no independent choice of suffix values at separate occurrences.

### Terminal nonmerging

A proper agreement between cuts i<j in an accepted domain word cannot have equal
ORIGINAL labels at any aligned offset. Otherwise determinism in I would reach
its terminal f at the earlier position n-(j-i), before the word ends. This is
the existing C036 mechanism, with its proof made explicit for labeled domains.

## 3. Productive synchronized-return certificate

Form a pair graph with vertices (p,q) such that p!=z and lambda(p)!=lambda(q).
A letter b gives an edge to (eta(p,b),eta(q,b)) only when both transitions exist,
the new left state is not z, and the new original labels differ. Right-final
vertices are terminal endpoints (u,z). Let P_A be the vertices able to reach
such an endpoint, including endpoints themselves.

For an original target label t, roots are precisely the vertices in P_A with

    lambda(q)=t and (lambda(p),t) in G.

Let R_t be every vertex reachable from those roots in the graph induced by P_A.
The column is certified RETURN-CLOSED when

    (p,q) in R_t and lambda(q)=t  implies  (lambda(p),t) in G.       (RC)

This is ordinary finite graph reachability. On the original k-state domain its
pair graph has at most k^2 vertices and at most |alphabet|*k^2 edges. Checking
all target columns is polynomial in the explicit input. The saved certificate
contains the productive set and a root-containing edge-closed set R_t. A
separate checker recomputes productivity and verifies those finite obligations.

The pair graph overapproximates actual comparisons on one word. Therefore a
failed certificate is a synchronized-path obstruction, NOT necessarily an
actual accepted counterexample and never a mathematical NO answer.

### Lemma 1: last visit to each certified target is sufficient

If column t is return-closed in A, an accepted word has no forbidden comparison
into ANY t position iff it has none into its LAST t position. With no t visit
the statement is vacuous.

Proof. The forward implication is immediate. For the reverse, suppose a bad
comparison begins at i and targets a t cut j. Let J>=j be the last t cut.
Set d=J-j. The matched suffix at j includes the segment from j to J, so the two
aligned runs read that same segment from i and j. Their endpoint cuts are i+d
and J, with i+d<J. Every pair on this path is productive: the remaining equal
suffix reaches the final on the right and a strictly earlier, nonfinal cut on
the left. Terminal nonmerging excludes equal original labels. Its root is in
G's t column. By (RC), its endpoint is also in that column. The terminal suffix
at J consequently gives a forbidden comparison from i+d, a contradiction.
The case d=0 is the initial comparison itself. This argument explicitly allows
overlapping occurrences; no disjoint-block assumption is used. QED.

In particular, when every target column is return-closed, all obligations reduce
to a finite list of LAST occurrences, one per original target label. Their
suffixes are still unknown and not independently assignable. Lemmas below
supply the missing simultaneous synthesis step for this class.

### Lemma 2: inheritance under regular restrictions

If column t is return-closed in a domain A, it remains so in every trimmed
deterministic regular restriction B of A with the state projection mu
defined in Section 2.

Proof. Any productive pair path in B projects to a productive nonmerging pair
path in A: its right endpoint is final and its left endpoint is nonfinal under
the original projection. Its original target labels and flags are unchanged.
A return in B is a return to the SAME ORIGINAL LABEL, so (RC) in A applies.
Merging accepting copies to one terminal final preserves this projection.
Deleting other target columns does not affect this column's condition. QED.

The implementation may check (RC) AFTER a fixed-tail restriction, even when it
failed initially. This can certify extra instances. The completeness theorem
needs only initial return closure, which guarantees every later check succeeds.

## 4. Exact source-sensitive fixed-tail filter

Let A have K states. Fix a state q whose original label is t, and a nonempty
word Y of length m accepting from q. Define B to accept exactly those words w
in L(A) for which

* the suffix Y starts at q at cut |w|-m; and
* every occurrence of Y whose starting state's original label is p with
  (p,t) in G is absent.

Occurrences overlapping the terminal copy are included. The final copy itself
starts at t, so the absence of a diagonal flag ensures it is not rejected.
This restriction is weaker than uniqueness and retains every original witness
with this chosen terminal occurrence. It does not enforce other columns yet.

### Lemma 3: at most K*m+1 states suffice

A deterministic filter needs only memory (ell,p), where 0<=ell<m, ell is the
length of the longest suffix of the scanned prefix that is a PROPER prefix of
Y, and p is the A-state at the START of that matching suffix. When ell=0, p is
the current A-state. In general the current state is eta(p,Y[:ell]).

After reading b, consider V=Y[:ell]b. Compute the longest prefix of Y that is a
suffix of V. Its start state is obtained by following from p the portion of V
before that suffix; if the new length is zero it is simply the new current
state. If a complete Y has just occurred, its start state is therefore known
exactly. Reject iff its original label is forbidden into t.

When the current A-state is final, accept iff a complete Y just ended and its
start state is q. Otherwise reject this terminal candidate. For a nonfinal
state, after a complete match retain the longest proper border of Y and its
start state, computed along Y from the complete match's start. This is the
usual prefix-matching recurrence with a deterministically propagated start
state, not separate histories for each smaller matching prefix.

Why no past information was lost: all previously completed forbidden matches
have already rejected. A future match can start only at one of the suffixes
that match a prefix of Y. Every shorter such suffix is inside the longest one,
so its start state is determined by propagation from p. Final acceptance also
uses exactly this state, retaining the designated anchor, not only the letters.

There are K*m possible proper-prefix memories. All successful terminal states
can be merged into one extra accepting terminal. Other terminal states reject.
Thus B has at most K*m+1 states before trimming. Its labels are the original
labels of the current A-states, so it is a domain of the same form. QED.

An independent reference filter stores a literal sliding window of m-1 letters
AND every A-state along that window. The checker exhausts the symmetric-
difference product between this exponential reference construction and the
K*m+1 construction. This checks whole regular languages, not only short words.

## 5. Elimination algorithm and why it terminates

Maintain a trimmed domain A and remaining original target labels R. The invariant
is that every word in L(A) already satisfies eliminated columns, and its remaining
witness obligations are exactly the original flags targeting R.

First, any accepted path avoiding every R-labeled cut is a witness. A shortest
such path is found by finite graph search.

Otherwise every candidate has a last R-labeled cut. For each possible state q at
that cut, consider accepting tails whose positive cuts avoid ALL of R. The
initial occurrence of q is allowed once. This is a finite graph language.

### Infinite-tail branch (existing C077 mechanism)

A productive cycle makes this tail language infinite. Choose a shortest prefix
X to q, so l=|X|<=K-1. There exists a tail Y with

    K*l <= |Y| <= K*l+K-1.

Take a sufficiently long permitted tail through length K*l, then a shortest
permitted continuation. For l=0 a shortest tail suffices. If this Y occurred
earlier in XY, its shift d would satisfy 1<=d<=l and its two copies overlap.
Consequently Y would be a prefix of a d-periodic infinite word.

A terminal K-state automaton accepts no such word of length >=K*d: two of its
(state, position mod d) pairs would repeat, forcing the terminal state to occur
early. Hence |Y|<K*d<=K*l, a contradiction. For l=0 there is no earlier cut.
Y is unique. Every earlier target suffix contains Y at its end, so ALL remaining
flags are safe, even without return closure. Eliminated columns remain safe by
the domain invariant. The resulting whole original word has length at most
K^2+K-2. A finite threshold-counter BFS constructs it.

This is a reuse of C077's positive lemma, not a new primitivity theorem or an
external decision oracle. Absence of such a cycle is not a negative verdict.

### Finite-tail branch (new recursive step)

If every possible last-target tail language is finite, its productive graph is
acyclic. Every such tail Y has length 1<=m<=K-1, and all tails can be enumerated
completely. For every (q,Y):

1. Construct the fixed-tail source-sensitive domain B of Section 4.
2. If B is empty, this branch is NO.
3. Otherwise certify return closure of t=lambda(q) in B.
4. If certification succeeds, remove the WHOLE original column t and recursively
   solve B with R minus {t}. If it fails, the branch remains UNKNOWN.

Every original witness in a finite-tail case belongs to one listed branch,
because its actual last target and tail are listed and it has no forbidden
occurrence of that tail. In a certified branch, Lemma 1 upgrades the fixed-tail
condition to safety at every occurrence of t, establishing the invariant for
the child. Other columns and the full word are unchanged.

Any positive child yields the SAME full original word, not independently spliced
pieces. A negative answer requires ALL tail branches to be empty or recursively
negative. No branch cap or failed return certificate is treated as NO.

When the initial columns are all return-closed, Lemma 2 makes every subsequent
check succeed. Each child removes one original target label. Thus the recursion
has depth at most r=|R_initial|, each branching set is finite, and every local
operation is a terminating finite graph construction. With unbounded resources
this supplies a decision procedure for the stated class. The implementation's
explicit caps, and a host recursion limit if encountered, return UNKNOWN.

### Theorem C079: an explicit computable witness bound

For K>=2 and r>=0 use

    F(K,r)=2*K^(2^r).

At r=0 a shortest accepted path has length <=K-1. An infinite-tail branch has
length <=K^2+K-2<=2*K^2, and r>=1. In a finite-tail child, Lemma 3 gives

    K_child <= K*m+1 <= K*(K-1)+1 <= K^2.

The induction bound for r-1 remaining labels is therefore

    F(K_child,r-1) <= 2*(K^2)^(2^(r-1)) = F(K,r).

No text is appended when a child word is returned; it is already a full domain
word. This proves the bound without an extra accumulated-prefix term. K=1 is
the direct empty-word case. Thus every positive initially return-closed
normalized k-state input has a witness of length at most 2*k^(2^r).

The same bound controls every positive certificate produced by the dynamic
wrapper, though completeness outside the initial class is not established.
No polynomial or unrestricted complexity bound is claimed. The elementary
bound here does not contradict C073/C076: their known growth examples fail the
required return certificate. No universal bound is inferred from finiteness of
the set of k-state automata or from finite testing.

## 6. A recurrent example that genuinely requires legal repetition

Take start 0, final 4, no Bad states, and

    delta=((2,-1),(4,0),(4,3),(1,2),(-1,-1)),
    G={(1,3),(2,1),(3,2)}.

States {0,1,2,3} form a nonflat SCC containing three sources and three targets.
All three columns are return-closed, as the recorded finite pair certificates
check. The earlier C078 wrapper returns UNKNOWN. The new solver returns 0100
with three source-sensitive eliminations; the shortest witness is actually 00,
verified separately. The solver does not promise the shortest witness.

Every accepted word starts and ends in 0, and its last target cut is the state
1 or 2 immediately before its final letter. That last suffix 0 always occurs
at the initial cut, whose state is 0. Thus NO accepted word has a unique suffix
at the last target. Completing all target columns gives an exactly negative
instance, independently decided by the old C077 complete-column solver.

Yet 00 is a witness of the original flags, and so is 0100. For 0100 the run is
0,2,3,1,4. The last target-1 suffix 0 repeats at original states 0 and 3, both
allowed into 1; it does not start at the forbidden source 2. Other target
suffixes in this same word are 00 at state 3 and 100 at state 2.
The selected elimination chain retains and checks those shared suffixes rather
than requiring any of them to be unique. This separates the new method from
the previous implemented target-anchoring wrapper, not from every prior solver.

An eight-state nonflat negative fixture, also UNKNOWN for that wrapper, has a
complete recursive proof with six finite-tail filters and three certified
column eliminations. Its exact transition table and full proof are reproduced
by the checker. The independent checker verifies complete tail coverage, filter
language equality, productive return closure and every negative child. Two
deliberately damaged proof trees are rejected.

## 7. The missing general implication is exposed, not hidden

Dropping (RC) is unsound. In the existing (2,3) modular instance take

    w = 1^4 0 1^6 0 = 111101111110.

It is accepted and passes the source-sensitive tests at the LAST occurrence of
EVERY target state. Nonetheless it has a forbidden comparison at cuts (0,7),
with state pair (0,5) and matching suffix 11110. Reading 111 along the pair takes
(0,5) to (1,5): the target returns to state 5 but its source flag has disappeared.
The later comparison is legal. This is a fully realized counterexample, not
merely an overapproximating pair-path obstruction.

The modular instance remains UNKNOWN for the new wrapper, with its existing
positive witness retained. The six-state marking-barrier NO example likewise
remains UNKNOWN, despite its earlier exact arithmetic negative proof. Failure
of this certificate does not decide either instance.

It is also unsound to split target copies silently. In the labeled domain

    delta=((2,1),(2,0),(4,3),(4,2),(-1,-1)),
    labels=(0,1,2,2,3), start=0, final=4, original G={(0,2)},

the original target group 2 is NOT return-closed. If copies 2 and 3 are wrongly
treated as different target labels, each separate copy has only even-length
returns and both appear closed. Word 10110 passes the last original-group test
but is bad. Removing the entire original group on either copy's individual
certificate would be invalid. The executable regression retains this distinction.

The global remaining task is to treat such return-loss branches exactly, or
produce a complete existence-preserving cover that eliminates them. Neither
that cover nor an undecidability reduction is supplied here. The result closes
the simultaneous source-sensitive synthesis step for RETURN-CLOSED columns,
not the unrestricted subtype problem.

## 8. Evidence, dependency and literature boundaries

Run from the repository root:

    python3 experiments/check_target_return.py --output /tmp/target-return.json --full-output /tmp/target-return-full.json
    cmp results/target-return.json /tmp/target-return.json

The direct and reversed witness predicates, existing boundary normalization and
baseline C077/C078 solver are imported unchanged from target_anchor.py, whose
base blob is f83d7691d21f595986e7332bab25a6ae74d844e1. The new filter is compared
with a separately written literal-window automaton by full finite-language
equivalence. Negative-proof replay separately checks synchronized closure and
DAG tail coverage and verifies every filter by that same independent language
comparison. It does not call the new solver to decide negative proof nodes.

The deterministic suite records 1,024 complete three-state decisions against the
older complete checks, 120 complete acyclic languages, 120 exact filter-language
equivalences, 30,600 literal filter word comparisons, 64,512 three-state word
comparisons and 113,442 last-column word comparisons on certified inputs. Of 248
additional productive random instances, 222 satisfy initial return closure;
all finish at the chosen resource caps. The dynamic outcomes are 232 YES,11 NO,
5 UNKNOWN. Raw bounded scans never supply a NO verdict.

There are 536 negative proof replays; 501 boundary-empty slices are counted
separately so that they are not mistaken for difficult recursive eliminations.
The replay traverses 41 nonempty negative nodes, validates 43 filter languages
and three nontrivial return eliminations. Counts and every fixture are in the
saved output. Explicit tests retain overlapping occurrences, original-label
groups, missing-tail/corrupted-closure rejection, and a resource cap returning
UNKNOWN. These are code/certificate checks, not an independent mathematical
referee or Lean verification.

The external literature search found Havlena--Hecko--Holik--Lengal, *Negated
String Containment is Decidable*, MFCS 2025 / arXiv:2506.22061v1. Theorem 29 and
Section 8 distinguish ONE negated-containment atom with chain-free word equations
from the multiple-atom question. This result is NOT used as a decision oracle
here, and its stated scope does not alone cover arbitrary source-sensitive
recurrences. The proof above is a native finite construction under (RC).
Primary text: https://arxiv.org/html/2506.22061v1#S8

Prior construction entry points:
- C036/C038: notes/2026-09-05-nonflat-overlap.md and the terminal-period note.
- C077/C078: research/TARGET_ANCHOR.md and notes/2026-09-13-target-anchoring.md.
- C073/C075/C076: their existing recovered-source-walk and scheme-cost records.

Independent mathematical review and a full subtype-bridge audit are not claimed.
The new supplementary evidence does not promote any dependency's proof status.
