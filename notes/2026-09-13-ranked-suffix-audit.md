# Ranked suffixes: an existence obstruction and an exact decorated repair

Date: 2026-09-13. Base: c4f7e56665828710b3bda77e32bb2904ad4006d6.
Workstream A017, with implications for A012. Scoped attempt; no new C/E IDs.

Status: written ordinary proofs, independent review pending, not Lean-checked.
This is not a solution of unrestricted Problem 1.7. The computational evidence
is recorded separately; no unexecuted suite is claimed in this checkpoint.

## 1. Route and exact closing obligation

The attempted route was to replace unbounded changing-return schemes by finite
order information about suffixes. A sufficient first step would have been:
whenever a binary terminal instance has a witness, some witness has an acyclic
proper agreement relation on its ORIGINAL state labels. This is weaker than
requiring all words to have that property, and makes no length or polynomial
scheme-cost assumption. Section 2 refutes even this existential statement.

A corrected construction can instead assign ranks to individual positions of
one accepted word. Section 3 gives a finite nondeterministic state decoration
with an exact projection theorem. This does not supply a deterministic quotient
or an emptiness algorithm. The missing implication is a terminating procedure
for the decorated model retaining ONE common input word and ONE common run.

The current C076 counter/scheme-cost result remains authoritative. This attempt
does not overwrite it or revive polynomial scheme bounds or Q002/Q003.

## 2. A seven-state instance forces an agreement cycle in EVERY witness

Let the initial state be 0, the sole terminal final be 6, Bad be empty, and

    delta=((1,-1),(2,3),(6,4),(5,-1),(1,-1),(-1,2),(-1,-1)),
    G={(0,1),(0,3),(4,1)}.

For a defined word w of length N with run c, define its proper, nonempty-target
agreement graph by

    P(w)={(c(i),c(j)): 0<=i<j<N and w[j:] is a prefix of w[i:]}.

Diagonal position comparisons and the empty suffix are deliberately excluded
from this graph; they remain included in the actual witness predicate.
The present instance has no diagonal or final-column flags.

Put A=010, C=10110, D=1010. Its candidate and witness languages are exactly

    Candidates = 0(A|C)*(00|D),
    Witnesses  = 0 A (A|C)* D.                         (1)

### Proof of the two language identities

At state 1, the two returning paths are precisely A and C; its two terminal
exits are 00 and D. The initial transition is 0. This proves the candidate
identity, including zero repetitions.

A candidate exiting through 00 is invalid. With no return, it is 000 and
violates (0,1). With at least one return, the final return passes through
state 4 immediately before the final visit to 1. The suffixes there are 000
and 00, so (4,1) is a forbidden agreement.

Now suppose the exit is D. If there is no return, or the first return is C,
the whole word starts 010. The final visit to state 3 has suffix 010, so
(0,3) is violated. Every witness therefore has the second shape in (1).

Conversely, a word of that shape starts 00. A suffix beginning at state 1
starts either 1 or 01, since its exit is never 00. A suffix at state 3 starts
01. Neither is a prefix of the whole word, eliminating the two flags from 0.

For (4,1), a matching target at 1 would have to start with A, since a target
starting with 1 disagrees immediately with the source's initial 0. Write that
target suffix as 010 V, where V is another state-1 suffix ending through D.
The source suffix begins 0 T with T at state 1. Matching requires T to begin
with 1. If T is the final D, this source suffix is only 01010 (five letters),
whereas the target 010 V has at least seven letters; it cannot be a later
suffix of that source. Otherwise T starts with C, so the source begins 01011.
The target begins 0100 if V starts A, and 01010 if V starts C or D. In both
cases a mismatch occurs within five letters. Thus (4,1) cannot fire, proving
sufficiency for every length, not just a tested range.

### Forced two-cycle and shortest witness

Every witness contains (1,2) in P(w): use the state-1 cut immediately after
the initial 0, whose next letter is 0, and the final one-letter suffix 0 at
state 2.

Every witness also contains (2,1) in P(w). The last return finishes at state
1 by the path 2 -1-> 4 -0-> 1, followed by D. The resulting final six letters
are 101010; its last four are 1010. Their start states are respectively 2 and
1, giving the required proper agreement.

Hence every witness has the directed cycle 1 -> 2 -> 1 on its original state
labels. The shortest witness is 00101010, of length eight. No alternative
witness, however long, can repair the acyclic-state-profile hypothesis.

All three flags are essential, not just syntactically present. Removing them
individually admits, respectively, 000, 01010 and 01011000. Each of these words
has an acyclic proper agreement graph. Their runs directly verify that the
removed flag is a genuine forbidden comparison in the original instance.
No minimal-state theorem is claimed for the seven-state construction.

This does not contradict terminal nonmerging. The actual occurrence graph
has increasing cut positions and is acyclic. A cycle arises only when distinct
occurrences of the same state are identified. Neither the guarded-order
calculus on its different arithmetic objects nor any existing conditional
acyclic-pair certificate is refuted.

## 3. Exact occurrence ranks are possible, but are not a deterministic quotient

Consider any k-state binary deterministic terminal instance I and any admissible
word w, even if w is not a witness. Form the graph on its positions with an
edge i -> j when i<j<=N and w[j:] is a prefix of w[i:]. The empty suffix is
included here. Define

    h(i)=1+max{h(j): i -> j}, with max(empty)=0,
    r(i)=k-h(i).

The graph is a DAG because positions increase. Every chain has at most k
vertices. Indeed all its suffixes are prefix-comparable. If two chain starts
had the same original state, the shorter accepted suffix would reach the
terminal final early from the earlier start, contradicting the remaining
nonempty defined run. Thus all states on a chain are distinct.

Consequently 0<=r(i)<k, r(N)=k-1, and every proper agreement has r(i)<r(j).
This is an effective decoration of a SUPPLIED word. It does not bound the
number of positions with a given rank.

### Finite decorated transition system

Use states (q,r) with q in Q and 0<=r<k. Initial states are all (q0,r).
For every defined original transition q -a-> t, include

    (q,r) -a-> (t,s), for every r,s in {0,...,k-1}.

The accepting states are (f,k-1), f in F; Bad is lifted over all ranks.
Lift every original flag over all rank pairs, and additionally forbid

    ((p,r),(q,s)) when p!=q and r>=s.

Interpret the witness predicate on ONE chosen accepting run of this
nondeterministic system, comparing the ORIGINAL binary letters. Projection
of a witnessing decorated run is an original witness, because every original
flag was lifted. Conversely every original witness has a witnessing decorated
run using the ranks above. The extra flags do not reject diagonal cuts: p=q
there, and proper agreeing cuts cannot share an original state by terminality.
Empty-suffix comparisons are preserved by the final rank k-1.

Thus existential decorated-run witness existence is exactly equivalent to
original witness existence, using k^2 states. Proper agreement edges of every
witnessing decorated run strictly increase rank and are acyclic.

The qualifications are essential. This is a NONDETERMINISTIC decoration;
rank choices are not determined by the input prefix. Subset determinization
with existential coloured-run tests has not been justified. Encoding ranks
as extra letters would change which factors compare equal. Moreover, although
the continuation language from (q,r) is the original prefix-free language from
q, choosing a path to a differently ranked cut independently can be inconsistent
with the chosen full run. C067's deterministic wrong-state clause must not be
reused unchanged. The construction moves the unresolved obligation into
consistent occurrence annotations; it does not close it.

## 4. Literature route: the missing regular-word constraints

Michaliszyn, Otop and Wieczorek, CONCUR 2023, `Reachability and Bounded Emptiness
Problems of Constraint Automata with Prefix, Suffix and Infix`,
DOI 10.4230/LIPIcs.CONCUR.2023.3, prove finite reachability in PSPACE for their
specified relational constraint automata. Their word variables are compared
by prefix/suffix/infix/equality and incomparability. The model-theoretic
amalgamation theorem does not include arbitrary regular membership tests or
exact letter-removal equations between consecutive configurations.

Those are not dispensable details in our source-capture setting. An elementary
counterexample shows why simply adjoining finite DFA actions to relational
types cannot justify the same local-to-global proof.

Let R=0+1 0+1 and L=0+1, with + denoting positive repetition. Share a word W
in R between two constraint sets. The left set asks for X in L that is a
strict prefix AND a suffix of W. The right set asks for Y in L that is a
strict prefix of W but is suffix-incomparable with W. The L-prefix is unique.
Writing W=0^n1 0^m1, the left projection is n<=m; the right projection is n>m.
Each set is satisfiable, but their union on one shared W is not.

Both 0010001 and 0001001 have the same length, symbol counts and entire word
transformation on the standard complete DFAs for R and L: their zero action
is idempotent, so every n,m>=1 has the same full-word action. Nevertheless one
extends only to the left condition and the other only to the right. The
projection n<=m is nonregular: prefixes 0^a1 and 0^b1 for a<b are separated
by continuation 0^a1. No fixed finite automaton-action partition of W can
represent that projection exactly.

This is not a refutation of the published theorem, a proof that all enriched
models are undecidable, or an impossibility result for richer shared-word
relations. It identifies an invalid transfer that must not be used as the
missing termination theorem. The precise outstanding step is an effective
synthesis method retaining the regular constraints and one shared annotated
word across every suffix comparison.

## 5. Publication and evidence boundary

The previous local changing-returns variant was replayed in this session: all
nineteen files in its supplied SHA256 manifest stayed identical. Its original
patch targets 4ce1d6b and proposes IDs since assigned to the stronger current
C076/E048 result. It must not be applied over current main. Current C076 adds
a universal last component and proves liveness for every visited source;
its canonical statement is not replaced by the older variant.

The present occurrence-ranking attempt is separate. Its discovery search was
bounded and is not a negative oracle. The proof of (1), not a search cutoff,
establishes that EVERY witness in this fixed instance has a colour cycle.
The general decorated equivalence uses terminal determinism explicitly.
No independent mathematical review, Lean build, unrestricted decision, or
claim of proximity to a final solution is implied by this checkpoint.
