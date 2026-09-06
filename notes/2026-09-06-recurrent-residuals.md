# Recurrent targets: preserve shared word parameters, not isolated suffix summaries

Date: 2026-09-06. Workstream: A017, Agent 2 of the ten-agent campaign.
Main baseline: `bd4fde8f986a843fbc6f7b6f7ca626a5d0f67b0f`.

**Status:** a scoped proof-and-falsification attempt, with written all-length
arguments and reproducible tests. Independent review and Lean verification are
pending. This is not an unrestricted solution, a new complexity classification,
or a claim of literature priority. Earlier research branches are not merged by
this change. No new global claim or experiment ID is allocated in this attempt.

## 1. The specific question

Can recurrent target suffixes be merged using their starting/ending automaton
states, visited states, induced transition transformation, and full agreement
profile? Could exact inclusion of their viable-prefix languages instead provide
a terminating antichain search?

The answer to both proposals, in that literal form, is no. An explicit five-state
instance has infinitely many suffixes with identical summaries but pairwise
disjoint nonempty left-context languages. A twelve-state instance shows that
adding length, symbol counts, endpoint letters, intrinsic budget, and longest
repeated-suffix length still does not repair the summary: two concrete equal-
length words collide on all of those fields and have incompatible left contexts.

This does NOT refute recurrent-target saturation. It says what its symbolic
representation must retain. Nor does it prove that an existence-preserving
finite abstraction is impossible: Section 4 gives a three-word existence basis
for every annotation of the five-state transition table.

## 2. Exact five-state recurrent-target instance

Let the initial state be 0, the only final state be terminal state 4, Bad empty,
and G={(0,3),(1,2)}. Use columns 0,1 in this table:

| State | 0 | 1 |
|---|---|---|
| 0 | undefined | 1 |
| 1 | 2 | 1 |
| 2 | 2 | 3 |
| 3 | 4 | 3 |
| 4 | undefined | undefined |

State 2 is a flag TARGET and has a productive self-loop on the final-word
symbol 0. Thus recurrence is present in the comparison-relevant target region,
not just in an unrelated prefix. Every accepted word has the unique form

    w(m,z,n) = 1^m 0^z 1^n 0,  m,z,n >= 1.

The witness language for the displayed G is exactly

    {1^m 0^z 1^m 0 : m,z >= 1}.                         (1)

A complete agreement-profile formula proves this and will also let us test
arbitrary annotations, rather than just these two chosen flags.

Let D={(q,q):q=0,...,4}, E={(q,4):q=0,...,4}, and B=D union E. Then

    A(w(m,z,n)) = B union {(1,3)}
                 union ({(2,3)} if z>=2, else empty)
                 union O(m,n),                        (2)

where O(m,n) is the singleton

    {(0,3)} if m<n; {(0,2)} if m=n; {(1,2)} if m>n.

### Proof of the profile formula

All five states are visited, giving exactly D and E for diagonal/empty-suffix
comparisons. Every proper nonempty target suffix ending in the last zero must
start either in the last one-run or in an earlier run.

For a target consisting of the final zero alone, an earlier occurrence begins
in state 1 at the first zero of the middle block. This yields (1,3). If z>=2,
an earlier zero also begins in state 2, yielding (2,3). These are all earlier
zero positions.

For a target 1^t0 with t>=1, the corresponding earlier occurrence must finish
at the FIRST zero of the middle zero-run. If t=n, the target starts in state 2.
The source is state 0 exactly when m=n, and state 1 exactly when m>n. If t<n,
the target starts in state 3. A source at state 0 occurs exactly when t=m<n;
sources at state 1 add only the already-present pair (1,3).

Any suffix starting in the middle zero-run and including the last one-run has
form 0^t1^n0. An earlier start in that same zero-run has strictly more initial
zeros and therefore mismatches at the first target one. There are no earlier
zeros elsewhere. A suffix starting in the first one-run and containing the
middle zero-run likewise cannot agree from a strictly earlier start: the
initial one-runs have different lengths. No additional proper pair exists.
This proves (2), including z=1 and n=1. Formula (1) follows immediately.

## 3. The suffix-summary collision and residual antichain

For n>=1 take v_n=1^n0, run from state 2 to state 4. Every v_n has:

    start 2; endpoint 4; visited set {2,3,4};
    full transition action (2,2,4,4,undefined);
    agreement profile {(2,2),(3,3),(4,4),(2,4),(3,4)}.

The transition action is evaluated on ALL five input states, not only the
suffix's selected start. There is only one zero in v_n, so it has no proper
nonempty suffix agreement. These summaries are independent of n.

For any suffix v accepted from q, define its exact left-context language as

    R_q(v) = {x : delta(0,x)=q and x v is a witness}.

All paths from state 0 to state 2 have form 1^m0^z, m,z>=1. By (1),

    R_2(v_n) = {1^n0^z : z>=1}.                        (3)

Hence all these residual languages are nonempty and pairwise disjoint. In
particular neither inclusion direction holds for two different exponents.

The smallest displayed collision is v_1=10 and v_2=110. Prefix x=10 gives
xv_1=1010 (a witness) and xv_2=10110 (not a witness). Prefix 110 reverses which
suffix works. Choosing one representative for their identical finite summaries
can therefore lose a valid word or manufacture an invalid one.

Consequences with exact scope:

* This summary is not a congruence for valid left extension.
* Any finite summary that must preserve every left-context membership test
  would have to distinguish infinitely many v_n, so cannot have finite range.
* Exact language-inclusion subsumption of individual R_2(v_n) has an infinite
  antichain. A proposed well-quasi-order/termination proof based on that literal
  relation fails already on this fixed input.
* These statements do not forbid symbolic descriptions of whole parameterized
  families, global existential pruning, or other sound orderings. Equation (3)
  has a tiny description with ONE shared integer parameter n.

No state-minimality assertion is made.

## 4. Why the antichain does not obstruct deciding existence here

For the SAME transition table, allow ANY G subset of {0,...,4} squared and any
Bad set. All candidates visit every state. Thus any nonempty Bad set or any flag
in B immediately makes the answer NO.

Otherwise (2) shows that z=1 is never worse than z>1: it only removes the
additional agreement (2,3). Each of the three order types m<n, m=n, m>n has the
same profile regardless of the magnitudes. Representatives are respectively

    10110, 1010, 11010.

Therefore, for every annotation of this table,

    a witness exists iff one of these THREE words is a witness.             (4)

Equivalently, after the boundary checks, (1,3) must not be flagged and at least
one of (0,3),(0,2),(1,2) must not be flagged. Other pairs never matter to the
three representatives. This is a complete all-length argument for this TABLE,
not a conjectured five-state-wide bound.

`decide_kernel` implements (4), validating every positive output with the
independent reverse predicate and returning UNKNOWN for any other transition
table/start/final configuration. This is a small exact test oracle, not a new
replacement for the existing flat-graph decision (this table is itself flat).

The important methodological distinction is explicit: infinitely many contexts
must be distinguished for full language recognition, while a finite symbolic
calculation can preserve existence. Confusing those tasks would falsely reject
potentially useful saturation methods.

## 5. Adding lengths and symbol counts still loses word content

The first example can be repaired by remembering an integer. To test whether
that repair is sufficient in general, use the following twelve-state binary
instance, start 0, terminal final 10, Bad empty:

    delta = ((4,3),(4,3),(4,3),(1,2),(5,-1),(11,8),
             (9,8),(9,8),(6,7),(10,-1),(-1,-1),(10,5))
    G = {(0,6),(0,7),(1,5),(1,7),(2,5),(2,6)}.

Let E(0)=10 and E(1)=11. Its exact candidate and witness languages are

    Candidate = {E(u)00 (01)^a E(v)00 : u,v binary words, a>=0},
    Witness   = {E(u)00 (01)^a E(u)00 : u binary words, a>=0}.               (5)

This is an explicit recurrent extension of the earlier whole-word
synchronization mechanism. The cycle 5 --0--> 11 --1--> 5 contains target 5.
We do not claim the equality-enforcing predecessor-tag idea itself is new.

### Proof of (5)

States 0,1,2 are first-stage code boundaries tagged START,0,1. States 5,6,7
are second-stage boundaries with the same tags. A data token is 1 followed by
its bit, read through helper 3 or 8. A first-stage 00 enters state 5. At state
5, token 01 returns to state 5 via helper 11, while 00 accepts the empty final
block. After final data begins, states 6,7 can terminate on 00 via helper 9 but
cannot execute a neutral 01 token. This gives exactly the candidate language.

Flags go only from first-stage boundaries to second-stage boundaries with
DIFFERENT predecessor tags. If u differs from v, take their longest common
suffix t. Immediately preceding its two occurrences, the tags differ (including
START when one word is exhausted). The later suffix E(t)00 matches at that
first-stage boundary, so the flag is violated. This covers empty data words.

Conversely, when u=v, a target boundary after the neutral returns has remaining
suffix E(t)00. A match at a first-stage boundary must reach the first 00 marker
at the same aligned offset, so the remaining data tails have equal length and
content. Equal copies select the same boundary and equal predecessor tags;
there is no flag. A target at state 5 BEFORE a still-unread neutral return begins
with 01. No first-stage boundary has a defined 01 path, so that suffix cannot
match at a flagged source. There are no other flags. This proves the witness
identity without bounding a or the data words.

As a result, for every binary data word u,

    R_5(E(u)00) = E(u)00 (01)*.                         (6)

These nonempty residuals are pairwise disjoint over different u. They require
remembering shared WORD CONTENT, not merely a unary exponent.

### A collision even with extensive numerical information

Take data words u=0100 and v=0010. The suffixes from state 5 are

    s = 1011101000,
    t = 1010111000.

Both have length 10, five zeros, five ones, the same first/last letters, visited
set {5,6,7,8,9,10}, and complete transition action

    (5,5,5,undefined,undefined,10,10,10,
     undefined,undefined,undefined,undefined).

Both have longest repeated-suffix length 2 and intrinsic sufficient budget 2.
Their exact full agreement profiles are also equal:

    {(5,5),(5,10),(6,6),(6,9),(6,10),(7,7),(7,10),
     (8,6),(8,8),(8,9),(8,10),(9,9),(9,10),(10,10)}.

Their state traces are respectively

    5,8,6,8,7,8,6,8,6,9,10
    5,8,6,8,6,8,7,8,6,9,10.

Nevertheless ss and tt are witnesses, whereas st and ts are not, by (5).
Thus recording all the displayed numerical and finite-state information still
cannot make these suffixes interchangeable in left contexts. The exact trace
order/word contents matter. The regression checks every stated field directly.

## 6. Constructive representation target after this test

Represent the second family using ONE shared word variable X, not a collection
of independently existentially quantified copies:

    suffix = E(X)00,
    viable_prefix = E(X)00 (01)^a,  a>=0.

This is a finite relational template for an infinite antichain of concrete
languages. The first family similarly has suffix=1^n0 and prefix=1^n0^z.
The parameters are shared: choosing X separately for each edge reintroduces
the exact false positives in Section 5.

The next general saturation proof needs an effective representation of such
relations, exact transition/composition rules preserving all shared parameters,
and a well-founded reason the family of templates stops growing. Neither the
ordinary transition action nor isolated agreement profiles provide that reason.
No completeness or termination theorem for arbitrary inputs follows here.

The existential decidability of a more expressive string formalism also cannot
be assumed to eliminate the universal internal suffix comparisons. The search
reviewed general results on regular-constrained pattern languages and constraint
automata; their decidable/undecidable fragments are not identified with this
special problem. No external classification is used in any proof above.

## 7. Reproduction and dependency status

Run:

    python3 experiments/check_recurrent_residuals.py
    python3 experiments/run_experiments.py

The new deterministic suite checks 32,767 raw words for the five-state fixture
and 131,071 for the copy fixture; 1,024 numerical count vectors; 30,705 exact
left-context membership tests across the two fixtures; 1,024 distinguishing
prefix pairs; 16,384 effective flag sets with all 32 Bad sets (524,288 cases);
8,192 irrelevant-flag extensions; 900 data/return tuples; the four strong
collision combinations; 22 exact canonical regular-model path checks; and
malformed-input/unsupported-instance guards. Full counts are in the saved JSON.

The 14 effective flag positions are the nine boundary pairs plus the five
possible proper pairs in (2). Exhausting their subsets does not claim to
explicitly enumerate all 2^25 full flag relations: the remaining eleven pairs
are excluded by the written profile formula and additionally tested by all
2^11 additions to four representative annotations. Only 14 of the effective
flag sets are positive; the unbalanced count is expected because any boundary
flag already rejects all candidates.

The original border regression is replayed without changing its implementation.
Dependencies are hashed in the new result. The subtype checks use the existing
terminal realization and exact canonical-model code; they inherit their
recorded written/audited status rather than independently formalizing the
bridge. The five-state and twelve-state realizations have respectively 11/25
variables and 12/30 constraints. No finite-tree semantics are substituted.

These are bounded implementation checks plus separate all-length proofs.
No full repository test suite or Lean build is claimed. The branch-level
scientific records and existing claim numbers are not rewritten or promoted
by this small main-branch attempt. Its canonical chronological record is A017.
