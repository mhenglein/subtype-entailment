# Target-frontier saturation beyond bounded marker counts

Date: 2026-09-06. Base: PR #9, commit
`df54d87ec4432f489d0b845c7834612f6af70c12`.
Approaches A012/A017. Proposed claims C054-C056; experiment E035.

**Status: written proofs and reproduced finite checks; independent review
requested; not Lean-checked.** This is a strict extension of the marker
certificate C053, not a solution of unrestricted Problem 1.7. It permits
unbounded marker cycles before the first relevant flag target. No claim is
made that arbitrary target-containing cycles can be normalized this way.
No literature-priority claim is made.

## 1. Exact scope and notation

Begin with one boundary-normalized terminal accepting slice of a binary
BorderAvoid instance, as in C053. Remove Bad states, diagonal-flagged states,
and all sources of flags into the selected final f. Retain states reachable
from the initial state and able to reach f. Empty slices and an initially
accepting terminal are handled directly.

Check one of C053's two token formats without altering any candidate word:

* paired: data tokens 10 and 11, marker 00, all candidates ending in a marker;
  no relevant flag endpoint may occur at an odd token position;
* unary: data 1 and marker 0, again ending in a marker.

The paired check uses the same five-state format parser and the same
conservative odd-position rejection. The unary format has no helper positions.
Macro transitions retain exactly the original paths, including the safety of
intermediate raw states. A proper flagged raw suffix agreement is equivalent
to its logical token agreement: both flagged endpoints are token boundaries,
and at those boundaries marker and data tokens are distinguishable.

Let Q be the productive macro states, K=|Q|, delta their partial transition
function on data letters and a marker #, and G the remaining ordered flags.
Only productive flags matter. Flags sourced at f cannot occur in a strict
ordered pair; final-column and diagonal flags were already handled. Define

    T = {q in Q : some p in Q satisfies (p,q) in G}.

T consists of the **second endpoints** of flags, not their source states.
Every accepted path avoiding T is a witness, so a simple finite graph search
settles this case first.

All subsequent statements concern candidates with at least one T occurrence.
Split a candidate immediately before the first data block that contains T:

    u_1 # ... u_h # v_0 # ... v_(r-1) #.

The u blocks form the early prefix. Every logical state in their data runs,
including the state immediately before each marker, is outside T. Their last
marker may lead to a cut state in T; that state belongs to the first v block.
The v blocks are the reference suffix. They include every flag-target position
of this candidate. Individual block lengths are not assumed bounded.

## 2. Fixed-reference pending-mask normalization (C054)

For this section fix the actual reference words v_j AND their complete state
runs. They may be arbitrarily long. No hypothesis on marker cycles is needed
for the local statement.

For an earlier data block u, with its actual state run, define two subsets of
{0,...,r-1}:

    E(u) = {j : u=v_j},
    H(u) = {j : some equal data-tail depth t has a flag from the state
                    before suffix_t(u) to the state before suffix_t(v_j)}.

Both t=0 and t equal to the length of a block are included when defined.
H is an occurrence statement, not a statement about whole-block equality.
Even unequal blocks can have an equal-tail flag hit.

### The exact pending monitor

Suppose a hit against reference block j is observed in an early block.
The target suffix includes the tail, its first marker, and then precisely

    v_(j+1) # ... v_(r-1) #.

The hit is a violation exactly when the blocks that subsequently follow its
source match that finite list. For j=r-1 the list is empty, so the hit is an
immediate violation. Otherwise it starts a pending check whose next required
block is v_(j+1).

Maintain a subset P of {1,...,r-1}. An index t means that a pending check is
waiting for v_t and would then require v_(t+1),...,v_(r-1). All pending checks
with the same t are equivalent for every future continuation and can be merged.

On reading the next early block u:

1. For each t in P, drop the check if t is not in E(u). If t is in E(u),
   advance it to t+1, or reject if t=r-1 and the pattern completes.
2. Reject if r-1 is in H(u). For every j<r-1 in H(u), add j+1 to the new P.

When the early prefix ends, feed the fixed reference blocks to these pending
checks, without spawning new early-source checks. Equivalently, reject a
pending index t precisely if

    v_a = v_(t+a) for every a=0,...,r-t-1.

Reference-to-reference constraints are checked independently by the C052
cross-stage formula. There are no flag targets in the early prefix, so these
two categories exhaust all proper flagged comparisons. Within a single data
block, distinct positions have their first marker at different offsets and
cannot give the required suffix agreement.

This monitor preserves ALL flag obligations; it does not rely on sampling
short tails or overlooking comparisons that cross multiple early markers.

### Deleting repeated boundary memory

The monitor at a block boundary has memory

    (current macro state, P).

There are at most K*2^(r-1) memories. If two boundaries of the early prefix
have the same memory, delete the complete intervening blocks and their markers.
The macro states agree, so the remaining run splices correctly and retains
acceptance and boundary safety. Each retained block has the same letters and
state run as before and hence the same E/H observations relative to the fixed
reference suffix. The pending monitor starts the remaining continuation in
exactly the same P. Reference-internal comparisons are unchanged. Therefore
witnesshood for the given G is preserved.

Repeated deletion terminates. A resulting early prefix has distinct boundary
memories, so

    h <= K*2^(r-1)-1.

**C054.** Every witness with the given reference suffix and target-free early
prefix has another witness with that SAME reference suffix and at most this
many early blocks. Block lengths are not bounded by this argument.

This is a G-specific normalization, NOT full agreement-profile domination.
New unflagged agreement pairs may appear after a deletion. Neither Q002's
k-2 budget conclusion nor Q003's unconditional strict descent follows. Their
modular counterexamples remain valid.

## 3. Choosing the unknown reference words consistently (C055)

C054 fixes words that have not yet been chosen by the existence solver. Merely
choosing a possible E/H edge independently for each block could use a different
reference tuple for each edge and would be unsound. The following powerset
construction keeps ALL observations tied to one common reference tuple.

Fix a reference **schema** of r stages: each has a chosen macro start,
data accepting endpoint, and marker successor. Data paths inside a stage can
have arbitrary recurrent components. The first stage is required to visit T.

### Reference convolution

Read all r reference words backwards in padded synchronous convolution.
Keep their current reverse states (or FINISHED), pairwise equal-prefix bits,
and persistent pairwise flag-hit bits exactly as in C052. A stage can finish
only at its chosen start. Its marker endpoint and successor are fixed by the
schema. A Boolean records whether the first reference run visits T.

At completion the equality bits describe full reference-word equalities.
Reject any reference-to-reference hit whose later-block equality guard holds.
This is the C052 exact test, including empty tails and delayed guards.

### Powerset of all possible earlier blocks

Alongside the reference memory maintain a set of descriptors

    (b, q, E, H, done).

Here b is the data endpoint of a possible early block, so delta(b,#) determines
its following boundary. q is its current reverse data state, retained as its
start state after finishing; E and H are its current reference equality and
hit subsets; done says it has emitted its first padding symbol.

All active earlier-block states are in Q\T. The marker successor of b must
also be outside T, except that the final early marker may enter the chosen
reference cut. The actual prefix graph will enforce that it stops there.

Initialize all possible endpoints b, with E all true and empty-tail hits
observed against the reference endpoints. For each chosen reference column,
extend EVERY possible unfinished earlier block backwards by each available
data predecessor, or let it finish at its current state. A finished block
emits padding forever. Update equality bits by the current symbols and add
any newly observed equal-tail hits. Merge identical resulting descriptors.

The invariant is literal: after any reference-column sequence, the set is
exactly the collection of possible earlier-block reverse histories at that
depth, summarized by the displayed descriptor. Histories with the same
descriptor have identical future effects; this justifies taking a powerset.
The earlier word choices are not fixed yet, but the reference-column sequence
is the SAME for every descriptor in the set.

### Longer earlier blocks require no new word comparison

Let M=max_j |v_j| after all references have finished. If an earlier descriptor
is still active, each reference has emitted padding, so its E is now empty.
No future deeper tail can match any reference tail, since every reference
word has ended. Its H can never grow again.

Consequently the unmatched left part of that earlier block is accounted for
by ordinary reverse reachability through Q\T. Compute that finite closure and
record every obtainable start state. Finished descriptors already retain
their exact start state and final E/H values. This gives all and only the
possible early-block edges

    (start, marker successor, E, H, data endpoint)

for THIS reference tuple. It includes blocks longer than all reference words,
not just bounded source samples.

Now search the finite (macro state,P) graph from Section 2, using those edges,
to connect the original initial state to the chosen reference cut. Its final
pending checks are evaluated from the common reference equality bits. Every
selected edge can be realized independently by an earlier block relative to
these same references: all cross-block effects are already represented by
E/H and P, and there are no targets in any earlier block. This proves both
soundness and completeness of the combined search for this schema.

Successful words are reconstructed by a finite replay against the selected
reference tuple. The implementation then checks the raw binary result using
both `witness` and the independent reversed `border_witness` predicate.

### Explicit finite and length bounds

There are at most

    D = 2*K^2*4^r

earlier-block descriptors: K possibilities for each of b,q, 2^r for each of
E,H, and two done values. Their powerset has at most 2^D states. With
b_r=binom(r,2), the combined machine has at most

    N(K,r) = 2*(K+1)^r * 2^(2*b_r + 2*K^2*4^r)

states. The factor two includes the first-stage target-visit Boolean.
These are generous finite upper bounds, not claims about typical search size.
An uncapped search therefore terminates, even though the reference lengths
and the number of earlier marker loops were not supplied with cutoffs.

A shortest successful combined path has fewer than N(K,r) transitions, so
M<=N(K,r) is a safe bound. For a possible earlier block longer than M, retain
its last M+1 letters. A shortest unmatched left extension between its prescribed
start and the retained suffix's start has at most K-1 letters. It stays outside
T and changes no E/H observation. Thus every selected early edge has a
representative of data length at most M+K. The reconstruction checks this bound.

Together with C054, one positive witness has binary length at most

    2*[(K*2^(r-1)-1)*(N(K,r)+K+1) + r*(N(K,r)+1)].

This is a construction-specific computable bound. It is not a bound for
unrestricted terminal BorderAvoid. Unary raw words need no binary doubling,
so the displayed expression also bounds them conservatively.

The practical implementation has explicit state, transition, descriptor,
schema, and reconstruction caps. A cap gives UNKNOWN, not NO. Passing None
for each cap gives the uncapped finite procedure. Large theoretical bounds
are formulas in this note; the program does not allocate integers or graphs
of those sizes merely to assert finiteness.

## 4. A broader raw-input certificate (C056)

Once the format has been verified, let Cone(T) be the macro states reachable
from T. Require:

    No productive marker edge on a directed cycle has its source in Cone(T).

This permits arbitrarily many productive marker cycles elsewhere. It strictly
weakens C053, which forbade productive marker cycles everywhere.

If a candidate has no T occurrence, the earlier simple target-free path search
already finds a witness. Otherwise retain the data block containing its first
T occurrence and all following blocks as its reference suffix. From that first
T onward, every marker advances strictly through the condensation graph.
There are at most K-1 such markers, so

    1 <= r <= K-1.

The cut is either the original start or a marker successor reachable through
a target-free prefix. Enumerate these finitely many cuts and reference marker
sequences. The first reference data stage must visit T; all subsequent marker
edges lie in Cone(T), where marker cycles were excluded. Data-only cycles
are retained, not unrolled. This is exactly the reference-schema enumeration
in `target_frontier.py`.

Apply C055 to each reference schema. Every genuine witness either is target-free
or has one of these schemas and an early prefix handled by its observation
powerset. Conversely every successful schema search reconstructs an original
raw witness. Thus all schemas empty gives an exact NO for this certified slice.
Take the union over terminal-final slices. A positive slice yields YES even if
another slice is unresolved. NO requires every slice to be certified and empty;
format failures or resource caps leave UNKNOWN.

This cover is existence-preserving; it is NOT a claim that every candidate has
a bounded number of markers. Indeed the explicit fixtures have arbitrarily
many markers before reaching T. The prefix normalization bounds the markers
needed by some witness without modifying the retained reference suffix.

For K>=2, C054 also gives the coarse existential total-block bound

    K*2^(K-2) + K-2.

The length formula of Section 3, maximized over 1<=r<=K-1, supplies a computable
bound for this certified class. A deliberately looser single expression is

    N_K = 2*(K+1)^K * 2^(K*(K-1) + 2*K^2*4^K),
    length <= 2*K*(2^K+1)*(N_K+K+1).

These double-exponential-scale bounds are permitted by, and do not evade,
C046/C050's lower bounds. No unrestricted complexity classification follows.

## 5. Strict extension and a normalization example

The following macro table has seven states, with start 0, final 6, and columns
for data 0, data 1, and marker #:

| State | data 0 | data 1 | # |
|---|---|---|---|
| 0 | undefined | 0 | 1 |
| 1 | 2 | 1 | 0 |
| 2 | undefined | 3 | 4 |
| 3 | undefined | 3 | 4 |
| 4 | undefined | 5 | undefined |
| 5 | undefined | 5 | 6 |
| 6 | undefined | undefined | undefined |

With G={(2,4),(2,5),(3,4)}, the final two blocks impose the same three
incompatible inequalities as C051. The instance is NO. Removing (2,4) gives
a YES instance, with logical witness

    # 01 # 1 #,

whose raw binary form is `001011001100`. It uses two early blocks (epsilon,01)
and one reference block (1).

The macro marker cycle 0 -> 1 -> 0 is productive, so C053 returns UNKNOWN for
both inputs. Its vertices are not reachable from targets 4,5. The new front
end certifies both. The observed combined searches use nine states for the
negative fixture and six for the positive fixture, each with one reference
schema. These small counts are fixtures, not an asymptotic bound.

The independent binary expansion allocates 21 raw states; 18 are live in these
slices. **Seven is the macro-state count, not the binary-instance count.**
The subtype checks use the actual raw instances through C030, without changing
the arbitrary-tree semantics or upgrading that bridge's proof status.

A separate five-macro-state example, with two retained reference blocks 0 and
01, demonstrates the pending-mask deletion rather than just final-block hits.
An eleven-block early prefix

    1, epsilon, 111, 11, 111, epsilon, epsilon, 111, 1, 111, 1

normalizes to the single early block 1, while the reference tuple (0,01) stays
unchanged. The saved result includes its macro flags and both complete tuples.
Both binary word predicates validate the shortened word.

## 6. E035 executed checks and evidence levels

Run from the repository root:

    python3 experiments/check_target_frontier.py

The deterministic seed is 2026090654. The saved result is
`results/target-frontier.json`.

* 160 acyclic raw inputs with all 290 accepted candidates independently
  enumerated: 65 YES, 95 NO.
* 160 arbitrary bounded schemas checked against the prior exact C052 solver:
  63 YES, 97 NO. These use a distinct algorithm but inherit that solver's
  written/audited status; they are not independent proof-assistant checks.
* All 256 flag relations from four earlier macro sources into the last block
  of the seven-state macro fixture: 88 YES, 168 NO. An independent all-length
  two-schema argument reduces each fixture to two C052 calls (512 calls total).
  With targets only in the last block, removing complete two-block early
  cycles removes sources and cannot change later-block guards. No new powerset
  solver is used to justify that oracle's prefix bound.
* 140 exact source-observation sets (120 two-reference, 20 three-reference)
  compared with an independently enumerated oracle for fixed references. The
  oracle includes sources beyond the longest reference via a proved M+K length
  bound, not an arbitrary cutoff.
* 700 logical/raw forward/reversed comparisons: 600 two-reference cases and
  100 three-reference cases. The latter exercise two distinct pending-pattern
  positions. Two additional three-reference existential solver fixtures return
  independently checked YES words.
* 207 witness normalizations remove 936 early blocks in total. These are finite
  checks of the local statement, not its all-length proof.
* Eight exact canonical regular-model path checks for the positive/negative
  binary fixtures, using C030's realization and the existing canonical bridge.
* Four unsupported-input guards retain UNKNOWN; five deliberately small caps
  retain UNKNOWN; the two main fixtures also pass with every cap set to None.

There were no algorithm/oracle mismatches in the completed run. An initial
unsupported-odd-flag test expected UNKNOWN from a fixture that in fact admitted
a valid unary fallback. That TEST EXPECTATION was replaced by a mandatory
odd-target fixture for which both format certificates genuinely fail. No
semantic counterexample or theorem was inferred from the failed expectation.

The original core border regression and both prior E033/E034 suites were
rerun and reproduce their saved outputs byte-for-byte. Their result Git blobs
are respectively aa6d1680b5442493744c667024d2df77a1bd8e78,
b320319d36baade23b0cc138294a56bc5e5e442b, and
bd354e2beb510eee234f7c0358bb1680f0ec5c94. The new checker records dependency
hashes. Full repository CI/link validation and Lean were not run; the working
snapshot is partial. No independent mathematical review has occurred.

## 7. Failed routes and the exact remaining question

This attempt also considered using the terminal bound on the depth of nested
border chains as a complete finite-memory argument for reversed words. No such
argument was established: bounded chain depth alone does not identify which
unbounded word contents must be remembered. The existing nonregular-language
examples already preclude silently treating this as an ordinary finite witness
recognizer.

The present powerset works because every earlier block can be summarized
relative to a finite SAME tuple of target-containing reference words. It does
not show how to cap that tuple when a productive marker cycle is reachable
from a flag target. Reusing a raw state label for different suffix words would
lose information and is not justified by determinism alone.

Nor can missing delimiters be inserted freely: C053's flagged `00` example
changes its answer after delimiter insertion. All markers here belong to the
original candidate words, and all significant paired-code positions must be
aligned. Inputs outside these format/cycle conditions remain unresolved by
this theorem, not negatively decided.

The next target is a finite representation of recurrent flag TARGETS, or a
different agreement-preserving decomposition for inputs with no suitable
marker format. C054 removes unbounded target-free prefix multiplicity; C055
removes the need to supply concrete reference words; C056 combines them into
a checkable raw-input class. None of those steps is a proof that every terminal
instance belongs to that class. An unrestricted completeness argument remains
unproved rather than hidden in the algorithm's stopping rule.
