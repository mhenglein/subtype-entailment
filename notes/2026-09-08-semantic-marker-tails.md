# Semantic marker tails: exact search with recurrent target states

Date: 2026-09-08. Workstreams: A012/A017; issue #15.
Base main: `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status: written proofs and executed independent-predicate/finite-oracle checks;
independent mathematical review pending; not Lean-checked. Unrestricted Problem
1.7 is not resolved.** No new global claim/experiment IDs are allocated while
sibling branches have overlapping numbering. This record concerns a new exact
relaxation, a decidable semantic subclass, and an explicit limit of that route.
It is not a claim of literature priority.

## 1. The change of parameter

The last-aligned-flag method on main bounds the *length* of a violating terminal
suffix. Target-frontier saturation on PR #10 instead bounds a reference suffix
containing all occurrences of flag-target states, and excludes marker cycles
reachable from those states. Neither condition is necessary for the construction
below. We bound the number of occurrences of the final bit in an actual
last-aligned comparison. Unary runs can be arbitrarily long; target states and
productive marker cycles can occur arbitrarily often before the retained tail.

The finite-prefix/reference machinery is adapted from the exact common-reference
powerset invariant in [the PR #10 source](https://github.com/mhenglein/subtail/blob/6a13dfb3bf90da83deefe3cf5749cbf6949fa052/experiments/target_frontier.py)
and [its proof](https://github.com/mhenglein/subtail/blob/6a13dfb3bf90da83deefe3cf5749cbf6949fa052/notes/2026-09-06-target-frontier.md).
The changes are substantive: prefix sources are allowed in **every** original
state, first-target detection is removed, and the target restriction is a
position in the word, not a restriction on which state labels may recur.

## 2. An exact fixed-marker-tail relaxation

Let I be a terminal binary instance. Handle Bad states, diagonal flags and flags
into the final empty suffix by the existing boundary exclusions. Split each
nonempty accepted word by its terminal state f and last bit b. Because f is
terminal, deleting transitions into f with the wrong last bit preserves exactly
this last-bit slice; it is not an appended delimiter or an encoding.

Write a=1-b. Every remaining word has a unique form

    w = a^n_0 b a^n_1 b ... a^n_(m-1) b,  n_i >= 0.

For H>=0 define Tail_H(I,w): w is boundary-safe and has no forbidden proper
agreement whose target suffix contains at most H occurrences of b. The empty
word is handled separately by the original witness predicate. This is a
relaxation: Witness implies Tail_H, and increasing H strengthens the predicate.

**Theorem 1.** For each supplied finite H, existence of a Tail_H word is decidable.
An exhausted negative answer proves unrestricted nonexistence as well. A positive
answer only proves existence for the relaxation, unless its reconstructed word
passes the original witness check or a separate exactness certificate applies.

### 2.1 A finite schema cover, without bounding the prefix

If H=0, boundary-safe regular reachability suffices. Otherwise put r=min(H,m).
Retain the final r whole blocks as references. Their first boundary is the cut.
For r=H allow an arbitrary prefix of complete blocks. For r<H the prefix MUST
be empty. Allowing a nonempty prefix in the latter case would omit targets still
within the final H blocks and would be unsound.

Enumerate the finite choices of r, cut state, each reference block's start/end
states, and its following b-edge. A data segment uses only a and may have
unbounded length. For r=H the prefix path, not the schema enumerator, checks
whether the cut is reachable. No cycle restriction is imposed. This is a finite
cover for fixed H even when accepted words contain arbitrarily many b's.

### 2.2 Exact comparison formula

Let reference words be u_0,...,u_(r-1), all in a*. At reverse data depth t,
retain the actual original state of each active reference run. For i<j record
H_ij when a flagged pair has occurred at some equal-tail depth. Record E_ij for
equality of the complete reference words. A comparison between reference
blocks i,j is bad precisely when H_ij holds and

    R_ij = AND_{h=1,...,r-1-j} E_(i+h,j+h).

Indeed the first b in a target suffix must match a first b at the same offset
in its earlier occurrence. Thus the initial data tails have equal lengths;
each later whole target block then equals its corresponding source block.
Conversely these matches concatenate to the suffix-prefix agreement. Two
strict cuts inside a single a-run cannot agree: their first b's have different
offsets. Empty data runs and cuts immediately before b are included at depth 0.
The formula also permits overlapping occurrences; no disjointness assumption
is made when corresponding block indices overlap.

A reverse padded convolution chooses the reference words simultaneously.
Equality bits only clear, and hit bits only accumulate. A hit cannot generally
be rejected immediately: its later-block equality guard is evaluated when all
references have finished. This is not a collection of independently chosen
representatives for different comparisons.

### 2.3 Exact observations of every earlier source block

At the same time maintain the SET of all descriptors

    (source_end, current_source_state, equal_mask, hit_mask, finished).

A descriptor represents a possible source data word read backwards in parallel
with the SAME partially chosen reference tuple. Initially include every state
with a defined b-edge, observing depth-zero flags against every reference end.
On a column, branch over all reverse a-edges and the choice to finish; after
finishing emit padding. Update the equality and hit bits against that column
and the reference states. Taking the union is an exact powerset image, not an
independence assumption between references. Different prefix blocks may later
choose different source words, but all use this one reference tuple.

Once every reference is finished, unfinished source words have zero equality
mask, since the reference finishing column emitted padding. Their longer
unmatched prefixes can be completed by ordinary reverse a-reachability. This
produces the exact finite set of source observations

    (start, state_after_b, equality_to_references, hits, source_end).

The invariant holds by induction on reverse columns. Initially it describes
all empty source tails. Each reverse edge/finish option is precisely one legal
extension, and none is omitted. The final reverse closure describes exactly
all remaining lengths, including arbitrarily long unmatched source prefixes.

### 2.4 Connect any prefix while retaining delayed obligations

A finite forward monitor over those source observations remembers the current
DFA state and a pending mask. Bit j means that a previously observed source hit
still requires the forthcoming blocks to equal reference blocks j,...,r-1.
An equality advances that bit; a mismatch kills that obligation. Completing a
pending suffix means a real violation and rejects the path. A fresh hit against
reference j starts the pending check at j+1; a hit against the last reference
rejects immediately. At the cut, decide any remaining obligation by comparing
the retained reference prefix with the indicated reference suffix.

These updates are exactly the formula in 2.2 applied to sources in the prefix.
The monitor starts with no obligations. Induction on prefix blocks shows that
its pending mask represents all and only unfinished possible violations. Checks
that cross the cut are discharged against the same reference equality matrix.
Consequently an accepting monitor path plus a completed reference convolution
is equivalent to a Tail_H word in that schema, in both directions.

Reconstruction chooses one source word realizing each observation. This is
sound because source choices are independent conditional on the fixed common
reference tuple. If a source is longer than all references, its extra prefix
may be shortened to a simple reverse data path; max(reference lengths)+k
letters suffice. The implementation checks the reconstructed word with the
direct Tail_H predicate. The regression also uses an independent reversed form.

### 2.5 Termination and an explicit bound

Put k=|I| and c=r(r-1)/2. There are at most 2 k^2 4^r source descriptors.
A reference/observation state belongs to a set of size at most

    S(k,r) = (k+1)^r * 2^(2c + 2 k^2 4^r).

This accounts for reverse states including FINISHED, all reference equality/hit
bits, and the source-descriptor powerset. There is no first-target bit.
The prefix monitor has at most k 2^(r-1) states, so a shortest successful
prefix has at most k 2^(r-1)-1 blocks. A shortest successful convolution can
be chosen with at most S(k,r)-1 columns; a graph-state repetition can be deleted
because it preserves the ENTIRE reference/observation memory, not just the
original DFA state. Thus, for fixed r, the loose explicit word-length bound

    (r + k 2^(r-1)) * (S(k,r) + k + 1)

suffices whenever that schema has a Tail_H word. Take the maximum over
1<=r<=H, and handle H=0 by a shortest regular path. The bound is for the
relaxation; it is not an unconditional witness bound. The uncapped algorithm
terminates. A cap at any stage returns UNKNOWN.

## 3. Exact boundedness of semantic marker costs

A last-aligned flagged comparison is a proper agreement i<j<|w| with no flagged
aligned pair at a later positive offset. Every boundary-safe bad word has one:
choose a violation with minimum target-suffix length. This is the existing
last-flag argument, which does not say that every last-aligned comparison is a
global minimum.

For a fixed final/last-bit slice J define

    Lambda_b(J) = { number of b's in w[j:] : (w,i,j) is last-aligned }.

**Theorem 2.** The supremum of Lambda_b is effectively computable, or its
unboundedness can be certified by a positive-cost pumping family. This holds
even when the ordinary length spectrum is unbounded.

Use the [main-branch joint-action construction](2026-09-07-realizable-lastflag-spectrum.md).
Every marked comparison has the form

    w=x(uv)^e u,  v != epsilon,  1<=e<=k-1,
    w[j:]=(uv)^(e-1)u.

The joint machine remembers single-state actions and synchronized pairs that
reject a positive-time flag. A finite choice of head state, u-action, v-action
and e is accepted exactly when ONE common u and ONE common v realize the
comparison. The component languages are regular action fibres in the right
Cayley graph. Copies always use the same chosen representatives.

The target marker count is

    e*count_b(u) + (e-1)*count_b(v).

Assign weight one to b-edges and zero to a-edges in that finite Cayley graph.
An action fibre has unbounded cost iff a reachable positive-cost cycle can
reach it. In an SCC this means an internal weight-one edge. Zero-cost cycles
DO NOT imply unbounded marker count. For finite-cost fibres all removable
cycles have cost zero, so a maximum-cost representative can be taken on a
simple path. The code computes infinite-cost descendants and then finite
maxima with attaining words. It constructs a pumping lasso through an actual
positive-cost cycle rather than reusing an arbitrary infinite-length lasso.

For each accepted template, the displayed linear combination either has a
finite attained maximum or an unbounded positively weighted factor. The v
coefficient is zero when e=1; in that case arbitrarily large v costs are
irrelevant. Preserve a nonempty v representative even when its maximal cost
is zero and the identity action also has the empty representative.

The union of those finitely many template spectra is effectively unary regular:
erase a-edge weights to epsilon, replace b by a unary letter, take fixed
multiples and sums and a finite union. The implementation computes boundedness,
maximum, and certificates without materializing a determinized unary automaton.

If the monoid has M elements and the spectrum is finite, then

    H <= (2k-3)(M-1)  for k>=2.

This uses the simple-path bound for finite-cost fibres. As in the prior
construction, M <= N^N for N=k+(k-1)^2+1. This is conditional on finite marker
spectrum, not a universal successful witness budget.

## 4. Exactness on a new certified class

**Theorem 3.** If Lambda_b(J) is bounded by H, then

    Witness_J(w) iff Tail_H(J,w)

for every word in that normalized last-bit slice. Hence Theorems 1 and 2 decide
all slices with finite semantic marker spectra.

The forward implication is immediate. A non-witness has a last-aligned
violation; its target contains at most H markers and so violates Tail_H.
Equivalently every required target lies in the final H blocks, even though
flag-target STATES may have occurred arbitrarily often earlier. No statement
that the earlier prefix is target-state-free is needed.

Combine final/last-bit slices in the usual way: any independently checked
positive word proves YES, while every slice must be settled negatively before
returning NO. Unbounded/capped unresolved slices prevent NO. Neither unbounded
marker spectra nor failure of a proposed witness family is a NO certificate.

### A useful all-input subclass: reset markers

Suppose J has a sole terminal final f, every candidate ends in b, and every
defined b-transition has destination either one fixed state q or f. Then NO
proper suffix agreement can have two b's in its target suffix. At its first b,
neither aligned run can enter f before its required continuation finishes;
therefore both enter q and merge, contradicting terminal nonmerging. Thus H=1
suffices for every flag relation, including arbitrary productive nonflat
components. This is a direct certificate, independent of monoid enumeration.

## 5. A six-state nonflat obstruction and positive companion

Start 0, sole terminal final 5, no Bad states:

| State | 0 | 1 |
|---|---|---|
| 0 | 2 | 1 |
| 1 | 2 | 1 |
| 2 | 2 | 3 |
| 3 | 2 | 4 |
| 4 | 5 | 3 |
| 5 | undefined | undefined |

Let G={(0,2),(0,3),(0,4),(1,2)}. The productive SCC {2,3,4} is nonflat: it
contains the 0-loop at 2, the 1-cycle through 3,4, and the reset edge 3--0-->2.
There is a productive marker cycle reachable from a flag target, so the old
unary target-frontier structural certificate fails. Paired 10/11-versus-00
format is not a workaround: the accepted word 0110 starts with the invalid
token 01. This is a comparison to those precise certificates, not a claim that
no other imaginable solver could decide the instance.

Every candidate has initial run 1^n, n>=0, then a zero, arbitrary intervening
reset blocks, and a final run 1^m0 with positive even m. Every intermediate
completed data run after a reset has length zero or odd. For n<m choose the
initial source and the final-run tail 1^n0: its target state is 3 or 4. For n=m
choose the final-run entry in 2. For n>m choose the initial-run cut n-m, in
state 1, and final-run entry 2. All three choices give an actual flagged
agreement. Thus the instance is NO, independently of the search algorithm.

All 0-edges lead to 2 or the final 5, so the reset-marker lemma gives H=1.
The implemented exact marker spectrum has maximum 1, and the tail algorithm
proves NO by exhausting three schemas. Removing just (1,2) gives the positive
companion; the implementation returns 1110110, checked by both original
witness predicates.

This NO example also defeats EVERY finite length/gap necessary budget. For
odd n>=1 set w_n=1^n0 1^(n+1)0. Its only violating pair is (0,n+2), with flag
(0,3), suffix length n+1 and gap n+2. The initial-state flags require the final
tail to contain exactly n ones; (1,2) would require a longer first run.
Therefore

    Necessary(w_n,L,D) iff n+1>L and n+2>D.

Odd n can be arbitrarily large, so each finite necessary language is nonempty.
This comparison is last-aligned: subsequent source states are 1 while target
states alternate 3,4, never giving (1,2). Consequently its LENGTH spectrum is
unbounded, although its marker spectrum is {1}. The new method decides it
where necessary-budget exhaustion, finite-length-spectrum certification and
the target-frontier structural certificate do not. Its NO verdict is not
inferred from unboundedness. The terminal-to-subtype transfer remains subject
to the existing C030/C031 evidence and semantic hypotheses; no new end-to-end
Lean proof is claimed.

## 6. Why this does not close the unrestricted problem

The tempting stronger assertion that every NO instance is refuted by SOME
finite raw-marker-tail bound is FALSE. Apply the exact uniform code

    C(0)=00, C(1)=10

to the old five-state obstruction from [PR #9](https://github.com/mhenglein/subtail/pull/9).
Keep flags on original-state boundaries; helpers have no flags or Bad labels.
The code is injective and length two, so boundary-aligned suffix comparisons
correspond in both directions. The resulting ten-state terminal instance is
still NO and all its accepted words end in 0.

For its old family w_n=1^n0 1^(n+1)0, the unique violation in C(w_n) has target
suffix C(1^n0), containing n+2 zeros. Thus for every H, a sufficiently large n
gives Tail_H(C(I),C(w_n)) even though the instance has no witness. The marker
spectrum is unbounded and semantic_decision correctly returns UNKNOWN. This
refutes completeness of this PARTICULAR increasing-bound negative method, not
decidability or a method allowed to recognize and invert suitable encodings.

The encoded obstruction suggests using agreement-preserving token structure
rather than raw-symbol cost, but an effective complete choice/iteration of
such structures is still missing. Shared-word synthesis, an unconditional
small-model theorem, or a complete symbolic negative calculus is not supplied
by these results. No undecidability claim follows either.

## 7. Executed evidence and reproduction

    python3 experiments/check_marker_tails.py
    python3 experiments/run_experiments.py

The new run uses seed 2026090821. It checks 746 total two-generator graphs
through three vertices with all four 0/1 cost choices: 2,984 fibre analyses and
15,471 instantiated positive-cost lassos. Independent reachability closure and
bounded simple-path dynamic programming check the weighted graph conclusions.

There are 200 complete acyclic-language oracles with 400 accepted candidates,
800 exact relaxation queries, 200 semantic decisions, and 366 exact marker/
length spectra. In addition, 75 infinite stage-chain languages have complete
finite equality-partition oracles: 360 exact queries and 82,810 tuple-formula
checks, including delayed equality guards. The oracle's completeness comes
from its separately stated equality-partition argument, not from a cutoff.

The 1,034 normalized terminal tables/flag sets through three states exercise
3,102 exact relaxation calls and 7,587 accepted-word predicate comparisons;
the semantic answers are 570 YES and 464 NO. Short words in this part are
positive/soundness diagnostics, NOT independent NO oracles. Analytic fixtures
include the five-state obstruction, both new nonflat companions, the existing
seven-state different-gap example, and the encoded all-marker obstruction.
There are 16 unique-violation checks, 1,024 necessary identities, five exhausted
necessary graphs (all inhabited), six encoded relaxation survivors, and eleven
input/cap guards. See the result file for full records and exact scope.

The unchanged core replay is byte-identical to main's recorded result, Git blob
`aa6d1680b5442493744c667024d2df77a1bd8e78`. Before running it, recovered source
files were checked against original blob hashes `1144ae52379e0417772e79582269cacd91c5bc17`
(border_lab) and `a2ea20afe716774ab34be4b19025f5ad7c6fa037` (run_experiments).

Local work used a partial snapshot because the container could not resolve
GitHub's host; connector reads/writes were available. No full local repository
CI, global link scan or Lean build is claimed. Written all-length proofs are
not established merely by these finite checks, and independent mathematical
review remains necessary before promoting their status.

[Relaxation solver](../experiments/marker_tail.py) ·
[Weighted spectrum and certified decision](../experiments/marker_spectrum.py) ·
[Independent checks](../experiments/check_marker_tails.py) ·
[Recorded result](../results/semantic-marker-tails.json).
