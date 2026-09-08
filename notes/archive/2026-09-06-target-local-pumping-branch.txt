# Marker cycles before flag targets: a finite pending-context pump

Date: 2026-09-06. Parent: `df54d87ec4432f489d0b845c7834612f6af70c12` (PR #9).
Approaches A012/A017. Proposed C056; experiment E036.

**Status: written proofs and executed finite checks; independent review
requested; not Lean-checked.** This extends C053 to some inputs with productive
marker cycles. It is not an unrestricted alignment theorem. The accompanying
universal run-normalization result C054 is a separate statement.

## 1. Precise extension of the marker certificate

Work in a final-specific boundary-safe slice of a binary terminal Instance.
As in C053, verify either the paired format (10/11 data, 00 marker, relevant
flags always at token boundaries), or the unary format (1 data, 0 marker).
Every safe accepted word must finish with a marker. No marker is inserted.

Let the productive macro graph have K states. A relevant flag has both ends
in the live slice and a nonfinal source. Let T be its nonfinal target states.
The old certificate rejected EVERY productive marker cycle. The new condition
is weaker:

    No productive marker cycle is reachable from any state in T.

Productive marker cycles may occur earlier, and candidate words may therefore
contain an unbounded number of markers. In particular, there need not be a
finite complete cover of ALL candidate words by bounded-marker schemas.

If T is empty, the boundary-safe candidate language is already the witness
language and ordinary graph reachability suffices. Otherwise let h be the
maximum number of markers on a path from any q in T to the chosen final f.
Then

    1<=h<=K-1.

This h is computable: give marker edges weight one and data edges weight zero.
Restrict to states reachable from T and co-reachable to f. Longest-path
relaxation detects a positive-weight cycle; if none exists, its fixed point
gives h. Zero-weight data cycles do not obstruct finiteness.

In every candidate word, every relevant target position lies in the final h
blocks. Earlier positions have at least h+1 markers remaining and cannot be
an occurrence of a T state. This is an all-path graph consequence, not a
cutoff chosen after inspecting a bounded sample.

## 2. A witness-preserving pump for the preceding blocks

Fix one actual witness. Protect its last h data blocks

    s_0 # s_1 # ... s_(h-1) #.

Everything earlier has no relevant flag target. The following argument keeps
the protected data and its complete state trajectories unchanged. If the word
already has at most h blocks, there is nothing to pump.

For one earlier source block x, together with its actual entry state and run,
define finite signatures:

    E_j(x) := [x=s_j];
    H_j(x) := [some equal data-tail depth t in x and s_j carries a flag
                between the corresponding original source and target states].

The H condition includes t=0, the empty data tail. The exact C052 formula
says that H_j(x) is dangerous precisely when the NEXT h-1-j source blocks
are the complete words s_(j+1),...,s_(h-1), in that order. For j=h-1 it is
immediately dangerous. These guards depend only on a fixed suffix of the
protected reference list, not on the absolute index of the source block.

### Pending-context monitor

Store a set of next-reference indices

    D subseteq {1,...,h-1}.

An index l means that a previously observed flag hit will become a violation
if the upcoming blocks are s_l,...,s_(h-1). Different origins with the same l
have IDENTICAL remaining obligations and can be merged.

When processing a prefix block x:

1. For each l already pending, if E_l(x) is false, discard that obligation.
2. If E_l(x) is true and l<h-1, advance it to l+1.
3. If E_(h-1)(x) is true for pending h-1, a forbidden context completes;
   reject. This never happens along the given witness.
4. If H_(h-1)(x) is true, reject immediately.
5. For each H_j(x) with j<h-1, add j+1 as a new pending index.

Order matters: old obligations consume the current block before new hits
start obligations for the NEXT block. While processing the protected tail,
use steps 1-3 only. Its internal source/target comparisons were already valid
and its strings and run states remain unchanged.

This monitor has 2^(h-1) possible states. Pair it with the original block-entry
macro state, giving at most

    K * 2^(h-1)

combined states.

### Deleting a repeated combined state is sound

If two boundaries in the prefix have the same original macro state AND the
same pending set, delete the complete intervening blocks.

The raw automaton still has a defined accepting run: the equal macro states
make the splice valid, and all retained block trajectories remain unchanged.
No new Bad visit can appear. Its future source-block signatures remain the
same, because both each retained entry state and the protected reference
trajectories are unchanged. The pending-context monitor resumes from exactly
the same state and therefore produces the same valid continuation.

Every potentially new flagged comparison must have its target in the
protected tail. Those with sources in retained prefix blocks are exactly the
H hits and their pending guards, which the monitor checks. Comparisons with
both ends in the protected tail are unchanged. There are no relevant targets
in the remaining earlier prefix. Boundary comparisons were already excluded.
Thus the shortened word is a witness.

Repeat until no prefix combined state repeats. A resulting prefix has at most
K*2^(h-1) blocks (a deliberately loose bound), so every positive certified
instance has a witness with at most

    B = h + K*2^(h-1)

markers. This is an existence-preserving bound, not a claim that all witnesses
or all candidates have that many markers. The pump preserves witnesshood for
G, not necessarily equality of the entire annotation-free agreement profile.

## 3. Exact automatic decision on the enlarged class

Enumerate all marker-edge schemas with at most B markers in the original
macro graph, allowing its productive prefix marker cycles. Between consecutive
markers keep the full regular language of data-only paths. For each schema,
copy original flags to its stage-state copies and use the exact C052
convolution decision.

Soundness: a positive schema supplies an original raw accepting run, and the
original direct and reversed predicates independently validate its witness.
Completeness: if any witness exists, the preceding pump supplies one among
these finitely many schemas. Therefore exhausting them all with negative
answers proves unrestricted NO for this CERTIFIED instance.

Missing formats, unaligned flag endpoints, a marker cycle reachable from T,
or any resource cap remain UNKNOWN. The implementation does not guess that
an uncertified slice is empty. Final-state slices are combined by disjunction;
one positive slice suffices, while NO requires every slice to be settled.

A coarse explicit length bound follows from C052. Each schema has r<=B stages
with at most k original states in each stage, so a positive instance in this
class has a binary witness of length at most

    2B * (B(B-1)+1) * (k+1)^B.

Here K<=k and h<=K-1; the bound is computable from the certified input and may
be very large. No corresponding bound is claimed for arbitrary terminal
instances. No new tight complexity classification is claimed for this class.

## 4. Why original-state repetition alone is still insufficient

Use the following macro transitions; # is the logical marker. Start at 0,
accept only at terminal 6, and use G={(0,3)}.

| State | data 0 | data 1 | # |
|---|---|---|---|
| 0 | 0 | 1 | 0 |
| 1 | 0 | 2 | 0 |
| 2 | 2 | 2 | 3 |
| 3 | 4 | 4 | undefined |
| 4 | 4 | 4 | 5 |
| 5 | 5 | 5 | 6 |
| 6 | undefined | undefined | undefined |

Its binary expansion has 21 states, including the direct expansion's helper
slots. Target 3 has at most two markers remaining, so h=2, K=7, B=16.
The prefix has productive marker cycles, so the older C053 certificate says
UNKNOWN.

The six-block word

    (0, 10, 1, 11, 0, 1)

is a witness. Deleting just the complete second block 10 is an equal-original-
state splice but is NOT valid: it makes a 0 source block immediately followed
by a 1 block. The suffix beginning at target 3 in the penultimate block is
now matched there, creating the forbidden comparison.

The two boundaries have different pending-context sets. The combined-state
pump does not identify them. It instead safely retains

    (11, 0, 1),

whose encoded binary word is `11110010001100`. All three deleted blocks are
certified through repeated combined states. This is a concrete case in which
the pending bit, not only the original DFA state, is essential.

For a negative strict-extension example, the checker independently expands
macro states with transitions

    0: data 0/1 -> 1, # -> 0
    1: # -> 2
    2: data 0/1 -> 3
    3: # -> 4
    4: terminal

and flag (1,3). Every candidate's first nonempty block ends in state 1 and the
last block ends in 3, giving a flagged empty-data-tail comparison. The old
certificate rejects the productive marker self-loop; the new certificate
proves NO by exhausting five schemas. The binary direct expansion has 15
states and flag (3,9). No minimal-state claim is made.

## 5. E036 evidence and limits

Run `python3 experiments/check_target_tail.py`. The standard-library result
is `results/target-tail.json`.

Completed tests:

* 120 acyclic raw instances, with all 214 candidates enumerated independently:
  63 YES, 57 NO, no UNKNOWN.
* All 256 flag subsets of the special cyclic-prefix family above: 32 YES,
  224 NO. Four no-prefix candidates per instance are a complete independent
  oracle because removing the initial empty blocks only removes profile pairs.
  The test additionally checks 3,072 expanded prefix repetitions.
* 140 known witnesses with arbitrary maximal-profile-preserving subsets of
  eligible flags. All 140 undergo strict safe pumping, with two direct word
  predicates checking their outputs. This is a positive-word test, not an
  independent negative oracle.
* 25 of those positive instances also complete the new decision with YES.
* Six exact canonical regular-countermodel path checks, the h=2 pending-bit
  counterexample, the original C051 unary NO fixture, and 2,044 additional
  forward/reversed predicate comparisons.
* Four unsupported/invalid-assumption guards and an intentional prefix cap
  retain UNKNOWN or raise a documented ValueError rather than infer NO.

The pump helper explicitly checks relevant odd-position annotations before
using the paired signature formula, and rejects a supplied h that fails to
protect all visited flag targets. The decider obtains h from its graph
certificate. Positive fixture tests do not establish its negative completeness;
that statement rests on Sections 1-3. No Lean verification or independent
mathematical review is claimed.

## 6. Remaining general obligation

Unbounded marker cycles BEFORE targets are no longer an obstruction for this
method. Productive marker cycles REACHABLE FROM a target still are. Without a
finite target-tail height, the monitor's protected reference list and pending
state count are not bounded by this proof. Neither free marker insertion nor
ordinary state pumping repairs that step. The universal C054 run normalization
controls run COUNTS only after their number is fixed. No general bound on that
number, or alternative unrestricted decision, has been proved here.
