# Single-source synchronized deletion: junction mismatch and the local-period target

Date: 2026-09-09. Continues `notes/2026-09-09-single-source-primitivity-correction.md`.

**Status: exact counterexample to a tempting shortcut + a proved local pumping lemma. Not a completed single-source bound.**

## 1. Mismatched junction offsets do not force a smaller global root

After synchronized deletion, the unresolved border equality compares a prefix
of the shortened cyclic block with another factor ending at the defect phase.
If the deletion junction occurs at the same relative offset in both compared
factors, reinsertion is expected to lift the equality to the original word.
The difficult case is when the two offsets differ.

A tempting claim is that a long equality with mismatched junction offsets must
force the shortened cyclic block itself to have a smaller period. This is false.
For every `D>=4`, let

    u_D = 0^(D-1) 1.

`u_D` is primitive. Put defect phase `xi=D-1`, comparison length `r=D-2`, and
second-factor start `s=xi-r=1`. Then

    u_D[0:r] = 0^(D-2) = u_D[s:s+r].

A junction at phase `0` occurs in the prefix comparison and not in the second
factor, so the junction offsets mismatch. The equality has length `D-2`, which
is unbounded relative to any fixed automaton-size constant, while the whole
block remains primitive.

The example also survives the short-defect condition. For defect length one,
choose the defect letter `0`: it occurs at phase `r=D-2`, whereas the expected
letter at the actual defect phase `xi=D-1` is `1`. Thus a genuinely
period-breaking short defect can coexist with the arbitrarily long mismatch.

So Fine-Wilf alone cannot close the remaining case.

## 2. What the mismatch does force: a long local period

If two ordinary factors of a word satisfy

    U[a:a+r] = U[b:b+r],     a<b<a+r,

then their union `U[a:b+r]` has period `p=b-a`: for every position where both
sides are defined, equality shifts the letter by `p`. The `u_D` family above
has `p=1`, explaining its long zero zone.

This points to a different use of finite-state control.

**Lemma (aligned local-period loop deletion).** Let an accepted run of a
partial deterministic automaton be `c(0..N)`. Suppose a factor interval
`[A,B)` of the input has period `p>0`. If

    A <= a < b <= B,
    b-a is a positive multiple of p,
    c(a)=c(b),

and deleting `[a,b)` leaves the relevant comparison endpoints outside the
removed interval, then the resulting word is accepted. Moreover the surviving
part of `[A,B)` remains p-periodic across the new junction.

*Proof.* Acceptance is the standard deterministic loop-deletion argument:
identical states at `a,b` splice the run. Since `b-a` is a multiple of the
local period, the suffix beginning at `b` has the same phase modulo `p` as the
prefix ending at `a`; therefore the p-periodic letter pattern agrees across the
splice. QED.

In a p-periodic zone containing more than `n` phase-aligned run positions

    q, q+p, q+2p, ...,

some two have the same automaton state. Hence a sufficiently long local-period
zone always contains an aligned deletable loop.

## 3. Remaining proof obligation after this note

The single-source root-length argument can now be organized as a dichotomy for
a T-border of the synchronized-deletion word:

1. **Matched junction offsets.** Reinsert the deleted root window in both
   compared occurrences and lift the border/state back to the original word.
2. **Mismatched junction offsets.** The overlap supplies a local period `p`.
   If its periodic zone is long enough, use the aligned local-period loop lemma
   to shorten the accepted word while protecting the defect and border ends.
   The unresolved part is to show that this second deletion either preserves
   the offending T-border structure strongly enough for the minimality
   contradiction, or can be iterated until the mismatch zone is bounded.

This is sharper than the previous handoff: primitivity is eliminated, new short
`mt` occurrences can be blocked by bounded endpoint context, and the only
remaining long phenomenon has an explicit local-period pump available.

## 4. Caution

The local-period lemma alone does not prove that deleting one aligned loop
preserves every border needed for the minimality argument. The deletion must be
placed away from the short defect/tail and from the two border endpoints, and
the effect on the compared occurrences must be synchronized. That placement
lemma is the next concrete target; no global decision claim is made here.
