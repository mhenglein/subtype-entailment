# Earliest-source normalization and the Q004 induction boundary

Date: 2026-09-10. Workstream: Q004 / A008 / A017.

**Status: written proof. Independent mathematical review pending; not Lean-checked. This does not decide Q004 or unrestricted Problem 1.7.**

## 1. Setting

Let `I=(Q,Sigma,delta,q0,F,Bad,G)` be a terminal BorderAvoid instance and let

    S = { p : exists t, (p,t) in G }

be its flagged-source states. For a safe accepted word `w`, write
`c(0),...,c(N)` for its run. A witness has no positions `i<=j` with
`(c(i),c(j)) in G` and `w[i:]` beginning with `w[j:]`.

C067 proves a one-visit normalization when **all** flags have one source. The
lemma below is different: arbitrary other sources are allowed, but only the
earliest source state is normalized.

## 2. Earliest-source one-occurrence lemma

**Lemma.** If `I` has a witness, it has a witness `v` with the following
property. If `a` is the first run position of `v` whose state belongs to `S`
and `p=c(a)`, then `p` occurs exactly once in the run of `v`.

If a witness avoids `S`, the statement is vacuous.

**Proof.** Start with any witness `w`. If it avoids `S`, stop. Otherwise let
`a` be its earliest source position and put `p=c(a)`. Let `b>=a` be the last
position of the run carrying state `p`. If `a=b`, take `v=w`.

Assume `a<b` and delete the loop between the two equal states:

    v = w[:a] w[b:].

Because `c(a)=c(b)`, determinism makes this a valid loop splice. The safe run
of `v` is the original run through position `a`, followed by the original run
from position `b` onward. Thus `v` is safe and reaches the same terminal final.

It remains to show that no new forbidden comparison exists. No position
strictly before `a` can source a flag, by the definition of `a`. Every source
position of `v` at or after `a` therefore lies in the unchanged suffix copied
from original position `b` onward; the splice position itself corresponds to
original position `b`. For any two surviving positions `i<=j` with source
position `i>=a`, let `i',j'` be their corresponding original positions. Then

    c_v(i)=c_w(i'),   c_v(j)=c_w(j'),
    v[i:] = w[i':],  v[j:] = w[j':].

Hence a flagged suffix-prefix agreement in `v` would be the identical flagged
agreement in `w`, contradicting witnesshood of `w`. So `v` is a witness.

Finally, there is no occurrence of `p` before `a` because `a` was the earliest
source position, and no occurrence after the splice because `b` was the last
occurrence of `p` in `w`. Therefore `p` occurs exactly once in `v`. QED.

## 3. Why this does not iterate naively

After the first step, the unique earliest source lies **before** every later
source. Compressing a later source can change that earlier source's suffix and
create a new violation. The five-state regression from C067/C068 does exactly
this: deleting a repeated later source changes witness `110010` into
non-witness `10010`, creating a new `(0,1)` comparison at the earlier source.

Thus an induction over source states needs a preservation summary for the
already-normalized prefix sources. The obstacle is not preservation of later
sources; first-to-last deletion of the current source makes all surviving
source positions at the splice or later correspond to an original suffix.
Only earlier protected sources can acquire new obligations.

## 4. Capture structure makes the protected history finite

C067's terminal prefix-free capture theorem is important here. For a fixed
earlier source position and target `t`, there is at most one accepted prefix
from `t` that can participate in a violation. The exact positive formula
`Phi_(p,t)(W)` has three semantic ways to certify safety:

1. no accepted target prefix (`W in A_t`), a regular condition;
2. the unique capture exists but is not a suffix, witnessed by one shared
   suffix variable in the mismatch equation;
3. the capture is a suffix but its aligned cut has the wrong state, witnessed
   by one repeated capture word plus a regular endpoint-state condition.

Consequently, once one satisfying branch and its variables are fixed, the
nonregular part of one protected flag clause contains only **one alignment
translation** between two occurrences of a shared word. A finite collection
of earlier source/target clauses therefore gives finitely many partial
translation constraints on deletion positions.

The corrected overlap-deletion audit already gives the exact local invariant:
a deletion mask preserves a selected equality when membership in the mask is
constant along every aligned-position edge. The least compatible mask is the
union of connected components in this finite alignment graph. Acceptance and
regular branch conditions add finite automaton-state loop signatures; mismatch
letters, source cuts and wrong-state cuts are protected positions.

This observation is not yet a pumping theorem: the alignment closure of a seed
can hit a protected position or produce a maximal deletion interval whose
endpoints are not equal in one of the required automata. But it changes the
induction target from 'remember an unbounded history of earlier words' to:

> given finitely many capture alignments and finite-state constraints, show
> that sufficiently many visits to the next source force a nonempty compatible
> loop-deletion mask, or derive an alternative finite symbolic summary.

## 5. Consequence for Q004

A particularly strong possible closing theorem is **source-simple
normalization**:

> every positive terminal instance has a witness in which every state of `S`
> occurs at most once.

If true, Q004 holds with `R(k)=|S|<=k`, and C068 immediately decides every
terminal instance. The known five-state sequential-deletion regression does
not refute this existential statement; it only refutes one normalization
algorithm.

The complete normalized four-state census is being used as an exact
falsification test. Absence of a four-state counterexample would remain finite
evidence, not a proof.

If source-simple normalization is false, the lemma above still gives a strict
normal form: the earliest source label can always be made unique. Any minimal
counterexample to a visit bound must therefore require recurrence only among
sources **after** at least one protected earlier source, exactly where the
finite capture-alignment system becomes relevant.

## 6. Next proof obligation

For two flagged source states `p,q`, normalize `p` to one earliest occurrence.
Then seek a first-to-last `q` deletion whose closure under every selected
`p`-capture alignment:

- avoids protected source/mismatch/cut positions;
- is a union of state loops in the original run;
- is also a loop in every regular DFA atom selected by the capture branches.

A bound for this finite translation system would decide the two-source class.
An induction that allows the signature to grow with the number of already
protected source states would prove Q004. Conversely, an explicit family where
all compatible masks are forced through protected positions would be the right
shape for an opposing undecidability construction.

Dependencies: C067/C068 in `notes/2026-09-09-source-capture-word-equations.md`
and the mask theorem in `notes/2026-09-09-overlap-deletion-audit.md`.
