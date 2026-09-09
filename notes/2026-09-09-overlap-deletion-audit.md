# Overlap deletion: counterexample, minimal mask closure, and corrected pumping

Date: 2026-09-09. Workstream A017. Reviewed pumping note at
`917ced2d49c3c7173368d99bf134bf7cc1212f42`; recovery integration at
`653ab77879ce88007adc16e3fbb56715bbaa0f33`.

**Status: written counterexample and corrected sufficient lemmas, with executed
independent-algorithm checks. Independent mathematical review pending; not
Lean-checked. No unrestricted or single-source decision theorem is claimed.**

## 1. The precise error

The [paired-overlap note](2026-09-09-paired-overlap-pumping.md) correctly observes
that deleting two disjoint state loops preserves acceptance. Its additional
assertion that aligned deletions preserve two OVERLAPPING equal occurrences
is false. Physical disjointness of the deleted intervals is not disjointness
of the compared occurrences. One deletion can affect both occurrences at
DIFFERENT relative offsets. The second deletion then need not compensate.

The counterexample below satisfies even the stronger interpretation that both
deleted intervals lie strictly inside BOTH occurrences. It also satisfies the
large-shift inequality and the stated interior-window margins. Thus the
large-shift equality-preservation conclusion does not follow as written.

This audit does not refute the separately stated single-source shape theorem
or the existence of a different successful pump. The examples need not be
shortest witnesses. They refute the all-accepted-word pumping lemma actually
used to justify the proposed local step.

## 2. Six-state all-length counterexample

Use start 0, terminal final 5, no Bad states, and this binary partial table:

| State | 0 | 1 |
|---|---:|---:|
| 0 | 1 | undefined |
| 1 | 1 | 2 |
| 2 | 2 | 3 |
| 3 | 3 | 4 |
| 4 | 4 | 5 |
| 5 | undefined | undefined |

The start has no incoming transition. Fix m>=3, put y=0^m1 and p=m+1, and
let w=y^4. Its occurrences at a=0 and b=p, both of length r=3p, are equal.
Delete the two one-letter intervals

    I=[p+1,p+2), J=[2p+1,2p+2).

They are disjoint, are strictly inside both [0,3p) and [p,4p), and are state
loops at states 2 and 3 respectively. The shortened accepted word is

    y (0^(m-1)1) (0^(m-1)1) y.

The surviving first occurrence is

    0^m1 0^(m-1)1 0^(m-1)1,

while the surviving second occurrence is

    0^(m-1)1 0^(m-1)1 0^m1.

They have the same length but differ at offset m-1. Acceptance survives;
the required equality does not.

### The proposed large-shift window does not repair the error

Take m=80. There are n=6 states and p=81>n^2=36. Use the 37 consecutive
relative offsets t=82,...,118. Their paired run states are all (2,3), and
the window is more than 36 letters from either end of both occurrences.
For ANY t<t' in this window, deleting [t,t') and [p+t,p+t') removes the same
positive number delta< p of zeros from the second and third blocks only.
The surviving first occurrence starts with 80 zeros; the second starts with
80-delta zeros. Every one of the 666 collision choices therefore fails the
claimed equality preservation, while still preserving acceptance.

This is not merely a bad choice among otherwise certified pair collisions.
The entire supplied interior window has the defect.

## 3. Corrected alignment-compatible mask theorem

Let w be a word and let E be a finite list of true factor equalities

    w[a:a+r] = w[b:b+r], with a<b.

A deletion mask D is a subset of letter positions. Write

    phi_D(t) = t - |D intersect [0,t)|,
    v = w with every position in D removed.

Require for every (a,b,r) in E and every 0<=t<r:

    a+t in D iff b+t in D.                             (M)

**Theorem.** Under (M), the images of each selected pair of occurrences are
still equal:

    v[phi_D(a):phi_D(a+r)] = v[phi_D(b):phi_D(b+r)].

*Proof.* Both images retain exactly the same relative offsets t, and the
original letters at each corresponding offset are equal. Reading those offsets
in order proves the equality and equal image lengths. This works for arbitrarily
many mutually overlapping occurrences. QED.

Condition (M) is sufficient, not necessary for accidental equality of one
particular word's images. For example, identical unary letters can hide some
mask differences. No converse about arbitrary string equality is asserted.

### The least compatible closure is effective

Build an undirected graph on letter positions, joining a+t to b+t for every
selected equality and offset. For any seed S, the union of graph components
meeting S is the unique least mask containing S that satisfies (M).

*Proof.* Every (M)-compatible mask is constant on every edge and hence every
connected component. It must contain each component meeting S. Conversely the
union of those components satisfies (M). QED.

The implementation uses union-find; the independent checker uses graph
reachability and, on short domains, enumeration of ALL possible masks. The
closure is minimal for these explicit alignment constraints, not a globally
minimal witness-preserving deletion.

## 4. Acceptance and coloured cuts must also be checked

Decompose D into its maximal disjoint intervals [l,h). If the original run
satisfies c(l)=c(h) for each interval, deleting all intervals preserves the
accepted run by processing the loop splices from left to right.

If a selected cut lies outside the strict interior of every deleted interval,
its state is also preserved at its image phi_D(cut). The executable certificate
protects the starts and ends of all selected factor occurrences, plus any
additional supplied cuts. It also requires distinct occurrence starts to
remain distinct. Protected letters may not be deleted.

Together these checks give a sound certificate for acceptance, selected
factor equalities, and their endpoint-state colours. A failed loop or protected-
position check returns NOT_CERTIFIED, never NO. A closure computation may
force deletion of a protected defect or introduce intervals that are not state
loops; it is not permission to perform such a deletion anyway.

For the counterexample, closing the two seeds forces FOUR deletions, at
positions 1,p+1,2p+1,3p+1. All four are valid zero loops. The new word is
(0^(m-1)1)^4; both selected occurrences become (0^(m-1)1)^3. This repairs the
local surgery rather than just withdrawing the failed claim.

## 5. Correct all-copy periodic pumping, with its exact limit

Suppose an accepted terminal word has the periodic tail

    w=x y^e u, p=|y|>0, u a proper prefix of y.

Terminality implies e<=k-1: two equal states at distinct complete-copy starts
would reach the terminal final early on the later state's remaining suffix.

Choose phase endpoints 0<alpha<beta<p on the SAME side of |u|: either
beta<=|u| or alpha>=|u|. Delete [alpha,beta) from every complete y copy and
also from the partial u copy exactly when beta<=|u|. These intervals are
disjoint. If their endpoint states agree in EVERY affected copy, the word
remains accepted and has form

    x y'^e u',

where u' is still a prefix of y'. The periodic equality is preserved, with
its gap changed from p to p-(beta-alpha). This is the all-copy special case
of (M), not the unsound two-interval substitution.

If an admissible phase region contains more than k^C phase positions, where
C is the number of affected copies, two positions have the same complete
C-tuple of run states. They give the required simultaneous loop splices,
provided all resulting intervals avoid the specified protected material.
C<=k, but existence of a sufficiently large admissible region remains a
separate placement obligation when additional equalities or protected defects
are present.

**Crucially, preserving selected equalities does NOT prove witnesshood of the
shorter word.** New unwanted borders, changed primitive roots, and newly
flagged comparisons must still be excluded. This audit does not turn a
finite-word certificate or the conditional tuple pigeonhole into a global
witness bound. It restores an exact local invariant for testing that next step.

## 6. Executed checks

```sh
python3 experiments/check_overlap_deletion.py
```

Seed 2026090901; [saved result](../results/overlap-deletion-audit.json).
The run checks 78 counterexample family members (m=3..80), including 45 with
p>6^2, and all 666 paired-loop choices in the m=80 large-shift window. Every
family member has a successful four-interval repair.

For the corrected closure, 364 short-domain queries are checked against all
possible masks; 5,616 binary surviving-factor checks validate the equality
claim, and 500 multiple-alignment cases compare union-find with a separate
reachability implementation. Six guards cover invalid inputs, protected
letters, nonloop closures, and the absence of strict shortening.

These finite checks validate the implementation. The quantified counterexample
and sufficient statements rest on the arguments above. No full local repository
CI, new Lean proof, or human referee is claimed.

[Implementation](../experiments/overlap_deletion.py) and
[checker](../experiments/check_overlap_deletion.py) are repository-contained.
