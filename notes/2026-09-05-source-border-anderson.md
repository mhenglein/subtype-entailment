# Forward-closed source borders and a 6n+1 impossibility certificate

Date: 2026-09-05. Continues A017 after `af6cde5`.

**Status: WRITTEN PROOF + REPRO. Not Lean-checked.** This is a new restricted
certificate, not a decision for unrestricted Problem 1.7. The combinatorial
argument adapts Anderson, Loftus, Rampersad, Santean, and Shallit, *Detecting
palindromes, patterns and borders in regular languages*, Theorem 58
(Information and Computation 207 (2009), 1096-1118; arXiv:0711.3183). No
priority claim is made for the underlying unbordered-word theorem.

## 1. Source-border terminology

Fix a deterministic finite automaton with terminal accepting states. Fix a
source state `p` and a set `T` of nonfinal states. A nonempty proper border
`b=w[j:]` of an accepted word `w` is a **T-border** when the run state at the
suffix start `j` lies in `T`. A word is T-unbordered when it has no T-border.

For a BorderAvoid instance, take

    T_p = { q : G(p,q) }.

If a witness suffix starts in `p`, it must be T_p-unbordered. Empty-suffix and
diagonal flags are boundary cases handled separately.

For existence questions we may delete every positive transition back into
`p`: if a witness suffix starting in `p` returns to `p`, the suffix from its
last occurrence of `p` is a shorter witness suffix from the same state. Thus
existence from `p` implies existence from `p` with no positive return.

## 2. Forward-closed target theorem (C039)

Let `M` be a deterministic finite automaton with `n` live states, terminal
acceptance, and no positive return to its start `p`. Let `T` be a set of
nonfinal states that is forward closed **before terminal acceptance**:

    q in T, delta(q,a)=r live and r nonfinal  ==>  r in T.

**Theorem.** If `M` accepts a T-unbordered word, then it accepts one of length
at most `6n+1`.

Equivalently, if every accepted word through length `6n+1` has a T-border,
then every accepted word has a T-border.

### Proof adaptation

Use the proof of Anderson et al., Theorem 58 with `N=0`, replacing the word
"bordered" by "T-bordered". Suppose `w` is a shortest accepted T-unbordered
word with `|w|>6n+1`. Their proof writes

    w = PsiL XL theta XR PsiR,

with `|XL|=|XR|=n` and `|PsiL|=|PsiR|>3n`. In the deterministic setting the
shorter accepted words used in Claim 59 can be obtained by deleting a loop
inside `XL` or `XR`; the equal endpoint state makes the complete later run
identical after the deletion.

Call the two shortened accepted words `zeta` and `eta`. By minimality of `w`,
each has a T-border. The ordinary proof first shows that the selected borders
must extend beyond `PsiL`; a shorter border lies wholly in unchanged outer
material and would already be a border of `w`. In the present setting its
suffix-start state is also unchanged, so it would already be a T-border of
`w`, contradiction.

The remainder of Claims 60-61 is word combinatorics only. The two long borders
force conjugate words at the left and right ends, and hence produce a nonempty
border `alpha` of the original `w` whose suffix occurrence begins inside
`PsiR`.

It remains only to recover the target-state colour. In either shortened word,
the suffix start of its chosen T-border occurs no later than the eventual
suffix occurrence of `alpha`. The run segment from that T-state to the start
of `alpha` contains only nonfinal states: a terminal final could not be crossed
and then continued. By forward closure, the state at the suffix start of
`alpha` is therefore also in `T`. The right outer run is unchanged by the
loop deletion, so this is the same state in `w`. Thus `alpha` is a T-border of
`w`, contradiction.

The constant `6n+1` is inherited from Theorem 58. This proof uses determinism
to preserve run colours after loop deletion; no NFA-coloured generalization is
claimed here.

## 3. BorderAvoid source impossibility (C040)

For one state `p` in a terminal BorderAvoid instance:

1. reject `p` immediately if it is Bad or diagonally flagged;
2. discard finals `f` with `G(p,f)`, because the empty suffix makes every
   `p`-to-`f` path invalid;
3. delete positive returns to `p`;
4. trim to states reachable from `p` and co-reachable to an unflagged final;
5. let `T_p` be the remaining targets of flags sourced at `p`.

If `T_p` is forward closed among live nonfinal states, C039 gives a finite
exact test for whether there exists any suffix from `p` satisfying **p's own
flags**. Exhaustively enumerate live candidate runs through `6n+1`; a resource
cap returns UNKNOWN. If none is T_p-unbordered, then no global witness can ever
visit `p`, regardless of flags sourced at other states.

Therefore a proved-impossible state may be added to Bad. Repeating this
pruning is sound. If the original start becomes impossible, the whole instance
is NO. If pruning makes the C037 last-flag pair graph acyclic, the existing
finite Necessary automaton then decides the remainder exactly. The composition
never interprets a resource cap or a failed forward-closure test as NO.

When the only relevant flag source is the start state, and its target set is
forward closed, the bounded test itself is an exact decision for the instance:
a T-unbordered accepted word is precisely a witness after the boundary
normalization.

## 4. Why forward closure is real

Forward closure cannot simply be omitted. In the four-state instance

    0: 1 -> 1
    1: 0 -> 1, 1 -> 2
    2: 0 -> 2, 1 -> 3
    3: terminal
    G={(0,1)},

the target set `{1}` has an internal edge `1 -> 2` leaving the set. The word
`1011` is a witness. Replacing `{1}` by `{1,2}` makes the source target set
forward closed and the corresponding cyclic instance has no witness.

This is exactly the place where the proof uses closure: a long T-border in a
shortened word is replaced, through the Anderson conjugacy argument, by a
shorter/later border of the original word. Its suffix-start state is reachable
from the original T-state, not necessarily equal to it.

## 5. Reproduction (E027)

Run

    PYTHONPATH=experiments python3 experiments/check_terminal_anderson.py

The saved deterministic check records:

- all 288 cases left UNKNOWN by C037 in the normalized four-state terminal
  census; 272 are positive and 16 negative under the independent C034 oracle;
- C040 proves the start impossible in **all 16** negative cases and in none of
  the 272 positive cases;
- the composed pruning + C037 decider therefore turns all 16 formerly cyclic
  negative cases into exact NO, leaving the 272 positive cases UNKNOWN rather
  than guessing;
- 700 seeded random terminal instances, with 315,840 direct short-word
  soundness checks; zero false impossibility certificates;
- iterative pruning removes the start in 427 of those random instances, while
  the first-pass source certificate does so in 405, demonstrating that sound
  state removal can expose additional impossible states.

The bounded search enumerates only defined safe runs and has an explicit node
cap. The theorem, not the finite random sample, justifies the all-length NO
certificate when enumeration through `6n+1` completes. No Lean build or full
repository suite is claimed in this continuation.

## 6. Remaining gap

C039-C040 control cyclic overlap when the flagged target colour is stable under
moving the border start toward the terminal end. The unresolved cases are
precisely those where a border chain can move between flagged and unflagged
regions. Terminality still bounds each nested border chain by the number of
states (C036), suggesting a next route: stratify target states by how many
flag/nonflag boundary crossings a forward path can make, and induct on that
rank. Rank zero is C039. A successful finite-rank induction would generalize
the 6n+1 argument beyond forward-closed target sets.
