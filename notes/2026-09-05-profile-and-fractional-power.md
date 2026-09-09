# Agreement-profile normalization and bounded fractional-power violations

Date: 2026-09-05. Base: `2ef127134535408a31ab2399328412c5ef8f26f2`.

**Status: WRITTEN EXACT REFORMULATIONS + FALSIFICATION EVIDENCE. Not Lean-checked.**
Unrestricted Problem 1.7 remains open.

**Status correction (2026-09-09).** The universal profile-normalization
conjecture discussed below is REFUTED; see [Q002](../research/conjectures/Q002.md)
and the [modular counterexample](2026-09-05-modular-synchronization.md).
C044 records an equivalence, not a proof of either refuted universal claim;
C043 and that equivalence retain their recorded evidence levels. The original
argument and bounded-search discussion below are preserved as history. This
correction is not a new independent review of their proofs.

## C043: every proper terminal violation has a bounded fractional-power form

Fix a k-state partial deterministic automaton with terminal accepting states.
Let `w` be a defined accepted word of length `n`, with run `c(0),...,c(n)`.
Suppose a proper suffix violation occurs at positions `i<j<n`:

    (c(i),c(j)) in G
    w[j:] is a prefix of w[i:].

Put

    d = j-i,
    N = n-i,
    x = w[i:j].

The agreement says exactly that the source suffix `w[i:]` has period `d`.
Write

    N = s d + r,       0 <= r < d.

Then

    w[i:] = x^s prefix_r(x).

Writing `u=prefix_r(x)` and `v=x[r:]`, so `x=uv` and `v` is nonempty, gives

    w = A (uv)^s u,    A=w[:i].

By C038,

    1 <= s <= k-1.

The state constraints are

    run(A) ends in p=c(i),
    run(Auv) ends in q=c(j),
    (p,q) in G,
    run(A(uv)^s u) ends in a terminal final.

Conversely, any boundary-safe accepted word with such a factorization and
state constraints has the stated violation: its suffix beginning after the
first `uv` is `(uv)^(s-1)u`, a prefix of `(uv)^s u`.

Therefore, after the standard Bad/diagonal/final-column boundary exclusions,
the entire non-witness language is the finite union, over `(p,q) in G` and
`s=1,...,k-1`, of these state-typed bounded fractional-power patterns.

This is stronger than merely saying a violating suffix is periodic: the number
of complete copies is uniformly bounded by k-1. The words `u` and `v`, and in
particular the gap `uv`, remain unbounded. Thus this does not itself give a
finite automaton, context-free grammar, or decision procedure for the
complement. General forall-exists word-equation validity cannot be invoked as a
decidable black box.

A deterministic scratch check on 1,200 random terminal automata compared every
proper violation found in all accepted binary words through length 8 with the
factorization above. It checked 1,638 boundary-normalized accepted words, 187
with violations, with no disagreement. The quantified statement rests on the
proof, not the sample.

## C044: the terminal budget conjecture is equivalent to flag-free agreement-profile domination

For a boundary-safe accepted word `w`, define its **agreement profile**

    A(w) = { (c(i),c(j)) : 0<=i<=j<=|w| and
                           w[j:] is a prefix of w[i:] }.

This definition includes diagonal and empty-suffix agreements. For any flag
relation `G`, the word is a witness exactly when

    G intersect A(w) = empty.

Fix k>=2. Consider these two statements.

**TB(k).** Every positive k-state terminal-final BorderAvoid instance has a
witness with sufficient budget at most `k-2`.

**PD(k).** For every k-state terminal DFA and every boundary-safe accepted word
`w`, there is a boundary-safe accepted word `v` such that

    A(v) subseteq A(w)

and `word_budget(v) <= k-2`.

Then

    TB(k) iff PD(k).

### PD(k) => TB(k)

Take any witness `w` for flags `G`. Since `G` is disjoint from `A(w)`, a word
`v` with `A(v) subseteq A(w)` is also disjoint from `G`, hence is also a
witness. Its budget is at most `k-2`.

### TB(k) => PD(k)

Given an accepted word `w`, form the **maximal preserving flag relation**

    G_w = (Q x Q) \ A(w).

Then `w` is a witness for `G_w`. By TB(k), there is a witness `v` for this
maximal instance with budget at most `k-2`. Since `v` avoids every pair outside
`A(w)`, necessarily

    A(v) subseteq A(w).

Thus the sharp terminal budget problem can be studied with **no input flag
relation at all**. The problem becomes a normalization theorem for accepted
words of a terminal DFA under the finite preorder induced by agreement-profile
containment.

C034 proves TB(k), and therefore PD(k), for `k<=4`. For larger k this remains
open.

## Why maximal preserving flags are a stronger adversarial test

Given a target accepted word `w`, `G_w` contains every flag that can possibly
be added while preserving `w`. Any other flag relation for which `w` remains a
witness is a subset of `G_w`. Therefore searching for a low-budget witness
against `G_w` is a stronger falsification test than choosing random flags.

In the local adversarial search, transition tables were generated first, then
high-intrinsic-budget accepted target words were selected, and `G_w` was built
exactly. The repository's finite Strong Sandwich automata then exhausted every
split with `L+D<=k-2`.

Observed completed runs:

- k=5, 1,200 transition tables: 1,134 high-budget targets tested in one profile
  run; every target had a profile-dominated witness with budget <=3; zero caps.
  A separate adversarial run tested 1,741 high-budget targets from 1,200 tables,
  with target budgets up to 11, and found no counterexample.
- k=6, 300 transition tables: 403 high-budget targets; every target normalized
  to budget <=4; zero caps. A separate 900-table adversarial run tested 1,568
  targets, with target budgets up to 12, and found no counterexample.
- Additional completed runs include k=5 (492/492), k=6 (425/425), and k=7
  (163/163) profile-normalization successes, again with no cap or counterexample.

These are falsification data only. They do not prove PD(k).

One representative k=5 normalization is

    target = 0100100
    replacement = 010100

under the transition table

    0: 0->1
    1: 0->2, 1->1
    2: 0->3, 1->2
    3: 0->4, 1->2
    4: terminal.

The target's intrinsic budget exceeds `k-2`; the replacement has budget one
and its full agreement profile is contained in the target's. No simple-path
replacement has that containment property, so a proof cannot merely erase all
loops.

## Interaction with the C037 cyclic residual

For maximal preserving flags, the unflagged state pairs are precisely pairs in
`A(w)`. This adds a realizability condition absent from arbitrary flag
instances. In sampled k=5 and k=6 high-budget targets, every maximal-profile
instance whose C037 last-flag pair graph was cyclic still had a Strong witness
within `k-2` (117/117 and 46/46 respectively, zero caps).

The stronger claim that such a cyclic case always has a profile-dominating
**simple** accepting path is false. The `0100100 -> 010100` example above is a
counterexample: the only simple accepting path is `0000`, whose agreement
profile is not contained in the target profile.

This leaves a more plausible target: exploit the fact that every unflagged pair
in a maximal-profile residual is realized somewhere in one common accepted
word, rather than treating the residual pair graph as an arbitrary graph.

## Next proof target

Assume PD(k) is false and choose a shortest accepted word `w` with no
profile-dominated accepted replacement of budget <=k-2. By C041, high budget
forces the nested terminal-suffix staircase

    g_m >= k-m,    1<=m<=k-1,

where `g_m` is the gap from the earliest occurrence of the terminal length-m
suffix to its terminal occurrence. Each such occurrence contributes an allowed
pair to `A(w)`, while terminal nonmerging constrains the corresponding aligned
state paths.

The desired contradiction should use this **simultaneous family** of nested
agreements. Individual loop deletion is known to be unsound. A successful
normalization must either preserve `A(v) subseteq A(w)` directly or show that
one of the nested agreements makes a different low-budget accepting path
profile-safe.
