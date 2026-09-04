# Audit of BorderAvoid, Sections 7–8

## Conventions needed for the statements

For a word `pi` of length `n`, write `s_i = pi[i..n]` for the suffix after
position `i`, and let `c(i)` be the state after the prefix of length `i`.
The partial DFA must reject a word as soon as some required `c(i)` is
undefined.  For `rho = reverse(pi)`, set `c'(m) = c(n-m)`.  A border of
`rho[1..m]` of length `b` has period `d = m-b`, and its flag test is

```text
G(c'(m), c'(b)) = G(c(n-m), c(n-b)).
```

This orientation agrees with the original pair `(i,j)`, where
`i = n-m` and `j = n-b`.  Empty and full borders are real constraints:
`b=0` tests the final class against every prefix endpoint, and `b=m`
tests the diagonal `(c'(m),c'(m))`.

Definition 8.1 should say explicitly that only words with a defined run are
eligible.  Likewise, the automaton for `N''`/`S''` must require
`c'(0) in Fin`, backward consistency, and `c'(n)=q0`; otherwise an arbitrary
annotation can satisfy the stated border tests without representing a run
from `q0`.  For example, an empty word annotated with a final state `f != q0`
would pass if the last condition were omitted.

## Claim-by-claim audit

* Proposition 7.1 is correct.  Taking `j=n` makes `s_n` empty, hence a
  prefix of every `s_i`, so every endpoint class must be unflagged against
  the final class, including its own diagonal.
* Lemma 7.2 is correct after making the displayed word explicit as
  `(0^n 1)^m`, with `m` large enough for the requested length.  Every
  period `p <= n` compares the final `1` in a block with a `0`, while
  `n+1` is a period.
* Lemma 7.3 correctly removes agreement pairs with `j <= n` when the
  appended block `x` has no period at most `n`.  Its prose should not be
  read as preserving DFA-definedness, Bad avoidance, or final acceptance;
  aperiodicity only removes those combinatorial agreements.
* Proposition 8.2 and the border orientation are correct, including
  `ell=0`, `d=0`, `b=0`, and `b=m`.
* Theorem 8.7(1) has a finite-state construction.  Store the first `L+1`
  letters/classes, the last `max(L+1,D)` letters and `D+1` classes, the
  period flags for `d <= D`, a counter through `L+D+2`, and the star bit.
  The stated upper bound is a generous product bound.  Definition 8.6 and
  Theorem 8.7 consistently allow `L,D >= 0`, which is required for the
  advertised extreme cases.
* Theorem 8.7(2) is sound once valid backward annotations end at `q0`.
  If a border has `b >= L+1` and `d=m-b >= D+1`, its first `L+1` symbols
  reoccur ending at `d+L+1 > L+1+D`, which violates the star condition.
* Theorem 8.7(3) is immediate: `N''` is a sub-conjunction of all border
  constraints.
* Theorem 8.7(4) is correct for nonempty words.  At `L=lrs(pi)`, the
  prefix `rho[1..L+1]` has no later occurrence.  At `L=0`, if `e` is the
  first occurrence end of the final letter and `D=n-e`, no occurrence in
  `rho` ends beyond `1+D`.  The empty word needs a separate convention
  because it has no last letter.
* Theorem 8.9 is correct under the standard assumption that instances have
  a finite effective encoding and `|I|` is its encoding length.  A decider
  lets us enumerate all yes instances of each size, search until a witness
  appears, and take a finite maximum of their `lrs` values.  This proof is
  not valid if `|I|` means only cardinalities while state/alphabet names
  range over an unbounded non-effective set.

## The truncation theorem

Theorem 8.15 itself survived an independent exhaustive check over all
two-state binary partial DFAs, all `Bad`/`Fin` sets and flag relations, and
all words through length 6.  Its proof has the right core:

1. Equal start classes for the two equal copies of `U_ell`, plus determinism,
   gives `c(e-lambda)=c(n-lambda)` for every `lambda <= ell`.
2. Minimality of `e=e1(ell)` makes `U_ell` occur only at the new end, so a
   repeated suffix of the prefix has length `< ell`.
3. Repeated suffix obligations of smaller length transfer from `pi`; longer
   suffixes occur only once and leave only diagonal checks, already imposed
   by the original witness.  The `lambda=0` checks transfer by Proposition
   7.1.

There is an empty-word exception in Corollary 8.16.  If `epsilon` is a
witness, then `e1(0)=0` and rigidity's condition at `ell=0` asks
`q0 != c(0)=q0`, which is impossible.  A concrete instance is one state
`q0`, `delta(q0,a)=q0`, `Fin={q0}`, `Bad=G=empty`: the empty word and all
`a^n` are witnesses, but no witness is rigid as defined.  Correct options
are to exclude the empty witness in the rigid-witness claim, or declare
`epsilon` rigid by convention and handle its budget separately.

## Refutation of Remark 8.17's equivalence

Rigidity only compares the states at the starts of the first and last
occurrences of each `U_ell`.  It does not imply that the two runs on the
common word never merge later.

Take `A={0,1}`, states `{q0,f}`, start `q0`,
`delta(q0,0)=f`, `delta(f,0)=f`, all `1` transitions undefined,
`Fin={f}`, `Bad=G=empty`.  Every `pi=0^n`, `n>=1`, is a witness.  Its
`lrs` is `n-1`, `e1(ell)=ell`, and for every `0 <= ell <= n-1` the two
start classes are `c(0)=q0` and `c(n-ell)=f`, so each such word is rigid.
For every `ell>=1`, however, the two runs on `U_ell=0^ell` merge after
the first symbol (`q0 -> f` and `f -> f`).  Thus fixed `|K|=2` admits rigid
witnesses with unbounded `lrs`; this disproves any bound applying to *all*
rigid witnesses.  It does not disprove the existential bound needed by
`B(I)`: the same instance has the one-letter witness and `B=0`.

The remark also says `ell < lrs(pi)` while Definition 8.16 uses
`ell <= lrs(pi)`.  Use one quantifier consistently.  The useful true
statement is that the two states are unequal at the designated first/latest
starts.  A merge at an offset gives a shorter repeated suffix, but it need
not be that suffix's first occurrence, so it need not violate rigidity.

## A stronger, useful truncation lemma

The following generalization is sound and gives a practical search rule.

> Let `pi` be a witness, let `v=pi[1..e]` with `0<e<n`, and let
> `h=lrs(v)`.  If `suffix_h(v)=suffix_h(pi)` and
> `c(e-h)=c(n-h)`, then `v` is a witness.

The empty prefix `v=epsilon` can be handled separately by the empty-word
case above (or by setting `lrs(epsilon)=0`).  The empty suffix case `h=0` is allowed.  Equality at the starts and
determinism transfer all states `c(e-lambda)=c(n-lambda)` for
`lambda <= h`.  Every repeated suffix of `v` has length at most `h`, and
its earlier occurrences also occur in `pi`; the original witness therefore
supplies the flag checks.  Suffixes longer than `h` occur only at the new
end and use diagonal checks.  Acceptance and Bad avoidance follow from
the transferred endpoint class `c(e)=c(n)`.

State equality can be weakened further.  It is enough to require
`c(e) in Fin` and, for every `lambda <= h`,

```text
Pred_G(c(e-lambda)) subseteq Pred_G(c(n-lambda)),
Pred_G(y) = {x : G(x,y)}.
```

Then every unflagged earlier occurrence for the original endpoint remains
unflagged for the shortened endpoint.  This profile version found more
cuts in the independent search and avoids treating DFA states that are
indistinguishable to the flag relation as different.

## Independent finite-state check

`experiments/border_lab.py` implements the direct witness predicate and the
reverse border predicate.  Its `Sandwich` search is complete until its
explicit state cap and returns `UNKNOWN` at that cap, never `NO`.  The
reversed class direction is correct: a reverse step uses predecessor `q`
as `c'(m)` and checks `G(q,c'(b))`.  The period bits start true because a
period longer than the current prefix is vacuous, then clear monotonically
on the new character.  Empty/full borders are checked by `initial` and the
diagonal/empty checks in `step`.

An exhaustive two-state/binary check covered all `81` partial transition
tables, all `16` Bad/Fin choices, all `16` flag relations, and all `127`
words of length at most six: `52,928` witness words and `131,436`
truncation candidates, with zero failures.  The separate reproducible run
over 80 random instances passed `121,920` direct-vs-automaton comparisons,
`2,142` original truncation cases, and found `789` equal-state
suffix-trace cuts on rigid words (plus profile cuts).
The useful next experiment is to enumerate every proper prefix `v` of each
bounded witness and apply the generalized suffix-trace/profile cut before
measuring its `lrs`.  Track separately (a) cuts on rigid witnesses, (b) the
minimum resulting `lrs`, and (c) actual `B(I)`.  This distinguishes the false
universal rigidity-bound hope from the existential bound required by
Theorem 8.9.
