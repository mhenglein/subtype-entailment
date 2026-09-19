# C081 extension readback

Date: 2026-09-20  
Actor/session: `c081-extension-readback-20260919`  
Base reviewed: `c946d86b9e65da2877e0df42c710abbdcb5a4037`  
Parent extension artifact: commit `31ab3ca6d09dda3401c72c155b4ba31ba0efbd67`  
Status: **review complete; regular transfer remains an ordinary-proof obligation**

This is an independent readback of the post-C081 extension note and its small
boundary experiment. It does not add a Lean theorem, promote a conjecture, or
claim a generic extension result. I inspected the parent note
`notes/2026-09-19-post-c081-extensions.md`, the boundary script and saved result at
the parent commit, and the current definitions in
`CanonicalModel.lean`, `CanonicalReachability.lean`, `StackReachability.lean`,
`StackSummary.lean`, `TreeSemantics.lean`, and `ExpressionNormalization.lean`.

## Regular countermodel construction

The construction in the parent note has the correct orientation after making
the following notation explicit. `StackReachability.Normal` states that

```text
Reaches W (p,u) (q,v)
iff there are x,y,z,m with
  u = x ++ z, v = y ++ z,
  Pop W p x m, and Pop (reverse W) q y m.
```

The stack top is the first list letter. Therefore, for a fixed seed `(p,u)`
and target control `q`, put

```text
L(q,m) = { y | Pop (reverse W) q y m }.
```

The exact fixed-seed language is then

```text
{ v | Reaches W (p,u) (q,v) }
= union over 0 <= i <= |u| and m with Pop W p (u.take i) m
    L(q,m) ++ {u.drop i}.
```

Here `u.take i` is the consumed prefix and `u.drop i` is the untouched
suffix. The target word is `y ++ u.drop i`; writing the fixed suffix on the
right is essential. This follows directly from
`StackReachability.reaches_iff_normal` and does not reverse the two Pop
relations. The parent note should use `take`/`drop` or an equally explicit
prefix/suffix convention wherever it states this factorization.

For each `L(q,m)`, the proposed epsilon-NFA is also correctly oriented. Its
states are the finite controls, its initial state is `q`, and its accepting
state is `m`. Add an epsilon edge for each `Balanced (reverse W) x y` pair and
an `a` edge for each `pop a` transition of `reverse W`. Epsilon moves are
available before the first letter, between letters, and after the last one.
Induction on the `Pop` word gives both directions: the empty word is a
balanced path, and each nonempty Pop derivation is one balanced segment, one
pop edge, and a shorter Pop derivation. The finite balanced table is
effective through the existing `StackSummary.balancedCheck` correctness
theorem. The note should say explicitly that this is an NFA with epsilon
closure, rather than a deterministic letter automaton.

There are only finitely many terms in the fixed-seed union: `i` ranges over
`0..|u|`, and `m` ranges over the finite control set. Attach a fresh path for
each fixed suffix to the corresponding NFA, and take the finite union. The
canonical seed set is finite as well: there is one empty-word forced seed per
forced control and one seed for every prefix of the supplied separating word
at the separating control. This is the finite-list version of
`CanonicalModel.pathSeeds`; it must not be confused with the Prop-valued
definition, which is only an exact specification.

The resulting language `D_q` is the set of addresses derived for variable
`q`. `CanonicalModel.derived_closed` proves its prefix closure once the seed
set is prefix closed and contains forced roots. `CanonicalModel.closure_models`
and `not_entails_iff_canonical` then supply the model and denial safety. These
facts are the semantic bridge that the NFA construction alone does not give.

Determinizing the finite NFA gives a finite residual graph. If its initial
state is rejecting, the corresponding value is bottom. Otherwise an accepting
state is a product node, and each child transition goes to the graph node of
an accepting state or to bottom for a rejecting state. Prefix closure is what
makes this collapse of rejecting residuals sound: a rejected prefix cannot
have an accepted extension. The unfolding has product-address set exactly
`D_q`, so it is a regular tree and satisfies the same normalized constraints.
This last graph-model argument should be written as a separate lemma in the
ordinary paper, including the induction from DFA residuals to addresses.

The reverse regular-to-arbitrary implication is immediate because regular
trees are a subclass of the existing arbitrary-tree values. The forward
implication is the new part and is still not checked in Lean. In particular,
the current Lean files establish the canonical closure and the finite
push/pop reachability normalization, but do not define regular trees or an
NFA-to-tree graph compiler.

## Naming and expression transfer

The normalization transfer is available at the exact semantic level through
`ExpressionNormalization.normalize_entails_iff` and
`normalize_separating_iff`. For a regular original valuation, `Naming.extend`
maps old variables to their values, bottom to bottom, and each product slot to
the finite product expression it names. Regular graphs are closed under
bottom and finite product construction, so this extension remains regular.
For a regular normalized valuation, `Naming.restrict` selects the old
variable nodes and remains regular. Thus the ordinary regular proof needs to
state both directions explicitly; the existing normalization theorems only
prove the semantic equivalence, not this extra regularity invariant.

## Finite-tree boundary

The finite-tree obstruction is correct. The premise
`x * bottom <= x` forces the root and, by repeatedly using the left child,
forces every address `false^j` in `x`. Hence no finite tree satisfies the
premise, and `x <= bottom` is valid over finite-tree valuations by vacuity.
Over arbitrary trees, `TreeSemantics.zeroSpine` is a regular countermodel:
`product zeroSpine bottom <= zeroSpine`, while `zeroSpine` has the root and
all-zero addresses and is not below bottom. The all-depth argument comes from
`CanonicalModel.lower_self_zero_spine`; the depth-four census is supporting
evidence only.

This example should remain in the paper because it separates arbitrary-tree,
regular-tree, and finite-tree semantics. A finite-depth truncation is not a
model-preserving operation for this premise.

## Explicit top

The three proposed substitutions fail for exact, small reasons:

* Mapping top to the full product tree `Omega` does not reflect order:
  `top <= top * top` is false in the labelled source but
  `Omega <= Omega * Omega` is true after erasing the label.
* Mapping top to bottom does not preserve order:
  `(bottom * bottom) <= top` is true but its image is not below bottom.
* Mapping top to a fresh unconstrained variable does not preserve universal
  validity: the target can assign that variable bottom. Adding the equation
  `t = t * t` forces the full product tree and returns to the first failure.

The first old proof dependency that breaks is `CanonicalModel.Forced` and its
use in `Derived`/`closure_models`: a lower premise `y * z <= x` forces the
root to exist, but explicit top can satisfy it with `x = top`, whose root is
not a product node. The push rules fail for the same reason when a child is
present on the left and the upper value is top. This is a failure of the
one-predicate product-address propagation model. It is not evidence that the
explicit-top problem is undecidable or that no least model exists. The next
proof must track at least the root label (bottom, product, or top) and prove a
new canonical separation theorem before reusing word automata.

## Contravariant and other signatures

The contravariant fixture is a valid semantic warning, but its scope must stay
small. Encode an arrow `a -> b` at a pair of child positions only for this
depth-two example and use

```text
(a -> b) <= (c -> d) iff c <= a and b <= d.
```

With `B = bottom -> bottom`, `(B -> bottom) <= (bottom -> bottom)` is true,
while the ordinary product-address set of the left encoding is
`{epsilon, 0}` and that of the right is `{epsilon}`. Address inclusion gives
the opposite answer. Reversing the arrows reverses the disagreement. The
boundary script therefore validates a literal finite obstruction, not a function-tree
semantics or a transfer theorem. A contravariant extension needs signed
paths and a new semantic bridge for every canonical propagation and monitor
step.

For one covariant constructor of fixed arity `r >= 1`, replacing `Bool` by a
finite alphabet is plausible but not a proof. The current development has
binary-specific `upper`, `lower`, left/right propagation, and query-enumerator
interfaces. A generic argument must reprove canonical propagation, first
return and coverage cases, alphabet-dependent enumeration, and the periodic
monitor. The proposed `r+2` edge labels and one-entrance first-return graph
are useful design hypotheses only.

With only bottom and one additional nullary constructor, the value domain is
finite and direct valuation enumeration is a separate decision procedure. For
multiple product-like constructors, address sets lose constructor labels even
when child addresses agree. A labelled tree graph and a new order bridge are
required; finite alphabets alone do not solve that problem.

The standalone automata claims in the parent note retain their stated
hypotheses. In particular, terminal rank decision needs terminal finals, the
infinite continuation result needs strong absorption, and generic push/pop
reachability does not by itself provide a subtype-tree interpretation.

## Boundary replay and disposition

I replayed the exact parent-revision boundary script from `31ab3ca` into a temporary
directory and compared its generated JSON with the saved parent result. The
repository was not modified by the replay.

```text
parent-revision replay: PASS
source_sha256: 7418b52f912f8293a63088c2f40577d6ec04d2d9950cfd5346753e1676dc8982
top-to-Omega counts: 475 both true, 924 both false,
  0 source-true/image-false, 45 source-false/image-true
finite census: 677 trees, 0 models at depth 4
graph check: 26 trees, 676 pairs
```

The experiment supports the exact counterexamples and the bounded claims. It
does not establish top-extension decidability, arbitrary-size encoding
preservation, the regular-countermodel theorem, generic arity, or multiple
constructors.

## Required follow-up

1. Add an ordinary proof lemma spelling out the epsilon-NFA language for
   `Pop (reverse W)` and the fixed-suffix factorization above.
2. Define finite graph regularity and prove that a deterministic prefix-closed
   language yields a bottom/product graph with exactly that address language.
3. State the regularity-preserving naming extension and restriction separately
   from `normalize_entails_iff`.
4. Only after those lemmas are reviewed should the repository claim regular
   countermodel output or regular-tree equivalence.
5. For explicit top, build a small labelled finite-graph falsifier before
   attempting formalization. For contravariance and arity, keep the current
   examples and proposals as open transfer obligations.

No shared ledgers, Lean source, or parent extension files were changed in this
review. The owned path is this new readback note only.
