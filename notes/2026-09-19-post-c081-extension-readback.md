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

## Follow-up readback of R1-R4

Parent checkpoint `cfb46f5` expands the requested ordinary arguments into
Lemmas R1-R4. I reread those lemmas against the checked definitions listed
above. Under the stated C081 hypotheses, the three proof areas are now
**discharged as ordinary mathematics**:

1. **Reachability languages (R1-R2): discharged.** R1 gives both directions
   of the word-length induction for the epsilon-NFA. Epsilon paths compose by
   reflexivity and transitivity of `Balanced`, and each first consuming edge
   is exactly one `Pop` step. R2 then applies the exact `Normal` factorization
   with `take i` and `drop i`; the finite seed list is precisely the forced
   empty seeds plus every prefix of the separating word. Fixed-suffix paths,
   finite unions, and the effective `Pop` tests complete the regular-language
   construction.
2. **Graph unfolding (R3): discharged.** The subset DFA construction handles
   epsilon closure and accepts exactly the NFA language by induction on the
   address. Prefix closure makes every prefix of an accepted address
   accepting, so a rejecting successor can soundly be represented by the
   bottom node. The address induction in R3 proves both directions between
   DFA acceptance and product-node walks, including the empty language case.
   The finite graph therefore unfolds to exactly `D_q`.
3. **Naming transfer (R4): discharged.** Finite graph representations are
   closed under bottom and binary product by disjoint union plus a fresh
   product root. Structural induction covers every finite expression used by
   `Naming.extend`; `Naming.restrict` is projection to finitely many existing
   roots. Together with the checked normalization equivalence, this gives
   regularity in both directions.

The remaining bridge is a short identification rather than a new idea:
the finite seed-list predicate must be identified with `CanonicalModel.pathSeeds`,
then `CanonicalReachability.derived_iff_reaches` identifies `D_q` with the
canonical `Derived` language. R2 states the first identification and the
existing declarations establish the second. I found no mathematical gap in
R1-R4 under those declarations.

This verdict is separate from implementation status. The R1-R4 argument is
not replayed by a new Lean module, and the repository still lacks an
executable NFA/determinization/countermodel extractor. Neither omission
prevents accepting the ordinary proof in the paper; they prevent claiming a
new kernel-checked theorem or a usable extractor. The older follow-up list
above is therefore discharged at the ordinary-proof level, while formalization
and tooling remain explicitly open.

Follow-up scope completed: only this note was changed; the path is released
after the follow-up handoff.

## Follow-up readback: constant-free ambient-domain example

Parent checkpoint `66eed7d` adds the formula

```text
premises: x = x × x, x <= y
query:    y <= x.
```

The all-word top-free argument is correct. Equality supplies both directions,
and the direction `x × x <= x` first forces the empty address of `x`. If `u`
is an address of `x`, then both `0u` and `1u` are addresses of `x × x`, hence
of `x`. Induction on word length gives every binary address in `x`, so
`x = Omega`. Since `x <= y` and `Omega` is the greatest top-free tree,
`y = Omega` and the query holds. This is an unbounded semantic proof; it does
not come from the finite experiment.

The explicit-top countermodel is also exact. Let `x = Omega` and `y = top`.
Both are regular; `x = x × x` and `x <= y` hold, while `y <= x` fails at the
root because top is a leaf and `Omega` is a product. The formula contains no
constants and can be represented in the checked C081 syntax by two inequalities
for the equality plus `x <= y`. It therefore fits the restricted
product-equality/variable-inequality grammar recorded for NP99. The example
refutes identity translation between the top-free and explicit-top
arbitrary/regular domains, but it does not establish hardness transfer or rule
out another reduction.

The finite-domain statement is separately sound. In either signature,
`x = x × x` has no finite solution: bottom and top fail the root-label
comparison, while a finite product solution would contain the root and both
children of every product address, producing infinitely many distinct binary
addresses. Thus both finite-domain entailments are vacuously true. This
all-depth argument is independent of the bounded finite census.

I replayed the updated boundary checker from `66eed7d` in a temporary
directory and compared its output with the saved result. The replay passed with
source hash
`55e9584c306fe2e4dbc3ce144be165ac83cf630b7b179b2935515360a0d456c1`.
The labelled finite-graph fixture held both premises and rejected the query;
the independent finite cross-check covered 1,444 source pairs. Those counts
validate the finite fixture and predicate implementation only. They do not
replace the all-word top-free induction or prove a general ambient-domain
reduction.

Disposition: the constant-free ordinary proof and its finite labelled
countermodel are **accepted with the scope above**. The top-free induction,
explicit-top regular witness, finite unsatisfiability argument, and bounded
checker evidence are distinct claims. No Lean formalization or executable
extractor was added or required for this review. The owned note path is
released after this handoff.

## Follow-up: a fresh-`omega` reduction for the constant-free fragment

A related proposal gives a sharper upper-bound comparison. Restrict the C081
input so that neither premises nor query contain bottom. Name every variable
and every product subexpression. For each named product `p = l × r`, add the
NP99-style product equation `p = l × r`; translate each source inequality to
an inequality between its names. Add a fresh variable `omega` with

```text
omega = omega × omega
```

and add `z <= omega` for every occurring variable or product name `z`. The
result uses only product equations and variable inequalities, so it has the
restricted NP99 syntax. Naming can share duplicate subexpressions or use one
slot per occurrence; either choice is polynomial in the input size.

The key ambient-domain lemma needs its proof stated explicitly. In the full
bottom/top/product arbitrary-tree domain, both directions of
`omega = omega × omega` force `omega = Omega`:

* the root cannot be bottom because `omega × omega <= omega` would fail, and
  cannot be top because `omega <= omega × omega` would fail, so it is product;
* if a top label occurred at a nonempty address `a u`, the inequality
  `omega <= omega × omega` would compare that top to the subtree at `u`,
  forcing a top at `u`; stripping letters reaches a top root, a contradiction;
* with no top labels and a product root, `omega × omega <= omega` propagates
  product labels from every address `u` to both `0u` and `1u`. Induction gives
  every binary address, hence `Omega`.

This uses both equality directions. The first inequality alone is not enough
in an explicit-top domain, because product can be below top. With
`omega = Omega`, the guard lemma is exact: `z <= Omega` holds precisely when
`z` has no top label. A top-labelled address would compare top with a product
at that address and fail; a bottom/product-only tree has all its product
addresses in `Omega`.

The reduction is semantics-preserving over arbitrary trees. A source model
extends by setting `omega = Omega` and interpreting each name by its finite
product expression. Conversely, a target model satisfying the guards has
top-free original variables; the product equations identify each name with
the corresponding source expression by structural induction. Restricting to
the original variables therefore gives a source model, and the translated
query agrees in both directions. The same two maps preserve regularity:
`Omega` is a one-node cyclic graph, and finite products of finite graph
representations remain finite.

The construction does **not** transfer to finite-tree semantics. The fresh
equation has no finite solution in the full domain, so every target query is
vacuously valid even when the source constant-free problem has a finite model
or a failed query. It also excludes C081 premises involving bottom or denial
constraints. Finally, this is an upper-bound direction (C081 fragment to the
NP99 restricted problem); it transfers no NP99 hardness result and does not
establish a regular-only complexity bound without a separate target theorem.

Disposition: after making the root-label proof and the guard lemma explicit,
the fresh-`omega` construction is an **accepted exact polynomial reduction for
the constant-free arbitrary/regular fragment**. It is a different result from
the identity-translation counterexample above and does not decide the full
C081 comparison. No formalization or implementation was added. The owned note
path remains released after this review.
