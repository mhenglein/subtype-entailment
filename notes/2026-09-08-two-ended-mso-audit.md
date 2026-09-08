# Two-ended MSO audit: why the naive Rabin shortcut is incomplete

Date: 2026-09-08. Workstream: A017 / direct-semantics audit.

**Status: scope/falsification note. This is not an undecidability proof for Problem 1.7, and it does not rely on an unverified enriched-MSO theorem.**

## 1. The tempting argument

The top-free semantics identifies each type variable with an arbitrary prefix-closed subset of `{0,1}*`. It is tempting to quantify one monadic set variable per type variable in the ordinary full binary tree and invoke Rabin's decidability of S2S.

That argument has a missing definability step.

## 2. The orientation mismatch

In the repository's exact bridge conventions, product propagation acts on the **leading** symbol of a path word: lower clauses prepend a symbol and upper clauses use the corresponding left quotient.

Ordinary prefix closure, however, is ancestor closure in the standard binary tree with successors

    w -> w0,   w -> w1,

so it removes symbols at the **right-hand** end.

An exact direct encoding would therefore need to express a cross-end relation such as

    y = 0x,

while the standard tree primitives directly express `y=x0` and `y=x1`.

The first draft jumped from this observation to a literature claim about the monadic theory of an enriched two-ended tree without giving a traceable source. That claim is not needed here and is withdrawn from the consolidated record.

## 3. What is actually established

A proof that simply treats `x -> 0x` as one of Rabin's ordinary successor relations is invalid: it has silently changed the structure. To rescue the S2S route one must **prove** that the required left-prefix relation is definable in the ordinary full binary tree, or supply another encoding that avoids it.

This note establishes only that the naive translation has this unresolved step. It does **not** establish that left-prefix is undefinable in S2S, that any enriched MSO theory is undecidable, or that the subtype fragment is undecidable.

## 4. Structural consequence

The orientation mismatch remains useful guidance. Prefix-closed semantic seeds and product propagation access opposite ends of a path word, and the BorderAvoid suffix/border formulation records that synchronization explicitly. Any direct logical shortcut must account for that two-ended interaction rather than assuming it away.

The honest routes remain:

1. prove a finite/well-founded normalization for the restricted Horn/pushdown fragment;
2. find a valid logical encoding with every required relation proved definable; or
3. prove undecidability by an explicit reduction using only the normalized constraint forms.

The current constructive frontier is still the terminal coverage problem: after boundary normalization, obtain a complete finite representation of the synchronized state-coloured suffix obligations, or a different terminating certificate calculus.
