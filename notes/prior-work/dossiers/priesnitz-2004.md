# PW-PRI04: Chapter 11 straight-language audit

**Source:** Tim Priesnitz, *Subtype Satisfiability and Entailment*, Saarland thesis, title-page year 2004; colloquium 1 April 2005. [Primary PDF](https://d-nb.info/986396834/34). The definition and lemma were checked against page images, not only extracted formulas. Printed p. 111 is PDF page index 124; printed p. 113 is index 126.

**Scope of this finding:** a counterexample to the literal Lemma 11.1. It was first recorded in [issue #36, comment 5737842853](https://github.com/mhenglein/subtail/issues/36#issuecomment-5737842853) and recalculated during consolidation. Independent mathematical review is still requested. It is not a refutation of Theorem 11.1 or of the entire thesis.

## Source statement under test

Chapter 11 defines a language as straight when there are no words `p,u`, with `u` nonempty, such that all `p u^n` for `n >= 0` belong to it. Lemma 11.1 (p. 113) asserts that a straight left language and arbitrary regular right language admit only one factorization of any concatenated word. The proof identifies accepting nodes with the second automaton's start and asserts determinism. Lemma 11.2 then uses uniqueness in eliminating a universal decomposition condition.

## Local counterexample, with no empty-word edge case

Take

```text
R1 = {0, 01}
R2 = {1, 11}
w  = 011

w = 0 . 11
w = 01 . 1
```

Both factor pairs belong to `R1 x R2` and differ. Both languages are finite, so both satisfy the printed straightness definition: if `u` is nonempty, the lengths of `p u^n` are unbounded, which a finite language cannot contain. Thus the hypotheses of the literal lemma hold and its uniqueness conclusion fails.

The ambiguity has a direct automata explanation. A deterministic automaton for `R1` accepts after `0` but may also continue on `1` and accept after `01`. Being cycle-free at accepting states does not forbid that continuation. Identifying those states with the start of an automaton for `R2` does not resolve the choice between continuing the left factor and beginning the right factor. A deterministic recognizer for the *concatenation language* could still exist; that would not make the original factorization unique.

## A sufficient repair for this lemma only

If `R1` is prefix-free, the split is unique: two left factors of the same whole word are comparable by prefix; prefix-freeness forces equality, and cancellation forces equal right factors. This argument applies to that split lemma. It does not establish that every later step of Chapter 11 works after changing its hypotheses, or that the stated straight-language theorem is false.

C067's terminal capture argument should therefore be audited for the stronger property it actually uses. Check that no accepted capture is a proper prefix of another under the applicable state constraints. Do not substitute 'straight', 'finite', 'acyclic' or 'regular' for prefix-free merely because they sound restrictive.

## Reproduction and remaining obligations

`python3 notes/prior-work/check_scholarship.py` checks the two unequal factor pairs and a finite prefix-free comparison fixture. The finiteness argument above is mathematical reasoning, not a bounded test of the universal definition. The script does not implement the thesis's cap construction.

September 19 update: a second agent read the primary definition/lemma pages and independently enumerated the finite example, with access to the earlier dossier. See the [core source review](core-lineage-review-2026-09-19.md). This is not blind whole-proof replication.

Open: audit the precise dependency in Lemma 11.2 and Theorem 11.1; search for errata or a later repair; compare a valid repaired fragment to C067 without assuming a novelty conclusion. Preserve any such repair alongside this counterexample rather than deleting the historical failure.
