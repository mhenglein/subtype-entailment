# Regular-middle erasure as a candidate-changing NO rule

Date: 2026-09-08. Base main: `18d9f9ad4f342c9ebf8c552f531a0d7f5feaf698`.
Workstreams: A012 / A017; continuation of issue #15 and the synchronized-tail regular-decoration barrier.

**Status: written proof + independent finite regression. Not Lean-checked or independently mathematically reviewed. This does not solve unrestricted Problem 1.7.**

## 1. Why this is a different move

The regular-decoration barrier proves that no finite candidate-covering regular choice of separator bits, followed by a fixed finite semantic-tail budget, can be complete. Its assumptions preserve every original candidate and change only annotations/markers.

This note uses a different quantifier order: for a certified regular middle region we **delete the middle word itself**. The rule is only used when a concrete forbidden comparison can be transferred back to every original candidate. It is therefore a G-specific candidate-changing normalization, not a decoration.

The first target is the six-state nonflat NO benchmark from `notes/2026-09-08-synchronized-tail-and-regular-marking-barrier.md`.

## 2. The benchmark language

Use the six-state terminal instance

    G = {(0,2),(0,3),(1,2)}

with transitions

| state | 0 | 1 |
|---|---:|---:|
| 0 | 1 | 2 |
| 1 | 1 | 2 |
| 2 | 3 | undefined |
| 3 | 3 | 4 |
| 4 | 5 | 2 |
| 5 | undefined | undefined |

Its accepted language is exactly

    0^n 1 M 0^m 10,
    n >= 0, m >= 1,
    M in (0^+ 11)*.                                  (A)

The middle language is genuinely nonflat: at state 2 it uses both the zero loop at 3 and the cycle `2 --0--> 3 --1--> 4 --1--> 2`.

Define the erasure map

    E(0^n 1 M 0^m 10) = 0^n 1 0^m 10.               (B)

This deletes an arbitrarily long productive recurrent region.

## 3. Three-case selector on the erased core

Let `w = 0^n 1 M 0^m 10`, let `N=|w|`, and let

    j = N-m-2

be the cut entering the final `0^m10` tail.

Exactly one arithmetic branch applies.

* `n < m`: choose source `i=0` and target `t=N-n-2`. The target is in state 3 and its suffix is `0^n10`. The source prefix of the same length is also `0^n10`: after the initial `0^n1`, the next letter is 0 because either `M` is empty and the final zero run begins, or `M` is nonempty and every nonempty member of `(0^+11)*` begins with 0. Thus `(0,3)` is a forbidden comparison.
* `n = m`: choose `i=0`, `t=j`. State pair `(0,2)` is flagged and both compared fragments are `0^m10`.
* `n > m`: choose `i=n-m`, `t=j`. The source is in state 1, the target in state 2, and both compared fragments are `0^m10`; `(1,2)` is flagged.

These are the same three cases as on the erased word `E(w)`. The middle contributes neither a selected endpoint nor any compared letter except the single first 0 used in the `n<m` source fragment.

## 4. Erasure theorem

**Theorem (regular-middle erasure for the benchmark).** For every accepted word `w` in (A), the erased word `E(w)` is accepted. Moreover the arithmetic branch selected from `(n,m)` yields a proper forbidden comparison in both `w` and `E(w)`. Hence

    E(w) bad  =>  w bad,

and in fact both sides are bad for every admitted `(n,m,M)`.

**Proof.** Every `M in (0^+11)*` labels a loop from state 2 back to state 2. Deleting it therefore preserves the boundary state at the start of the final zero run and yields an accepted erased word. The three comparisons above depend only on `n,m`, the fixed flagged boundary states, and the fact that every nonempty `M` begins in 0. Their suffix-equality checks are unchanged after shifting the final-tail target left by `|M|`. Thus each selected comparison exists in the original word exactly as stated. QED.

This is deliberately one-way proof engineering: we do **not** assert that erasure preserves the complete agreement profile or witnesshood on arbitrary inputs. For a NO proof it is enough that a certified violation on the normalized core lifts back to every original candidate.

## 5. Reusable rule suggested by the proof

The benchmark exposes a more general proof rule worth pursuing.

A regular middle language `L` at a boundary state `q` is **comparison-isolated for a selector** when:

1. every `M in L` returns the run from `q` to the same boundary state `q`;
2. the selector's source/target states outside the middle are therefore unchanged by deleting `M`;
3. every selected compared fragment is disjoint from the interior of `M`, except possibly for a fixed finite prefix of `M` whose letters are common to every nonempty member of `L`;
4. the empty/nonempty alternatives are covered explicitly.

Under these conditions deleting `M` preserves that selected violation. This gives a sound candidate-changing NO rule for arbitrary regular, potentially nonflat middle languages. The finite common prefix can be checked by ordinary DFA language tests. What is still missing is a complete algorithm that finds a finite family of such selectors/erasures for every NO instance.

This differs fundamentally from separator decoration: the middle candidates are discarded modulo a proof-relevant boundary summary.

## 6. Evidence

`experiments/check_regular_middle_erasure.py` independently implements the DFA run, accepted-language parser, direct forbidden-comparison predicate, three-case selector, and erasure map.

It checks:

* all 32,767 binary words through length 14; all 262 accepted words parse into (A), all are certified, and none is a witness;
* 6,240 structured candidates with `n=0..12`, `m=1..12`, and zero to three middle cycles with each zero-run length in `1..3`;
* all 6,084 nonempty-middle cases preserve acceptance after erasure and preserve the selected arithmetic branch and a concrete forbidden comparison;
* structured words up to length 42, exercising genuinely nonflat middles.

Finite testing supports but does not replace the all-length proof above.

## 7. Consequence and next target

The regular-decoration barrier does not force a retreat to pure arithmetic casework. A recurrent SCC can sometimes be quotiented away by a **proof-directed word transformation** when the selected violation only sees its interface.

The next useful theorem is to make Section 5 effective: enumerate candidate middle SCCs, compute their common finite interface prefixes and boundary actions, and search for a finite arithmetic selector cover whose comparisons avoid the erased interiors. A complete termination/coverage theorem is still absent, so unrestricted Problem 1.7 remains open.
