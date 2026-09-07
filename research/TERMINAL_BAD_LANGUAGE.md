# Terminal bad-language decomposition

Date: 2026-09-07. Main checkpoint starts from `7b9aa1d`.

**Unrestricted Problem 1.7 remains open.** This record isolates the exact bad-language form for terminal instances; the remaining step is a containment/small-model theorem.

## Exact structural result

For every proper flagged suffix agreement in a terminal `k`-state binary instance, exactly one of two cases holds:

1. **Non-overlap:** the word factors as `x z C z`; the copied `z` is the terminal suffix. State constraints around `x`, the first `z`, `C`, and the final `z` are regular.
2. **Overlap:** the source suffix is periodic with gap `d`; writing its length as `e*d+r`, it has form `y^e prefix_r(y)`, and terminal nonmerging gives `e<=k-1`.

Boundary failures (Bad states, diagonal flags, flags into the final empty suffix) remain regular.

Hence terminal witness existence is exactly regular-language escape from a finite union of state-constrained one-use terminal-copy languages and bounded-period overlap languages. This is an equivalence, not yet a decision theorem.

[Full proof and limits](../notes/2026-09-07-terminal-bad-language-decomposition.md).

## Reproduction

```sh
python3 experiments/check_terminal_bad_decomposition.py
```

The deterministic regression records 852 corpus entries and 435,372 words; 2,630 admissible candidates and 1,770 bad accepted candidates; representative proper violations split 407 non-overlap / 22 overlap; all proper violations split 749 / 32; maximum observed overlap exponent four; zero decomposition mismatches.

[Checker](../experiments/check_terminal_bad_decomposition.py) · [result](../results/terminal-bad-language-decomposition.json).

The finite corpus validates implementation only. The all-length statement rests on the written proof. Independent review and Lean verification are pending.

## Next theorem

The strongest constructive target is a **terminal coloured-border small-model theorem**: prove a computable `F(k)` such that every positive terminal `k`-state instance has some witness of length at most `F(k)`. It need not be small or elementary.

The decomposition means an Anderson-style pumping proof only has to preserve:

- one earlier copy of a terminal suffix in the non-overlap case; and
- bounded-power periodic overlaps, with exponent at most `k-1`.

A second route is to decide the resulting special containment problem directly. Generic word-equation or backreference results do not automatically settle that quantifier pattern.
