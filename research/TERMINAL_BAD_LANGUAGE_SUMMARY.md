# Terminal bad-language decomposition: concise handoff

The exact current frontier is now:

> For terminal binary BorderAvoid, every proper violation is either a one-use earlier copy of the terminal suffix, or a bounded-power periodic overlap with exponent at most `k-1`.

Therefore the remaining unrestricted terminal decision question is equivalent to deciding whether the regular candidate language escapes a finite union of those two special bad-language families.

This is **not yet a decision theorem**. The primary next proof target is a coloured-border small-model theorem giving any computable witness bound `F(k)`, or an exact decision procedure for the special containment problem.

See [the full proof](../notes/2026-09-07-terminal-bad-language-decomposition.md), [research record](TERMINAL_BAD_LANGUAGE.md), [checker](../experiments/check_terminal_bad_decomposition.py), and [saved result](../results/terminal-bad-language-decomposition.json).
