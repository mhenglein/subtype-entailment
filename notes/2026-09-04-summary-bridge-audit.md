# Summary bridge audit

Date: 2026-09-04

This note records an independent audit of the summary layer in
`experiments/summary_bridge.py`. The audit used a separate bounded PDS search
for Pop summaries and denial reachability. It did not modify the summary
implementation.

## Fixes verified

Two defects found in the first review are now fixed:

1. `build_pop_summary` converts its `rules` iterable to a tuple before both
   passes. A generator containing a push followed by a matching pop now
   produces the expected empty-stack summary.
2. `build_summary_bridge` rejects unsatisfiable systems. This prevents an
   `S` monitor that only sees alpha-seeded denials from being interpreted as a
   countermodel for a system whose forced roots already contradict a denial.

The explicit regression checks also cover absent query variables and the
empty query word.

## Independent checks

Run:

```sh
python3 experiments/check_summary_bridge_audit.py
```

The run uses seeds `20260904`, `20260904`, and `222` for the Pop, denial
monitor, and summary/canonical checks. The saved result is
[`results/summary-bridge-audit.json`](../results/summary-bridge-audit.json).

The checks report:

- `98,053` Pop-summary attempts over 300 random PDS instances. Direct
  exploration had `68,839` known comparisons and `29,214` `UNKNOWN` results.
  It uses a word-relative stack cap of `|word| + 5` and a `10,000`
  seen-configuration cap.
- `12,400` denial-monitor attempts over 400 random normalized systems and all
  binary words through length four. Direct exploration had `10,675` known
  comparisons and `1,725` `UNKNOWN` results. It uses 250 steps and stack
  length ten.
- `28,956` comparisons between the generated summary witness predicate and
  `canonical_countermodel` over 228 satisfiable systems and all binary words
  through length six. 147 cases include an absent query variable.
- Zero mismatches in the direct suffix predicate versus the independent
  reversed-border predicate.

The direct oracles return `UNKNOWN` whenever a stack, step, or seen-state cap
prunes an enabled successor. They compare Boolean answers only when the
bounded search fully exhausts its capped graph. A witnessed reachability still
returns `True` immediately; a capped search never treats a missing witness as
`False`.

## Scope and limits

The orientation is consistent with the memo: `B(u)` uses `Pop_W(alpha, -)`,
`A(u)` uses `Pop_{W^rev}(beta, -)`, and flags are
`B(c_i) intersect A(c_j)`. The denial monitor accepts every residual stack by
looping its internal final state. Its bad state therefore persists after a
denial-reachable prefix, which is required by condition `(S)`.

These results are bounded evidence. They do not prove the all-length
P-automaton saturation theorem, the summary-to-border reduction, or a
decision procedure for Problem 1.7. Those remain Lean and mathematical proof
obligations.
