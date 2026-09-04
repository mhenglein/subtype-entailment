# Research continuation: exact growth, three states, and summary absorption

Date: 2026-09-04. Base: `b8b8457245b693c760a52b5f445996c0fd2f8b0d`.

This imports the findings previously delivered in the conversation, following an independent replay of the saved checks. **Problem 1.7 is not settled by this continuation.** All new proofs are written mathematical proofs, not Lean formalizations; no literature-priority claim is made. The existing subtype bridge retains its audited/Python status.

## Claims

- **C021 (WRITTEN PROOF + REPRO):** a k-state, one-flag family has exact budget `2k-4`, unique shortest witness length `3k-3`, and boundary-only budget `k-2`. Five states require budget six, refuting the proposed abstract `B<=k` bound. [Full argument](2026-09-04-budget-growth-family.md).
- **C022 (WRITTEN PROOF + REPRO):** every solvable instance with at most three states has a witness of length at most six and budget at most two, both sharp. Witness existence is equivalent to nonemptiness of `Sufficient(2,0)` and `Necessary(1,1)`. [Full argument](2026-09-04-three-state.md).
- **C023 (WRITTEN PROOF + REPRO):** every positive descendant of a final state in an actual paired-summary output is final and has an empty incoming flag column. This remains true with denials. [Construction argument](2026-09-04-summary-absorption.md).
- **C024 (WRITTEN PROOF + REPRO):** total, Bad-free absorbing instances over at least two letters have an exact graph-reachability decision, witness length at most `2k-1`, and budget at most `k-1`. Actual denial-free normalized systems fall in this class, subject to the existing forward bridge. [Proof and limitations](2026-09-04-summary-absorption.md).

These IDs extend, rather than replace, C001-C020. Abstract examples are not silently promoted to subtype-derived lower bounds. The growth examples violate C023 as raw annotated outputs; this does not rule out another encoding or language-equivalent realization.

## Reproduce

Run from the repository root (standard-library Python):

```sh
python3 experiments/continue_research.py
python3 experiments/check_budget_growth_family.py
python3 experiments/three_state_decision.py
python3 experiments/check_summary_absorption.py
```

The scripts use the unchanged repository `border_lab.py`. Generated full results go to `results/`; [the compact replay record](../results/continuation-import.json) records the run imported here. The independent summary implementation intentionally omits denials; it is not a rerun of the complete subtype bridge.

### E016: exact growth family

All 28 parameter pairs `2<=m<=8`, `1<=t<m` were checked, including complete exhaustion of every lower sufficient budget split, with a 200,000-state cap that was never reached. There were 70,680 direct forward/reversed shortest-word comparisons. The all-parameter conclusion comes from the written proof, not the finite census.

### E017: complete three-state normal form

All 65,536 normalized binary instances were classified: 36,640 YES and 28,896 NO. Positive constructions pass forward, reversed, and direct `Sufficient(2,0)` checks. Every negative case independently exhausts `Necessary(1,1)`; the largest negative graph has 65 states. The boundary-normalization proof justifies the normal form. Arbitrary larger instances are not decided by a six-letter cutoff.

### E018: summary absorption and denial-free subclass

Seed 2026090421, 400 generated normalized denial-free systems, two through five variables: no invariant violation, 281 YES, 119 NO, at most eight paired classes. Positive words pass independent predicates; negatives exhaust `Necessary(0,0)`. The six-state prior obstruction and five-state growth instance fail the raw-output invariant.

## Review and next mathematical target

The previous six-state C020 budget-five obstruction was reproduced, as were the reductions in its budget after individual flag removals. The earlier seeded flag-mutation search was inconclusive and is not evidence for an upper bound. The conditional Lean theorem still assumes bounded coverage; an executable word checker is not a word-existence decision.

A009's `B>|K|` target is achieved for abstract instances. A008 now has a complete three-state theorem. A013 has a joint construction invariant and a denial-free decision. The unrestricted next target is to exploit the additional structure of the denial/safety component: padding cannot simply ignore Bad states.

For example, `x <= u * v`, `u <= bottom`, `v <= bottom` allows a root product at x but no product at either child. A separating root need not have a safe nonempty extension. The unrestricted continuation must either derive a safe-continuation theorem or supply another complete argument; failure of a bounded search remains UNKNOWN.
