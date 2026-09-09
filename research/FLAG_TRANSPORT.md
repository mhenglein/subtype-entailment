# A017/A012: flag transport and essential separator obstructions

Date: 2026-09-08. Base `c4875e599958dd624dd7220dd7cbe5bb96822b11`.

**Written proof + reproduced checks; independent mathematical review pending;
not Lean-checked. Unrestricted Problem 1.7 is not solved.** This scoped record
allocates no new global C/E identifiers.

## Result

The semantic-tail solver now accepts arbitrary regular data over an internal
separator alphabet, so it composes with the exact synchronous compiler.
This handles the newest target-recurrent fixture, but the hoped-for complete
negative procedure fails: a nine-state essential-flag NO instance survives
every separator-tail budget under every permitted fixed-annotation colouring.
One actual, unique comparison forces the cyclic marker class. An eleven-state
nonflat extension has the same obstruction with all four flags essential.

An exact new local rewrite moves a flag across its uniquely reversible common
letter. It preserves the entire witness language, while allowing comparison
positions and budget certificates to change. Finite proof-carrying placement
search repairs both examples. The nonflat example is proved NO at H=1 even
though a marked cycle remains reachable from relevant targets. A positive
companion is decided YES with 101000101000.

## Evidence

[Full proof, counterexamples, review correction, and limitations](../notes/2026-09-08-flag-transport-and-separator-obstruction.md).
[Transport and encoding](../experiments/flag_transport.py).
[General-data semantic-tail combination](../experiments/separator_tail.py).
[Independent checker](../experiments/check_flag_transport.py).
[Deterministic output](../results/flag-transport.json).

    python3 experiments/check_flag_transport.py

Seed 2026090881. The record covers 1,034 normalized small instances, 160 random
instances, 220 complete finite-language oracles, 97 exact source-reference
observation oracles, 193 weighted action graphs, and explicit analytic positive
and negative families. See the proof/result for exact cutoffs, omissions and
caps. A stopped or capped computation is never a NO proof.

## Remaining obligation

Neither the finite placement orbit nor its heuristic score is proved complete
for unrestricted decision. A global solution still needs an effective complete
normal form/cover, a complete negative calculus, or an exact undecidability
reduction. The counterexamples refute fixed-annotation separator convergence,
not arbitrary semantic rewrites or decidability.
