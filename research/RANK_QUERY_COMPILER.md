# Rank-query compiler and proposed unrestricted witness bound

Date: 2026-09-17. Base main: `afbb2954bb984998db3ecac252b5e2e23f62341a`.

**PROPOSED COMPLETE PROOF; INDEPENDENT REVIEW PENDING; NOT LEAN-CHECKED.**
This does not by itself promote Problem 1.7 to the project's established results.
No stable C/E ID is allocated. It continues [the published candidate](RANK_QUERY_CANDIDATE.md).

## What changed

The previous proof's full symbolic preimage construction is now implemented,
not just its concrete graph kernel. The finite diagram enumerator and compiler
have no concrete base-graph or word argument. Their output is again an existential
directed regular-path query with finite-colour guards. Actual compiled queries
are fed back through the compiler in the nested regressions.

The proof now spells out the shared interval controller, including delayed
next bits, positive-length guards, old-end recolouring, origin aliases, single-
vertex extensions, portal constraints and one shared assignment across all
observations. It supplies the explicit clause-size bound

    U_k(T)=64*k*T^(2T+2).

Taking T_0=k+10 and T_(j+1)=U_k(T_j), it derives the proposed all-state bound

    F(1)=0,
    F(k)=2*(k+1)*product_{j=1,...,k-2}(T_j+2), k>=2.

If the closure proof is correct, this bounds SOME witness of every positive
binary terminal instance, and yields decidability through finite search or
query elimination. C031 supplies the prior transfer to arbitrary-tree subtype
entailment at its recorded status. No useful runtime bound or new independent
audit of that bridge is claimed. External review of the closure theorem remains
necessary before the project records an established unrestricted solution.

[Full proof and review checklist](../notes/2026-09-17-rank-query-closure-audit.md).

## Source and reproduction

- [Finite predicate, observer and query grammar](../experiments/rank_preimage_core.py).
- [Full finite enumerator, compiler, repeated-query driver](../experiments/rank_preimage.py).
- [Independent graph-semantic and nested compiler checks](../experiments/check_rank_preimage.py).
- [Deterministic results](../results/rank-preimage.json).

```sh
python3 experiments/check_rank_preimage.py
python3 experiments/run_experiments.py
```

The run exhausts four complete tiny query-preimage unions (13,248 clauses),
with two positive and two negative all-length oracles. It checks 263 compiled
diagrams, 971 base evaluations and 694 reconstructed common-reference models,
including changed OLD base lengths. It compiles 21 successive preimages for
modular ranks two through seven and evaluates the final clauses on two-vertex
initial graphs. Those nested tests are certificate-guided positive branches,
not exhaustive searches of the full huge unions. All 1,152 two-state terminal
oracles agree (154 YES, 998 NO); one unguided promoted search finds 00.

The symbolic products may have huge declared state cardinalities; the tests do
not materialize every potential state. The generic driver still reaches its
200,000-work cap on the recorded infinite one-flag negative and three-copy
positive fixtures. Caps return UNKNOWN, never an unrestricted negative. A
reconstruction cap also returns UNKNOWN with a separate positive-query flag.

The code and tests are from the same research session. Differential oracles
are not independent mathematical refereeing. No Lean build, full repository CI,
or broad practical benchmark of the unrestricted algorithm has been completed.
The previous candidate and all failed quotient/counterexample records remain
unchanged except for a navigation link to this follow-up.
