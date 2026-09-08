# Synchronous separators: encoding-aware finite covers

Date: 2026-09-08. Continues A012/A017 after `d545bce5b040b344f1b293edfa83803fd568f1f9`.

**Status: written proof + reproducible checks; independent mathematical review pending; not newly Lean-checked. Unrestricted Problem 1.7 remains open.**

## 1. Motivation

The semantic-marker-tail attempt is exact when actual last-aligned violations contain only boundedly many copies of a chosen raw bit. Its explicit ten-state counterexample shows that no raw-bit choice is complete: the fixed code `0 -> 00, 1 -> 10` turns one logical zero into two physical zeros and makes every finite raw-zero tail bound survivable.

That obstruction is encoding artefact rather than new word equality. This continuation asks whether a finite-state transition colouring can expose a latent separator structure while preserving every flagged suffix comparison.

## 2. Synchronous transition colouring

Let I be a binary terminal BorderAvoid instance. Give every defined transition `(p,a)` a Boolean colour: data=0 or separator=1.

Start a synchronized pair graph at every flag `(p,q)`. Whenever both states have an `a` transition, advance to `(delta(p,a),delta(q,a))`. A colouring is **flag-synchronous** when every such aligned transition pair has the same colour:

    colour(p,a) = colour(q,a).

This is a finite set of equality constraints. It is deliberately stronger than requiring equality only along actually realized violations; the strengthening loses applicability, not soundness. Every transition entering a terminal final is forced separator. Union-find solves these equality/constant constraints, with unconstrained classes chosen data.

Two downstream certificates use the same synchrony relation:

1. **C053 mode:** additionally force every transition belonging to a directed cycle to data. A conflicting equality class makes this mode unavailable.
2. **C056 mode:** do not force cycle edges to data. If synchronization with a final edge marks a cycle, compile it and let the target-frontier theorem decide whether that marker cycle occurs only before relevant targets.

Thus the second mode strictly subsumes the artificial failure where a final edge is synchronized with an early source loop.

## 3. Exact binary compiler

Encode one original transition labelled `a` as

    data transition:       1a
    separator transition:  1a 00.

This is the existing paired token alphabet: `10` and `11` are data tokens, `00` is a separator. The compiler inserts deterministic helper states. Original states remain token boundaries and retain exactly the original flags, Bad annotations, start and terminal finals. Helpers have no annotations.

Every original accepted word has exactly one compiled word and conversely every compiled accepted word parses uniquely back to the original run. Because every transition into a final is a separator, every nonempty compiled candidate ends in `00`.

### Comparison preservation

Consider original positions i<j with a flagged state pair. If the original suffix from j is a prefix of the suffix from i, the two runs read the same letter at every aligned position. Their state pair therefore follows the synchronized graph rooted at that flag. Flag synchrony makes their separator colours equal at every aligned transition. Each corresponding encoded transition is consequently the same `1a` or `1a00`, so the compiled suffix agreement holds.

Conversely, a compiled flagged comparison starts at two original states because helpers carry no flags. Parsing from either boundary is unique: every transition contributes `1a` and may then contribute `00`. Equality of the compiled strings therefore implies equality of the decoded original letters, hence the original suffix agreement. Boundary, Bad, diagonal and empty-suffix conditions are unchanged because annotations remain on original states.

Thus for every original word w,

    Witness_I(w)  iff  Witness_C(I)(encode(w)).

The same argument preserves the entire set of flagged comparisons after decoding; no assumption about a particular witness is used.

## 4. Downstream exactness

### C053 mode

Collapse each compiled `10`/`11` data token and each `00` separator. A macro separator corresponds to one marked original transition. If a productive macro cycle contained a separator, decoding that cycle would give an original directed cycle containing a marked transition. But every original cycle edge was forced data. Contradiction.

Flags occur only on original states, all of which are paired-token boundaries. Every accepted word ends in a separator. Therefore C053's finite schema cover decides the compiled instance exactly.

### C056 mode

Drop the cycle=data constants but retain synchrony and final=separator. Any marked cycle in the compiled macro graph is now an actual original cycle whose transition class was forced separator by synchronization with a final transition. C056 permits arbitrarily many such marker cycles before the first relevant target. Its common-reference powerset keeps those early blocks tied to the same retained suffix tuple.

Therefore, when C056 certifies the compiled instance, its answer transfers exactly back through the compiler. A marker cycle reachable from a relevant target remains UNKNOWN; its existence is not a negative verdict.

**Theorem.** Either finite colouring certificate followed by its stated downstream solver is an effective exact decision procedure on the certified terminal class. Certificate/downstream failure is UNKNOWN, never NO.

## 5. It repairs the explicit encoded obstruction

Take C051's five-state NO instance and its exact fixed-length encoding `C(0)=00, C(1)=10`, producing the ten-state obstruction from the marker-tail note. The strict union-find certificate marks exactly

    (0,0), (1,0), (3,0)

in the ten-state encoded automaton. These are the first physical transitions of the logical zero tokens. The physical loop transitions implementing logical ones remain data. The marked classes are synchronized across every potential flagged comparison, and no marked edge lies on a directed cycle.

Compiling this colouring exposes exactly two logical separators on every accepted candidate. C053 exhausts the finite cover and returns NO. Hence the counterexample to raw-marker completeness is **not** a counterexample to synchronous-separator preprocessing. The original five-state source is certified directly as well.

## 6. Early-cycle strictness is removable; target-recurrent cycles remain

Consider

    0: 0 -> 1, 1 -> 0
    1: 1 -> 2
    2: terminal
    G={(0,1)}.

The final `1` edge from state 1 is synchronized with the `1` self-loop at state 0. Strict C053 mode therefore conflicts: the former must be separator and the latter was forced data. In C056 mode both are separators. The resulting marker loop is at state 0, before target state 1; it is not reachable from that target. Target-frontier pumping decides the compiled instance exactly and returns a genuine original witness. So this is not a real limitation of synchronous separators.

A sharper three-state fixture is

    0: 0 -> 1, 1 -> 0
    1: 0 -> 0, 1 -> 2
    2: terminal
    G={(0,1)}.

The same synchronized `1` loop is now reachable from target state 1 through its `0` edge. C056 rejects the structural certificate and the wrapper returns UNKNOWN. This is the next preserved obstruction. It does not prove the fixture hard and does not rule out target-local pumping with a richer context, another code, shared-word synthesis, or undecidability.

## 7. Reproduction and scope

Run

    python3 experiments/check_synchronous_separators.py

The checker exhausts normalized terminal tables/flag sets through three states, validates compiled/original witness equivalence for certified colourings, and runs downstream exact solvers. It separately checks the ten-state encoded obstruction, the early-cycle case rescued by C056, and the target-recurrent marker-cycle UNKNOWN fixture. Exact counts are recorded in `results/synchronous-separators.json` by CI.

The proof is the all-length argument above; bounded word checks are regression evidence, not its justification. C053/C056 retain their consolidated `WRITTEN PROOF + REPRO` statuses. Existing Lean jobs may pass without formalizing this new theorem.

## 8. Next question

The remaining obstruction is now narrower: a separator class forced by terminal synchronization can lie on a productive cycle reachable from a relevant target. The next target is to combine this encoding-aware compiler with the semantic-tail/pending-context machinery so that target-recurrent separator cycles can be summarized rather than structurally forbidden. Equivalently, seek a finite congruence on synchronized transition classes whose recurrent separator obligations compose with one common reference tuple.
