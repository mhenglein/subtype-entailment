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

This is a finite set of equality constraints. It is deliberately stronger than requiring equality only along actually realized violations; the strengthening loses applicability, not soundness.

Add two kinds of constants:

1. every transition that belongs to a directed cycle is forced data;
2. every transition entering a terminal final is forced separator.

All equality constraints and constants are solved by union-find. A class forced to both values makes this certificate unavailable. Otherwise unconstrained classes are chosen data.

The cycle test is also deliberately conservative: it includes irrelevant cycles before productive trimming. A future implementation may weaken it without changing this theorem.

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

## 4. Why C053 becomes applicable

Collapse each compiled `10`/`11` data token and each `00` separator. A macro separator corresponds to one marked original transition. If a productive macro cycle contained a separator, decoding that cycle would give an original directed cycle containing a marked transition. But every original cycle edge was forced data. Contradiction.

Flags occur only on original states, all of which are paired-token boundaries. Every accepted word ends in a separator. Therefore the paired `marker_structure` certificate C053 applies to every compiled nonempty slice. Its finite schema cover and exact delimited-convolution solver decide the compiled instance, hence the original instance by comparison preservation.

**Theorem.** Existence of a consistent synchronous-separator colouring is an effective sufficient condition for exact terminal BorderAvoid decidability. Certificate failure is UNKNOWN, never NO.

This is an encoding-aware preprocessing theorem: it can discover a useful logical delimiter even when neither raw symbol has bounded occurrence count.

## 5. It repairs the explicit encoded obstruction

Take C051's five-state NO instance and its exact fixed-length encoding `C(0)=00, C(1)=10`, producing the ten-state obstruction from the marker-tail note. The union-find certificate marks exactly

    (0,0), (1,0), (3,0)

in the ten-state encoded automaton. These are the first physical transitions of the logical zero tokens. The physical loop transitions implementing logical ones remain data. The marked classes are synchronized across every potential flagged comparison, and no marked edge lies on a directed cycle.

Compiling this colouring exposes exactly two logical separators on every accepted candidate. C053 then exhausts the finite cover and returns NO. Hence the counterexample to raw-marker completeness is **not** a counterexample to synchronous-separator preprocessing.

The original five-state source is certified directly as well.

## 6. Genuine limitation

The certificate need not exist. In the three-state fixture

    0: 0 -> 0, 1 -> 1
    1: 1 -> 2
    2: terminal
    G={(0,1)},

synchrony equates the `1` transition at state 0 with the `1` transition at state 1. The former lies on a productive cycle and is forced data; the latter enters the final and is forced separator. The equality class is inconsistent, so the method returns UNKNOWN.

This conflict is structural for this particular colouring theorem. It does not prove the fixture hard, and it does not rule out a richer variable-length code, a different finite cover, shared-word synthesis, or undecidability.

## 7. Reproduction and scope

Run

    python3 experiments/check_synchronous_separators.py

The checker exhausts all normalized terminal tables/flag sets through three states, validates compiled/original witness equivalence on defined short words for every certified instance, and runs the downstream C053 solver uncapped on each certified case. It separately checks the ten-state encoded obstruction and the explicit colouring-conflict fixture. Exact counts are recorded in `results/synchronous-separators.json` by CI.

The proof is the all-length argument above; bounded word checks are regression evidence, not its justification. The downstream C053 theorem retains its consolidated `WRITTEN PROOF + REPRO` status. Existing Lean jobs may pass without formalizing this new theorem.

## 8. Next question

The conflict fixture identifies the next precise generalization: permit a finite-state code in which an aligned transition may be represented at different separator depths while preserving equality of the complete codeword, rather than demanding one Boolean colour per aligned transition. Equivalently, search for a finite congruence/code on synchronized transition pairs whose cyclic classes are pumpable and whose terminal classes are cuttable. This is closer to an encoding-aware finite symbolic cover than to another raw numeric budget.
