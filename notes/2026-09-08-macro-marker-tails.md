# Macro marker tails with recurrent targets

Date: 2026-09-08. Continues `notes/2026-09-08-synchronous-separators.md` and the fixed-H semantic-tail construction.

**Status: written proof + executable regression; independent mathematical review pending; not Lean-checked. Unrestricted Problem 1.7 remains open.**

## 1. Point of the continuation

C056 permits marker cycles only before the first relevant flag target. The synchronous-separator compiler exposed a precise failure of that structural condition: a separator class forced by synchronization with the terminal edge may lie on a productive cycle reachable from a target.

That restriction is not inherent to the pending-context monitor. The September 8 semantic marker-tail construction already permits every original target state in an arbitrary prefix, but its source reconstruction assumes homogeneous unary data blocks. C056, conversely, already reconstructs arbitrary binary data blocks relative to one retained shared reference suffix, but unnecessarily restricts those source blocks to target-free states.

The constructions compose. The result below removes the target-free restriction for **supplied-H paired macro-marker tails** while retaining arbitrary binary data blocks.

## 2. Macro model

Use the paired token parser already shared by C053/C056:

- macro data `0` is raw token `10`;
- macro data `1` is raw token `11`;
- macro separator `#` is raw token `00`.

Relevant flags occur only at macro boundaries. Every nonempty accepted paired word ends in `#`.

An accepted macro word is written

    u_1 # u_2 # ... u_r #

with each `u_i` an arbitrary binary word accepted by the data-only macro graph.

For fixed H, retain every flagged comparison whose **target suffix contains at most H separators**. Boundary failures remain unconditional. A word is H-safe when none of those retained comparisons is a prefix agreement.

This is a relaxation: a genuine witness is H-safe for every H. If an independent theorem says every realizable last-aligned violation contains at most H separators, then H-safety is exactly witnesshood.

## 3. Finite suffix cover for supplied H

Every nonempty candidate has either fewer than H blocks or at least H blocks.

- For `r < H`, retain the entire word. Its first block starts at the macro start state.
- For `r = H`, retain the final H blocks and summarize an arbitrary earlier prefix. The first retained block may start at any productive macro state.

For a fixed number r of retained blocks, a schema records `(begin_i,end_i,after_i)` where `u_i` is an arbitrary data-only path from `begin_i` to `end_i` and `end_i --#--> after_i`. Because there are finitely many macro states and r is fixed, there are finitely many schemas. Data-only reachability suffices to enumerate them; no bound on `|u_i|` is imposed.

## 4. Shared reverse reference search

For one schema, choose all retained words `u_i` simultaneously by reading them right-to-left. The finite reference state records:

1. the current macro coordinate of every retained word;
2. which pairs of retained suffixes are still equal;
3. which flagged equalities have already been observed;
4. a finite set of descriptors for **all possible earlier source blocks** relative to the same retained reference tuple.

A descriptor

    (end, q, equal-mask, hit-mask, done)

has exactly the interpretation used in C056: it represents a possible earlier source block whose right endpoint before `#` is `end`, whose current reverse coordinate is `q`, whose equality relation to the retained reference words is `equal-mask`, and whose observed flag hits are `hit-mask`. `done` records whether the source word has already emitted left padding.

The crucial change from C056 is only this:

    source predecessor graph = all macro states,

not `states - flag_targets`.

Every source state with an outgoing marker is admitted as a possible earlier block endpoint. This is finite. No target visit is erased; flags are observed at every aligned reverse coordinate exactly as before.

## 5. Why recurrent targets do not require a new descriptor field

A target visit matters only when it participates in an actual suffix comparison. Such a comparison is determined by:

- the source macro state at the aligned position;
- the corresponding reference macro state;
- continued equality of the emitted suffix letters.

Those are already represented by the descriptor coordinate, equality mask, and hit mask. Merely visiting a target state without a matching source/reference flag pair creates no obligation. Therefore banning target states from the source predecessor graph was a sufficient structural shortcut for C056, not an invariant required by the shared-reference semantics.

When the source block itself crosses arbitrarily many marker cycles, it is represented as a sequence of finite observations, one per macro block. The pending mask below composes those observations.

## 6. Pending-context monitor

After the retained reference tuple is fixed, each earlier block induces a finite observation

    (source_start, next_state_after_#, equality_mask, hit_mask, source_end).

As in the semantic-tail proof, a pending bit `j` means that a flag hit against retained block j has occurred and can become a complete forbidden suffix agreement if subsequent macro blocks continue matching the shifted retained tuple.

For every observation the transition:

- advances old pending obligations whose equality bit survives;
- rejects any obligation that reaches beyond the final retained block;
- creates shifted obligations from newly observed flag hits.

The monitor state is

    (macro_state, pending_mask),

so for fixed r it has at most `|K| * 2^(r-1)` states. Breadth-first search therefore decides whether an arbitrary number of omitted earlier blocks can reach the first retained cut without completing a retained comparison.

This proof does not mention whether intermediate macro states are targets. All target-sensitive information enters through actual flag observations.

## 7. Reconstruction remains finite with arbitrary binary source data

C056's `recover_block` already solves exactly the needed problem. Relative to concrete retained reference words, recover a source data word producing a chosen finite observation by reverse BFS over

    (time, macro_state, equality_mask, hit_mask, done).

Once all reference words have emitted padding, equality bits are zero. Any additional unmatched left extension can be shortened to a simple data path without changing a flag/equality observation, so a representative exists with length at most

    max_i |u_i| + |K|.

This argument depends on finiteness of the macro graph, not target-freeness. Thus arbitrary binary source blocks are reconstructible after removing the C056 target exclusion.

## 8. Exact fixed-H theorem

**Theorem (macro marker-tail relaxation).** For every paired-token terminal BorderAvoid slice and supplied integer H>=0, H-safety is decidable effectively. The construction permits arbitrary earlier prefixes, including repeated visits to every flag target and arbitrary marker cycles. If it returns YES, the reconstructed raw word satisfies the exact H-relaxation. If its finite graph exhausts, the H-relaxation is empty. Resource caps return UNKNOWN.

**Proof.** The finite schema cover is exhaustive by the final-H-block split. For one schema, reverse reference saturation enumerates exactly the possible common retained suffix tuples and all source-block observations relative to that same tuple. The pending monitor is equivalent, by induction on omitted prefix blocks, to the set of cross-block flag hits that can still complete a retained suffix equality. Reconstruction supplies concrete data words for every chosen observation. Hence accepted finite states correspond exactly to H-safe words, and every H-safe word maps to one accepted finite state path. Finiteness follows from fixed H and finite macro state/mask spaces. QED.

This is the arbitrary-binary-data analogue of the earlier unary semantic-tail theorem.

## 9. The former target-recurrent fixture is no longer an obstruction

Take the original three-state terminal instance

    0: 0 -> 1, 1 -> 0
    1: 0 -> 0, 1 -> 2
    2: terminal
    G={(0,1)}.

The synchronous colouring marks the final `1` edge and, by synchronization, the `1` loop at state 0. State 1 is a relevant target and can return to that marked loop via `0`, so C056 rejects the compiled instance as `Marker cycle reachable from a flag target`.

But the original word `01` is a witness: its flagged positions carry suffixes `01` and `1`, which do not agree. After compilation the word is `10 11 00`, i.e. raw `101100`, with one final macro separator. The H=1 unrestricted-target macro-tail solver reconstructs this witness. Thus the C056 structural rejection was a genuine abstraction limitation, not evidence of hardness.

## 10. What remains

This theorem removes **target recurrence** as a structural obstacle when a suitable finite macro-separator bound H is available. It does not prove that such an H exists for every positive or negative instance.

The next exact question is now cleaner:

> Is the number of macro separators in realizable last-aligned comparisons effectively bounded, or can unbounded separator spectra themselves be summarized without retaining a fixed final H blocks?

The existing raw-letter weighted spectrum is not enough because paired data token `10` contains a physical zero. The correct next primitive is a **macro-token weighted spectrum**, assigning cost 1 only to `#` transitions and cost 0 to data tokens `0,1`. Because paired token boundaries are synchronized and uniquely parsed, this spectrum is encoding-invariant for the synchronous-separator compiler.

If that macro spectrum is finite, its exact maximum H composed with this theorem gives another exact decision class, now allowing separator cycles reachable from relevant targets.

## 11. Reproduction

Run

    python3 experiments/check_macro_marker_tails.py

The regression differentially records that C056 returns UNKNOWN on the target-recurrent positive fixture while the H=1 macro-tail solver returns YES and reconstructs a raw witness. Additional small compiled fixtures exercise H=1,2,3 shared-reference searches.

Implementation: `experiments/macro_marker_tail.py`.
Recorded result: `results/macro-marker-tails.json`.
