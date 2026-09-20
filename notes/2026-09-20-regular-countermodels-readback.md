# Regular countermodel construction: independent readback

Date: 2026-09-20. A010/A018, C081, issue #57.
Reviewer: separate read-only Astra context (henglein_rehof_review reused for
this bounded mathematical/software task). Parent supplied definitions and the
existing route, so this is independent source review, not independent invention.
No human peer review is claimed.

## Scope and outcome

The reviewer read pinned `3e41754`, with the extraction source from `93bfffd`:
`regular_countermodel.py`, `subtail.py`, tests and the ordinary route. No files
were edited and no Lean build was run. The new Lean module was absent from
this revision and remained explicitly PENDING.

No false-positive or ordinary completeness blocker was found. The review
checked exact DAG naming, finite balanced closure, reverse-pop language
semantics, suffix attachment on the right, denial language nonemptiness,
fair word enumeration, prefix-closed subset conversion, the original-input
cyclic graph checker, and preservation of a completed negative decision under
extraction failure. Direct zero-spine, full-cycle, forced-denial, zero-variable
and nested-product probes found only independently valid returned graphs.

The reviewer identified two useful explicit invariant checks:

1. Before returning, check that the seed word is accepted at the normalized
   left query control. The construction already implies this fact; an explicit
   check prevents a broken producer from relying on its own assumption.
2. Before mapping a rejected subset to bottom, check that it has no accepting
   descendant. Prefix closure already implies this fact. The finite NFA
   productive-state set makes the check exact.

The parent implemented both checks, with a regression that intentionally
passes a non-prefix-closed language to graph conversion and requires rejection.
The unbounded mathematical argument remains conditional on non-entailment;
Python recursion, memory and process limits can still return UNKNOWN.

## Certificate boundary reviewed

The emitter extends the graph with original expression nodes. Its total
expression-to-node function has a default value outside the finite input
forest. Therefore the Lean checker must recursively check every expression
used in premises/query, while requiring no property of unused expressions.
This contract was agreed with the certificate author in #57.

`--verify-certificate` emits an instance theorem using
`check_not_entails ... (by decide)`. VERIFIED requires the entire Lean process
to succeed and exactly one true marker. A marker printed before a later proof
failure cannot establish verification. JSON parsing and source emission remain
outside Lean; the checked target is the emitted original expression input.
The read-only reviewer did not claim a completed Lean certificate validation.

## Later formal/source validation

The exact completed module, parent readback and fresh combined-tree checks
are recorded in the main construction note and its linked machine receipt.
This review is not retroactively attributed to a module the reviewer did not
read. Changes after `3e41754` retain their own source and validation pins.


### Independent certificate semantic readback

The same separate reviewer then read the complete new module at `a5d0ebc`
(worker source `7a3bcd3`) without editing or building. This was a distinct,
later review, after source release. The reviewer confirmed product/root and
left/right address semantics, prefix closure, every finite table pair's local
simulation obligations, all-word induction, the original arbitrary Tree
valuation, recursive embedding of the whole input forest, and the final
`check_sound`/`check_not_entails` composition. No definition-level mismatch
was found. The parent independently read the same full 371-line module.

The relation need not be reflexive or transitive. Only its true pairs need
local simulation closure, checked over the entire finite pair carrier.
`below_iff_simulation` uses a semantic proposition-valued relation for its
existence direction; it does not implement the producer. The module has no
separate `RegularTree` predicate. Its finite `Graph v` with `treeOf` unfolding
is the precise formal representation. No claim that Python extraction or a
separate regularity/completeness theorem was formalized follows from C084.

The review ended with the worker's scope released. The later parent combined
build/kernel/audit/native results are recorded separately in
[the receipt](../results/regular-countermodels.json), at `d632852` with the
reviewed Lean source unchanged. All 24 declaration dependency closures pass,
including 14 non-theorems with no classical-choice dependency. There are
34 native cases, 15 positive instance proofs, 24 CLI tests and 9 extraction
tests. The actual CLI also produces five VERIFIED instance proofs, including
an independent supplied-model recheck. These tests support the implementation;
the checked general C084 theorem supplies its all-input certificate guarantee.
