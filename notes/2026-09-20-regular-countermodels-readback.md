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
