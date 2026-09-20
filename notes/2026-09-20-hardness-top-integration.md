# Hardness and explicit-top integration

Date: 2026-09-20. Session: `hardness-top-integration-20260920`.
Workstreams A010/A017/A018; ownership #37, theorem tasks #70/#71.
Base main: `d190256860a6e80b9eb2a40e2644bf8130271f53`.
Branch: `codex/hardness-top-integration-20260920`.

## Result and exact scope

[C087](../research/claims.md#c087) establishes ordinary PSPACE hardness for
arbitrary and regular bottom/product entailment by deterministic logspace
reduction. It covers every target valuation in the positive direction and
constructs one simultaneous regular negative model. All produced premises are
satisfiable, but no produced system has a finite model. Thus the finite-tree
lower bound and full-input PSPACE membership remain open.

[C088](../research/claims.md#c088) establishes an ordinary arbitrary-tree
explicit-top decision reduction to at most four C081 calls. Exact totalized
observations, finite naming, two projections, forced-top closure, universal
lifting under opposite SAT and inconsistency gates are all part of the
argument. Lean checks arbitrary-language lifting and decomposition. Labelled
tree representation/order, the finite expression compiler and final executable
composition remain ordinary proofs. This adds no native top solver or JSON
syntax, finite/regular explicit-top theorem or other-signature theorem.

## Preserved sources and review

- Hardness source: `371b97c40d532f076fbe09fc640db9333734c91c`, three paths.
- Explicit-top source: `0eff4818d990821fd1c08f704a2392f2d0047cf5`, four preserved
  proof/note/Python/result paths. Its isolated workflow is replaced deliberately.
- Each source head is retained as ancestry by a clean merge. The
  [receipt](../results/hardness-top-integration-20260920.json) records byte-for-byte
  comparisons and SHA-256 identities. No author branch was rewritten.
- The prior [independent submission review](2026-09-20-submission-review.md) at
  `2ffdbd8384f5d98aa257d476c1901cfc3deddd8f` accepted both arguments. Its HR98
  primary-source gate inspected rendered published pages 621–623, identifying
  binary CLOSED-UNIV hardness, the original top-valued negative case and the
  separate finite truncation. This is reused provenance, not a fresh literature
  search or a transfer of HR98's finite theorem.

Two separate read-only reviewers then read the actual new manuscript. The
hardness review covered all valuations, epsilon edges, regular graph construction,
always-satisfiable input, logspace output and the finite boundary. The top review
covered labelled-tree identification/order, shared names, both universal lifts,
product-root exclusion, vacuity, same-observation words and four-call termination.
Both accepted within these exact scopes. They inherited the submitted arguments;
this was mathematical readback, not a blind rediscovery or human peer review.
Minor presentation changes make the reduction equivalence, worked example,
source locator and formalization boundary explicit.

The paper now includes Theorem 12.3 and full Section 14, retaining the earlier
terminal and finite-tree exposition. Its map has 23 checked entries and seven
ordinary-proof records. The new source pin supplements the existing C081/C085
pins; it does not silently repin old modules. The novelty matrix distinguishes
the inherited Henglein–Rehof source hardness from the new exact-domain transfer.
It makes no publication-priority claim.

## Continuing checks and fresh evidence

The optional top module imports only Std. `scripts/check_explicit_top.py`
explicitly builds it, replays it through `leanchecker`, audits all 29 explicit
declarations and reruns both independent finite corpora. Non-theorem definitions
must not depend on Classical.choice; theorem proofs may use the usual logical
axioms but no custom/native/sorry axiom. An independent CI review identified
that an unused custom axiom could escape a selected-declaration audit. The gate
now rejects custom axioms, opaque declarations and placeholders before inventory
checking; five focused tests include unused/private negative controls.

Main/PR Lean CI runs the gate on changes to Lean, both scripts, the shared audit
helper, experiments, receipts or the workflow. Its artifact upload preserves
receipts and logs. The former branch-specific workflow is removed; the default
proof import graph and production solver are unchanged. Research checks already
runs on every main/PR change, including documentation, and checks the paper
against each immutable source pin. A paper-only edit does not trigger expensive
Lean validation or establish its ordinary mathematics automatically.

A fresh isolated Linux aarch64 checkout, with an empty project `.lake` and the
installed Lean 4.33.1/Python 3.13.14 toolchains, checked combined revision
`cdf22547a2a1dbd45ff296048e130ed4380d95de`:

| Command | Result | Seconds |
|---|---|---:|
| `python3 scripts/check_explicit_top.py` | PASS: build, kernel, 29 declarations, E063/E064 | 5.028 |
| `python3 scripts/test_check_original_bounds.py` | PASS: five audit-helper tests | 0.165 |
| `python3 scripts/check_original_bounds.py` | PASS: combined original-U/F proof and corpora | 62.306 |
| `python3 scripts/check_lean.py` | PASS: default build/kernel/axioms and Python agreement | 172.798 |

These checks reused the installed pinned toolchain, not a fresh operating system.
The two corpora matched the original semantic receipts exactly; only Python,
platform and (for hardness) machine metadata were ignored. E063 checks 4,504 NFAs
and 33,447 premise comparisons. E064 checks 393 systems and 5,156 lifted models;
its 217 absent bounded paired witnesses remain UNKNOWN. Failed naive encodings
remain preserved counterexamples. Neither corpus is an all-input proof or a
C081 backend execution.

The final hardened checker is rerun at its own pinned revision; the machine
receipt records that result separately. Unchanged-core checks above retain their
actual revision. Final organization, source-map, PDF and publication readbacks
are appended below rather than relabeling older evidence.

## Handoff and limits

#70 remains open for sharper upper bounds and exact complexity. #71's complete
ordinary theorem and selective-formalization milestone is complete. A full
explicit-top expression formalization, executable frontend and countermodel
output are separate unassigned follow-ups. The reviewed #68 producer core,
#72 arity/automata and #74 variance work still await their own integration;
#67's later native handoff needs its own review. No path is reserved for that
later work by this session.

No source papers, author names, license choices, earlier receipts, proof
interfaces or production solver were changed. Author workspaces, unpushed work
and stashes were not inspected or deleted. The final main readback in #37/#70/#71
records publication and explicitly releases this integration lease.
