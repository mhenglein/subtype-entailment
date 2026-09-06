# Universal run normalization and target-local pumping

Date: 2026-09-06. Parent checkpoint PR #9 (`df54d87`).
**Proposed C054-C056, E035-E036: written proofs and reproduction; independent
review pending; not Lean-checked. No unrestricted Problem 1.7 solution.**

<a id="c054"></a>
## C054 - Exact profile-preserving terminal run normalization

For any accepted word of any k-state binary terminal DFA, write r for its
number of maximal homogeneous runs. A common count-gap transformation
produces a no-longer word with the same r runs, the same run-boundary states,
the same visited-state set, and exactly the same full suffix-agreement profile.
Its length is at most r^2((k+1)^2+P), where P is the larger least common
multiple of the one-letter transition-cycle lengths and P<=k!. Run counts
are handled in binary; the profile and normalization algorithms do not expand
them. Thus arbitrary flags and Bad annotations are preserved.

This applies without a marker assumption. It bounds run lengths given r,
NOT r itself. Independent compression of each long count by its residue is
false; compression of the common ordered GAP list is the proved operation.

<a id="c055"></a>
## C055 - The supplied run-bounded decision is NP-complete

With R encoded in unary, existence of a terminal witness with at most R
maximal runs is NP-complete. Membership uses C054 and the polynomial symbolic
profile checker. Hardness uses positive unary-DFA intersection and an explicit
synchronization construction with exactly 2r runs. The implementation returns
NO_WITHIN_RUN_BOUND after complete finite exhaustion; that is NOT unrestricted
NO. Caps return UNKNOWN. C050's counting family already requires
(d+1)(d*2^d+2) runs, excluding polynomial bounds in the state count.

[Full C054-C055 proofs](../notes/2026-09-06-run-normalization.md).

<a id="c056"></a>
## C056 - Marker cycles before targets can be pumped safely

After the existing format and boundary checks, suppose no productive marker
cycle is reachable FROM an effective flag target. Let h be the maximum
number of markers on a target-to-final path and K the macro-state count.
Unbounded marker cycles BEFORE targets are allowed. Protect the final h
blocks of a witness and track pending whole-block equality guards while
reading its prefix. The combined state has at most K*2^(h-1) possibilities.
Deleting repeated combined states gives a witness with at most
h+K*2^(h-1) markers. A bounded complete C052 schema search now decides this
strictly larger, automatically recognizable class. No markers are inserted.

Original state repetition alone is insufficient: an explicit equal-state
block deletion creates a new violation. The pending-context bits distinguish
that unsafe join. The pump preserves the supplied G's witnesses, not the
entire agreement profile. Cycles reachable from targets still give UNKNOWN.

[Full C056 proof](../notes/2026-09-06-target-local-pumping.md).

<a id="e035"></a>
## E035 - Run normalization and symbolic profiles

`python3 experiments/check_run_normalization.py`

[Implementation](../experiments/run_normalization.py),
[bounded-run solver](../experiments/run_bound_decision.py),
[result](../results/run-normalization.json).

All 256 partial three-state terminal tables; 288 complete unary transformations
through four states; 135,535 gap and 26,136 tail-trace checks; 344 expanded long
words; 216 huge encoded words; 480 complete bounded-run oracles; 1,296 unary
DFA pairs and 20,736 block tuples; two canonical models; deliberate cap and
iterator guards. Huge-count checks are symbolic, not hidden expansion.

<a id="e036"></a>
## E036 - Target-local certificate and pending-context pumping

`python3 experiments/check_target_tail.py`

[Implementation](../experiments/target_tail.py),
[result](../results/target-tail.json).

120 complete acyclic oracles (63 YES, 57 NO); all 256 eligible flag subsets
of a cyclic-prefix family (32 YES, 224 NO); 3,072 extra-prefix profile checks;
140 strict witness-preserving pumps; 25 completed known-positive decisions;
six canonical model checks; four unsupported guards and a deliberate cap.
The previous certificate returns UNKNOWN on explicit examples now decided
both YES and NO. Proofs, not these finite counts, justify completeness.

## Remaining target and literature boundary

A general computable bound on required run count is still missing. So is a
complete treatment of productive marker cycles reachable from flag targets.
The new [literature scope check](../notes/2026-09-06-string-theory-boundary.md)
records why the single negated-containment theorem cannot simply be applied
to all state-typed internal suffix conditions. No unrestricted conclusion
is inferred from bounded-run or failed-certificate output.
