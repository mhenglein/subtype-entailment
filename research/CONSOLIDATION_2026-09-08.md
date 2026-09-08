# Research consolidation — 2026-09-08

This is the supplemental canonical ledger for the controlled integration of reviewed PRs #6–#14 onto main `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Evidence rule.** Entries below preserve their stated branch evidence levels. `WRITTEN PROOF + REPRO` does not mean Lean-checked or independently refereed. Unrestricted Problem 1.7 remains open.

Current main remains authoritative for earlier C001–C045/E001–E028 records and approach history. The historical proof texts imported here sometimes used provisional IDs on separate branches; those provisional labels are not globally meaningful. This ledger gives the collision-free canonical IDs used after consolidation.

## Canonical claims

<a id="c046"></a>
### C046 — Exact modular synchronization and terminal budget lower family

**Statement.** For periods `p_1,...,p_r`, an explicit flat binary terminal instance has witness language exactly `(1^N0)^r` for positive multiples `N` of `lcm(p_i)`, exact instance budget `(r-1)(lcm(p_i)+1)`, and unique shortest witness `(1^P0)^r`. The eight-state `(2,3)` instance has budget 7, refuting Q002 and Q003 at `k-2=6`. Periods `1,...,m` give budget `2^(Omega(sqrt(k)))`, ruling out every polynomial state-count terminal budget bound.

**Status / scope.** `WRITTEN PROOF + REPRO`; terminal BorderAvoid, with C030 supplying the recorded normalized subtype transfer. No unrestricted decision or undecidability result.

**Record.** [Proof](../notes/2026-09-05-modular-synchronization.md), [checker](../experiments/check_modular_sync.py), [Q002](conjectures/Q002.md), [Q003](conjectures/Q003.md).

<a id="c047"></a>
### C047 — No constant simultaneous-loop-deletion bound

**Statement.** In the all-period-one specialization with `r` unary blocks, a strictly shorter profile-dominated accepted replacement can require edits in all `r` blocks. Hence no constant number of simultaneous equal-state loop deletions suffices independent of state count.

**Status / scope.** `WRITTEN PROOF + REPRO`; this does not rule out a computable state-dependent deletion bound.

**Record.** [Proof](../notes/2026-09-05-modular-synchronization.md), [checker](../experiments/check_modular_sync.py).

<a id="c048"></a>
### C048 — Direct binary whole-word synchronization

**Statement.** A supplied tuple of binary DFAs can be compiled in polynomial size to a binary terminal BorderAvoid instance whose witnesses are exactly repeated encodings of one common word accepted by every DFA. Product reachability exactly decides this constructed subclass.

**Status / scope.** `WRITTEN PROOF + REPRO`; construction-specific, not a decomposition theorem for arbitrary BorderAvoid instances.

**Record.** [Implementation](../experiments/word_sync.py), [checker](../experiments/check_word_sync.py).

<a id="c049"></a>
### C049 — Fragment-specific PSPACE hardness

**Statement.** DFA intersection nonemptiness reduces through C048 and the recorded terminal realization C030 to non-entailment over the top-free bottom/product subtype fragment; by complement closure the corresponding entailment problem is PSPACE-hard as well.

**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted PSPACE upper bound follows.

**Record.** [Compiler/checker](../experiments/word_sync.py), [reproduction](../experiments/check_word_sync.py).

<a id="c050"></a>
### C050 — Fixed-word skeleton and concatenation-description lower bound

**Statement.** A polynomial-size family of DFAs has singleton intersection equal to a binary counting word with exponentially many distinct factors. The synchronized unique witness therefore forces superpolynomial body size for the stated fixed-word power skeletons and ordinary concatenation straight-line descriptions.

**Status / scope.** `WRITTEN PROOF + REPRO`; richer shared-word/regular-constraint representations are not excluded.

**Record.** [Counting construction](../experiments/counter_intersection.py), [checker](../experiments/check_word_sync.py).

<a id="c051"></a>
### C051 — Every finite Necessary budget can miss a fixed NO instance

**Statement.** A five-state flat terminal instance has empty witness language, yet for every finite `L,D` its `Necessary(L,D)` language is nonempty. The family `1^n 0 1^(n+1) 0` has exactly one violation with suffix length `n+1` and gap `n+2`.

**Status / scope.** `WRITTEN PROOF + REPRO`; refutes completeness of the negative semiprocedure that waits for finite Necessary-language emptiness, not the soundness of any individual certificate.

**Record.** [Proof](../notes/2026-09-06-delimited-convolution.md), [checker](../experiments/check_delimited_blocks.py).

<a id="c052"></a>
### C052 — Exact arbitrary-flag bounded delimited schemas

**Statement.** For a supplied finite sequence of regular data stages separated by a logical delimiter, arbitrary logical flags and Bad annotations are decidable exactly by a finite reverse padded-convolution machine with persistent equality/hit bits and delayed whole-block context guards. The supplied-schema problem is PSPACE-complete.

**Status / scope.** `WRITTEN PROOF + REPRO`; this is not a finite-cover theorem for arbitrary raw instances.

**Record.** [Proof](../notes/2026-09-06-delimited-convolution.md), [solver](../experiments/delimited_blocks.py), [checker](../experiments/check_delimited_blocks.py).

<a id="c053"></a>
### C053 — Exact bounded-marker raw-input certificate

**Statement.** A raw binary terminal instance is decided exactly when it satisfies the verified paired/unary token format, annotation-alignment conditions, and has no productive marker cycle in the certified macro graph. The front end derives a finite complete schema cover without inserting a delimiter.

**Status / scope.** `WRITTEN PROOF + REPRO`; unsupported formats/cycles/caps remain `UNKNOWN`.

**Record.** [Proof](../notes/2026-09-06-delimited-convolution.md), [certificate](../experiments/marker_certificate.py), [checker](../experiments/check_marker_certificate.py).

<a id="c054"></a>
### C054 — Fixed-reference target-free prefix normalization

**Statement.** Relative to one actual reference suffix containing all relevant targets, earlier target-free blocks can be pumped by a finite `(macro state, pending-context)` monitor while preserving the same reference suffix and witnesshood.

**Status / scope.** `WRITTEN PROOF + REPRO`; G-specific witness preservation, not unconditional full-profile descent.

**Record.** [Proof](../notes/2026-09-06-target-frontier.md), [implementation](../experiments/target_frontier.py).

<a id="c055"></a>
### C055 — Common-reference powerset/convolution solver

**Statement.** Unknown reference words can be chosen consistently by one reverse convolution while a powerset tracks all possible earlier-block observations relative to that same tuple. Longer unmatched source prefixes reduce to finite reverse reachability after the references end.

**Status / scope.** `WRITTEN PROOF + REPRO`; exact for a supplied target-frontier schema, not unrestricted BorderAvoid.

**Record.** [Proof](../notes/2026-09-06-target-frontier.md), [implementation](../experiments/target_frontier.py), [checker](../experiments/check_target_frontier.py).

<a id="c056"></a>
### C056 — Exact target-frontier class with unbounded early marker cycles

**Statement.** In the verified marker formats, arbitrarily many productive marker cycles may occur before relevant targets. If no productive marker cycle is reachable from a relevant target, a finite first-target reference cover plus C055 decides the raw slice exactly.

**Status / scope.** `WRITTEN PROOF + REPRO`; target-reachable marker cycles remain outside this certificate.

**Record.** [Proof](../notes/2026-09-06-target-frontier.md), [implementation](../experiments/target_frontier.py), [checker](../experiments/check_target_frontier.py).

<a id="c057"></a>
### C057 — Universal terminal maximal-run normalization

**Statement.** Every defined binary word ending at a terminal accepting state has a no-longer word with the same maximal-run letters, run-boundary states, visited-state set, and complete suffix-agreement profile, with run magnitudes effectively bounded as a function of state count and supplied run count.

**Status / scope.** `WRITTEN PROOF + REPRO`; no unrestricted bound on the number of runs is proved.

**Record.** [Integrated proof record](../notes/2026-09-06-run-normalization.md), [normalizer](../experiments/run_normalization.py).

<a id="c058"></a>
### C058 — Supplied maximal-run witness existence is NP-complete

**Statement.** With a maximal-run bound `R` supplied in unary, terminal witness existence is NP-complete. Fixed `R` admits exact finite polynomial enumeration with `R`-dependent degree. Executable bounded negatives are `NO_WITHIN_RUN_BOUND`, never unrestricted `NO`.

**Status / scope.** `WRITTEN PROOF + REPRO`; the missing unrestricted run-count bound remains explicit.

**Record.** [Integrated proof record](../notes/2026-09-06-run-normalization.md), [solver](../experiments/run_bound_decision.py), [checker](../experiments/check_run_normalization.py).

<a id="c059"></a>
### C059 — Target-local finite pending-context pump

**Statement.** When every effective flag target has finite marker distance `h` to the selected terminal final, protecting the final `h` blocks and pumping repeated `(macro state, pending-context)` memories yields an existence-preserving marker bound and an exact finite-schema decision for the certified class.

**Status / scope.** `WRITTEN PROOF + REPRO`; missing format, target-reachable marker cycles, and caps remain `UNKNOWN`.

**Record.** [Integrated proof record](../notes/2026-09-06-target-local-pumping.md), [implementation](../experiments/target_tail.py), [checker](../experiments/check_target_tail.py).

## Canonical experiments

<a id="e029"></a>
### E029 — Alternative terminal-copy synchronization regression

**Command.** `python3 experiments/check_terminal_copy.py`

**Evidence / scope.** Independent implementation and tests for the modular/copy reductions retained as differential evidence. It is not a second canonical claim numbering and does not decide arbitrary BorderAvoid.

<a id="e031"></a>
### E031 — Modular synchronization regression

**Command.** `python3 experiments/check_modular_sync.py`

**Evidence / scope.** Exhausts the concrete eight-state separating range and lower budget graphs, tests modular families, subtype transfer fixtures, complete profiles, and simultaneous-deletion examples. All-length conclusions use C046/C047's written proofs.

<a id="e032"></a>
### E032 — Whole-word synchronization and counting regression

**Command.** `python3 experiments/check_word_sync.py`

**Evidence / scope.** Exhaustive two-state DFA-pair intersections, random supplied products, binary parsing/witness comparisons, subtype fixtures, and the counting construction. Construction-specific only.

<a id="e033"></a>
### E033 — Delimited convolution and Necessary-hierarchy regression

**Command.** `python3 experiments/check_delimited_blocks.py`

**Evidence / scope.** Complete finite-language oracles, cyclic supplied-schema checks, delayed-guard fixtures, independent synchronization comparisons, and the five-state Necessary-budget obstruction.

<a id="e034"></a>
### E034 — Raw marker-certificate regression

**Command.** `python3 experiments/check_marker_certificate.py`

**Evidence / scope.** Complete acyclic raw-language oracles, cyclic supplied-schema/product comparisons, the five-state NO input, explicit unsupported-format/cycle guards, and cap-to-UNKNOWN behavior.

<a id="e035"></a>
### E035 — Target-frontier regression

**Command.** `python3 experiments/check_target_frontier.py`

**Evidence / scope.** Complete acyclic raw oracles, prior-schema differential checks, cyclic-prefix relations, source-observation set comparisons, normalization fixtures, and explicit caps/unsupported inputs.

<a id="e036"></a>
### E036 — Target-local pending-context regression

**Command.** `python3 experiments/check_target_tail.py`

**Evidence / scope.** Complete acyclic oracles, a cyclic family with independent existence oracle, known-witness pumping, pending-context deletion counterexample, subtype checks, and unsupported/cap guards.

<a id="e037"></a>
### E037 — Terminal maximal-run normalization regression

**Command.** `python3 experiments/check_run_normalization.py`

**Evidence / scope.** Symbolic/direct/reversed profile comparisons, exhaustive small tables, finite unary transformations, huge encoded counts, bounded-run complete finite oracles, and unary-intersection compilation. Quantified claims rest on C057/C058's written proof.

## Held back after review

### PR #12 — broader run-profile normalization

Scientifically distinct, but its reviewed `join_runs` helper consumes a one-shot iterable during validation and then silently produces an empty result. The central theorem's tuple-based internal callers are not thereby falsified. Repair the API, add list/tuple/generator parity tests, and reconcile its marker-count notation before integration.

### PR #14 — regular-family verification / shared-lasso continuation

The shared-orbit backend reproduced 43,069 exact backend agreements, but the reviewed head is held because its accompanying proof/publication layer needs: an explicit boundary-safe hypothesis for the minimum-violation Presburger theorem (or revised cost definition); removal of a nonterminal C021 inference from a terminal question; an all-bad-word argument for the one-flag global-minimum conclusion; deterministic result publication and CI wiring; and traceable proof/citation expansion. These issues do not establish unsoundness of the orbit implementation and do not decide Problem 1.7.

## Frontier

Large arithmetic exponents are manageable once a finite synchronization schema is known. The remaining general obligation is an effective, existence-preserving control of arbitrary nonflat recurrent structure: a computable essential-run/schema bound, a finite symbolic cover, another terminating exact procedure, or a genuine undecidability reduction for the normalized subtype fragment.
