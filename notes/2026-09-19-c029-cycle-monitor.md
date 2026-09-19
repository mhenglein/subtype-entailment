# C029 through bounded cycles and a reverse periodic monitor

Current-status update: the monitor language equivalence, finite search and
concrete periodic-trace obligations left open in this historical checkpoint
are now discharged by the [complete C029 Lean decision](2026-09-19-c029-completion.md).
The original outline, failed shortcuts and recorded evidence below are preserved.

Date / author: 2026-09-19, Codex Astra c029-cycle-monitor-20260919.
Workstreams A013/A018; C029; issues #31/#34/#37.
Base: 064fc7306b679bf607b91e7d8de259823f200c62.
Status: ordinary proof with independent source readback and kernel-checked
components. The complete executable C029 theorem remains unformalized.
The initial outline below was written before implementation.

## Exact target

For every finite binary Instance I satisfying AbsorbingTerminal.Absorbing,
construct an executable Bool infiniteWitnessCheck I and prove it is true iff
AbsorbingTerminal.InfWitness I. InfWitness uses the unchanged original Witness,
a safe finite stem and a nonempty safe cycle. Arbitrary pre-final loops, Bad
states, diagonal flags and the empty word remain in scope. This is only the
infinite-safe-continuation branch of normalized subtype non-entailment; the
terminal branch is already checked. Finite expression normalization and the
stronger quantitative U/F claim are separate.

## Proposed simplification and complete route

1. Extend any InfWitness safely to the base q of a nonempty safe cycle c with
   length at most k and empty incoming flag column. The witness prefix may
   be arbitrarily long. A k-letter safe path has repeated cuts; a positive
   extension from a final enters the zero-column region. This is the bounded
   cycle obligation, being formalized separately in InfiniteCycle.lean.
2. Enumerate all q and all nonempty binary c of length at most k, retaining
   exactly safe cycles from q to q with q final and empty incoming column.
   Every retained repeated cycle remains safe/final/zero by absorption.
3. For each retained (q,c), decide whether there is a safe word v from the
   original initial state to q for which the infinite word v c^omega has no
   equal suffixes at an ordered flagged pair of prefix cuts. Only prefix cuts
   can be flagged; all later target columns are empty. This is the monitor
   obligation. It quantifies over all v via finite reachability, not a cutoff.
4. Such a prefix and cycle yield a finite witness: there are only finitely
   many prefix cut pairs, each has a finite mismatch; take the maximum of
   those positions along the safe periodic continuation. Conversely an
   original witness already has a finite mismatch for every flagged pair,
   which safe extension cannot undo. This is the finite extraction obligation.
5. Combine finite enumeration, exact finite graph reachability, the bounded
   cycle theorem and finite extraction. No branching or nonpure-lasso case
   is needed for this existential route: extend the witness before selecting
   the bounded cycle. This simplification does not preserve arbitrary prefixes
   or all safe infinite tails and does not claim to do so.

## Reverse monitor construction (Lean invariant still open)

Let d=length(c)>0. A phase z in {0,...,d-1} denotes c rotated left by z.
Two phases are equivalent iff their rotations agree at all d positions.
This works for nonprimitive periods. Monitor nodes contain current original
state, phase, a Boolean recording whether the scanned suffix still matches
its aligned periodic template, and d sets of later cut states.

Start at q, phase 0, matching true, with q in bucket 0. Reject unsafe states.
Traverse original edges backwards: choose a predecessor p and letter a with
step(I,p,a)=current. Decrement phase modulo d. If still matching and a is the
expected c letter at the new phase, reject when p flags a state in any bucket
with an equivalent phase, then add p to its bucket. At the first mismatch,
switch matching off permanently; all earlier suffixes are nonperiodic and
cannot equal a later suffix. Continue checking safe reverse edges, but no
further comparison memory is needed. Accept at the original initial state.
The graph is finite (at most 2*k*d*2^(k*d) raw nodes), with explicit finite
state sets/edges; undefined or unsafe edges are absent. Reachability must be
exact, with a cap returning UNKNOWN if used in experiments.

Invariant: buckets record exactly the original states at later cuts within
the final matching segment, separated by phase; ordering is preserved because
new predecessors are tested as flag sources and stored cuts as targets.
No flag conflicts may occur among those cuts. Diagonal safety is checked
separately. Endpoint and later columns are empty, including boundary pairs.
A mismatch never repairs an existing equality between later suffixes; hence
rejecting a conflict before a later reverse mismatch is sound.

The key stream lemma says: if stream s eventually agrees with d-periodic r,
then for i<j, equal suffixes of s at i,j are equivalent to s agreeing with r
from i onward and r having equal rotations there. This is the PeriodicTail
obligation, under independent formalization. It avoids claiming d is primitive.

## Falsification and remaining proof obligations

Test the monitor against direct eventual-suffix equality over a finite prefix
and complete periodic remainder, including nonprimitive cycles, different
phases with identical rotations, reversed flag direction, initial/endpoint
cuts, unsafe states, repeated pre-final states and positive cycles. Compare the
new cycle-only decision with the preserved Python C029 implementation, and
validate every returned word with the independent literal Witness predicate.
Finite comparisons are evidence only. Audit the stream lemma, monitor invariant,
finite reachability and finite extraction separately before marking C029 Lean.

If this monitor fails, first distinguish a faulty rotation invariant from a
failure of the weaker existence route. A failure does not establish
undecidability. Retain the older branching/primitive-monitor proof and all
historical evidence; the new route may replace formalization work, not erase it.

## Ordinary proof of the complete cycle-only decision

The bounded-cycle theorem now proves the first implication in Lean. It gives
some original witness w at a final control q with an empty incoming column,
and a safe nonempty cycle c of length d <= k at q. The witness itself may be
long; no pre-final repeated-state deletion is used. The cycle need not be
simple or primitive. There are finitely many pairs (q,c) to enumerate.

Fix one enumerated pair. For any safe prefix v of length n ending at q, let
s = v c^omega and let q_i be the control at cut i, for 0 <= i <= n. Define
Good(v,c) to mean that no i<j<=n has both flag(q_i,q_j) and equal infinite
suffixes s[i:] = s[j:]. Diagonal conflicts are already excluded by safety.
All targets after n have empty incoming columns by strong absorption. The
endpoint n is included in Good, although its incoming column is also empty.

### Exact stream criterion, including nonprimitive periods

Let r be the d-periodic stream aligned with the tail at n. If s agrees with
r after n and s[i:] = s[j:] with i<j, set g=j-i>0. Equality gives period g
from i onward. For any t>=i, the shift g*d*n reaches a point at least n and
is a multiple of both g and d. Thus s(t)=s(t+g*d*n)=r(t+g*d*n)=r(t).
The equal suffixes also imply r[i:]=r[j:]. Conversely agreement with r from
i and equal r rotations immediately imply equal s suffixes. This is exactly
PeriodicTail.eventually_sameSuffix_iff; no primitive root or Fine-Wilf transfer
is assumed. Two rotations of the supplied d-letter word agree infinitely iff
they agree at every one of its d positions, even when distinct phases coincide.

### Reverse monitor invariant and exact acceptance

At the start, only endpoint cut n has been scanned. Its phase is zero and its
state is stored in bucket zero. The endpoint is safe. While scanning left,
phase decreases modulo d, so at cut i the phase is (i-n) modulo d.

As long as all scanned letters match r, every scanned suffix is its associated
pure periodic rotation. The buckets contain precisely the states of these
cuts at each phase. Adding an earlier source cut p creates a prohibited equal
suffix pair exactly if p flags a stored later control at an equivalent phase.
The code checks the source-target order in that direction and rejects it.
Sets are sufficient: multiplicities and order among already-checked later
cuts do not change whether such a newly introduced pair exists. All diagonal
flags are excluded separately by the safe-state test.

At the first mismatching letter encountered from the right, the current
suffix no longer agrees with r. Any yet earlier suffix also contains this
mismatch. The stream criterion says none of them can equal any later suffix.
The previously checked pairs among later cuts are unchanged. Therefore the
remaining buckets and phase can be discarded, while every remaining reverse
edge still checks original transition consistency and state safety. A conflict
found before this mismatch cannot be repaired by prepending it: those later
suffixes do not change. The implementation rejects such a conflict immediately.

Induction on the scanned length now shows that an admitted reverse path has
no prohibited equal suffix pair among its processed cuts, and every safe
prefix satisfying Good admits its whole reverse path. Reaching the original
initial state is exactly acceptance of a safe prefix v satisfying Good(v,c).
This includes v=epsilon. Undefined and unsafe predecessor edges are absent.

The represented monitor nodes are (q,z,true,buckets), plus canonical
(q,0,false,empty) nodes after a mismatch. There are at most
k*d*2^(k*d)+k nodes. Edges and initial/accepting tests are effective finite
tables. Breadth-first search therefore terminates without a resource cap.
A capped run reports UNKNOWN; a NO_PREFIX result requires graph exhaustion.
This is an ordinary proof of the monitor invariant; its full Lean transfer is
still an explicit obligation, not discharged by the stream theorem alone.

### From a monitor prefix to an original finite witness

For s=v c^omega, after n comparison offsets both suffixes at any old i,j lie
in the d-periodic region. If they agree for every offset t<n+d, they agree
forever: for t>=n+d subtract d from both arguments and use strong induction.
PeriodicTail.sameSuffix_of_eventually_periodic formalizes this exact strict
horizon. Thus every flagged old pair excluded by Good has a mismatch before
n+d offsets. The explicit extension W=v c^(n+1) has
length n+d*(n+1) >= 2*n+d, since d>=1. At every old target j<=n, the finite
comparison in W tests at least n+d offsets. It therefore cannot be a flagged
agreement. All newer target columns are empty. Safety, finality and the
remaining infinite continuation follow from the original safe cycle and
absorption. Consequently W is an original Witness and ends back at q, where
c is still a safe nonempty cycle. The algorithm returns this explicit W;
it does not reconstruct it with the older active-ray implementation.

Conversely, apply the bounded-cycle theorem to any InfWitness. Every flagged
pair in its resulting witness prefix already has a finite mismatch; equal
infinite suffixes would imply the forbidden finite agreement. Its pair (q,c)
is in the enumeration, and its reverse monitor path accepts. The graph search
therefore finds some prefix. These two directions establish the ordinary
soundness/completeness argument for the new algorithm.

### Discriminating regressions and failed shortcuts

- Nonprimitive c=00 has identical phase-zero and phase-one rotations. In a
  path 0->1->2 with flag(0,1), prefix 00 must be rejected; comparing only equal
  phase numbers would incorrectly accept it. The new monitor checks rotation
  equality across phases. The old forward monitor remains valid because it
  first replaces the supplied period by its primitive root.
- Reversing the flag direction changes this result. The exact ordered guard
  with flag(1,0) accepts that same prefix; this is an orientation regression.
- For prefix 100 and a flag between the two zero-suffix source controls, the
  leftmost mismatch cannot repair the later equality. Reverse rejection must
  persist, unlike a forward monitor's reset when extending on the right.
- In the three-state instance 0--0->1, 1--1->1, 1--0->2, 2--0->2, final {2}
  and flag(0,1), shortest safe entry 00 fails but 010 succeeds as a monitor
  prefix; 010 itself is not a witness, while 0100 is. This guards arbitrary
  pre-final loops and the distinction between accepted prefix and witness.
- In 0--0->1--0->2, with a zero loop at 2 and a one edge to terminal final 3,
  finals {2,3} and flag(0,1), 001 is a terminal witness but no infinitely
  continuable witness exists. A reachable cycle or an arbitrary branching
  certificate must not be confused with C029 acceptance.

Existing algorithms and historical proof notes are unchanged. The new route
removes whole case splits by changing where the existential prefix is chosen;
it does not justify a stronger theorem about every supplied prefix or lasso.

## Checked boundary, validation and provenance

Source checkpoint: 2a10fbdb9b80182fdbc1927a9a6c12fefabbaa61, based on current
main e1e8f635f0374d5c8112c8ee25c4220fc10198be after its disjoint literature
merge. No existing proof, definition, toolchain or literature file changed.
The three modules are in the default import graph. No C029 Boolean checker
exists in Lean yet; InfiniteWitness.lean deliberately proves the finite
extraction implication with its exact no-conflict trace hypothesis exposed.

The bounded-cycle worker source is unchanged from
36548917f7afc1842793591e496abac33311e29d (integrated as 6e5cef2).
Its initially reported eight-character suffix was mistyped; parent read back
the remote reference, corrected the failed cherry-pick and integrated the
verified commit. The correction is preserved in #31. PeriodicTail is unchanged
from bfc19b5e1ee19348053dbd20ca12e0795d036573 (integrated as 2229a31).

The final extraction contract is
`infWitness_of_absorbing_periodic_trace`: given the original deterministic
Trace, all safe controls, finality at N, positive eventual letter period d,
and no flagged equal infinite suffixes among i<j<=N, it yields the unchanged
InfWitness. `witness_of_periodic_noConflict` supplies the explicit prefix of
length 2*N+d. `trace_final_after` and `trace_emptyIncoming_after` derive all
later final/empty-column facts from Absorbing; they are not left as unchecked
facts about repeating a cycle. This is not a bound on the still-unbounded N.

Commands run on wb-marcus with Lean 4.33.1 and the pinned project environment:

```sh
source /home/marcus/.local/share/subtail/env.sh
(cd lean && lake build Subtail.PeriodicTail Subtail.InfiniteCycle Subtail.InfiniteWitness)
python3 scripts/check_lean.py
python3 scripts/check_infinite_witness.py --output tmp/c029/dependencies.json
(cd lean && lake env leanchecker Subtail.InfiniteCycle Subtail.InfiniteWitness)
python3 experiments/check_infinite_cycle_monitor.py
python3 experiments/run_experiments.py
python3 scripts/research_index.py --check
python3 scripts/test_research_index.py
python3 notes/prior-work/search.py --check
python3 notes/prior-work/test_search.py
```

The component build, full default build/kernel/core check, 33 complete new
declaration dependency audits, standalone kernel replay, both Python suites,
canonical index, 13 navigation tests, unified retrieval references and nine
retrieval tests passed. Existing saved core results were byte-identical.
Runtime declarations have no Classical.choice; standard proof axioms remain
explicit. No arbitrary bound, classical Decidable instance or missing proof
was substituted for C029. The workflow includes both new checks and triggers
on the audit script, experimental files and Lean modules. Combined source
hashes are listed below; final documentation/index checks belong to the later
record commit, not a claim of a second proof build.

Real remote Lean MCP checks on InfiniteWitness.lean returned no diagnostics,
failed dependencies or timeout (1.339 seconds). `lean_goal` at line 239 returned
the precise `InfWitness I` goal with Absorbing, Trace, periodicity, safety,
finality and hno hypotheses (0.024 seconds). This tests live source inspection;
it is not a throughput benchmark or a host reboot/persistence test.

Separate reviewers checked the complete ordinary reverse-monitor argument,
the Python implementation and the final theorem source. The stream author
reviewed the other worker's cycle theorem and the root's extraction theorem;
the cycle author reviewed the root's monitor. They inherited the route context,
so these are independent source readbacks, not blind derivations or external
human review. Neither found a defect. Additional ephemeral exhaustive monitor
checks were reported separately in #31, including a script preserved in the
[final readback](https://github.com/mhenglein/subtail/issues/31#issuecomment-5742565372).
They are not counted as repository CI or combined with the committed corpus.

## Exact next task and release contract

The remaining C029 work is substantive: define the finite reverse monitor in
Lean and prove its buckets/order/mismatch invariant; prove its total finite
reachability check accepts exactly the safe prefixes satisfying Good(v,c);
construct the concrete periodic word/control trace for a safe prefix and
cycle; then combine both implications with infWitness_iff_bounded_cycle and
infWitness_of_absorbing_periodic_trace. Enumerate exactly the finite binary
cycles of positive length at most k. The final theorem must be
`Absorbing I -> (infiniteWitnessCheck I = true iff InfWitness I)` with no
unproved monitor, graph completeness or witness-bound premise.

After that, assemble the existing exact subtype split and address finite
compound syntax normalization. No new worker is reserved by this note. C029
retains its ordinary-proof status with explicitly checked components, C080
retains its stronger candidate status, and Problem 1.7 is not marked solved.
Publication and final source/path release are recorded in #31/#37 with the
exact main revision and CI readback. The source branches are preserved.

### Source SHA-256 values at the checked checkpoint

- lean/Subtail/PeriodicTail.lean: `1243dc455f48858d1dc30e1543cdc3737e6078aa51f7cc2f761e8af67741b148`
- lean/Subtail/InfiniteCycle.lean: `0a3559e3b09dc9a3a1d2ce80893fc354bd6aec7f2ab0a12b82fe9917fb4e2fb3`
- lean/Subtail/InfiniteWitness.lean: `778759b132b97fd0e8546a2ad0346b1e977e0cbf34423f69f0e04170f7624fdc`
- experiments/infinite_cycle_monitor.py: `bbf6d81f8a90d440fab03581dc044eb1e5736e33ff8f940ba460ca94b25eb5b7`
- experiments/check_infinite_cycle_monitor.py: `a68de5d810d439e9f11829655ba43f2b0bfb0d283f68df22095d744e2ed76d9f`
- scripts/check_infinite_witness.py: `4e464d401cc2c770991439865052b0a5419d5564e37b10f580bceb91d6d05cf6`
