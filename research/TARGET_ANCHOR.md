# Last-target anchoring: native decision and sparse certificates

Date: 2026-09-13. Base: `c4f7e56665828710b3bda77e32bb2904ad4006d6`.
Workstream A017; relevant to A008 and Q004. C077-C078 / E050.

**Written proof + reproducible finite checks. Independent mathematical review
pending; not Lean-checked. The unrestricted subtype problem remains unresolved.**

[Complete proof, algorithm, scope and dependencies](../notes/2026-09-13-target-anchoring.md).
[Initial route and recorded outcome](../notes/2026-09-13-target-anchor-route.md).
The main addition is a native complete algorithm and a proved quadratic witness
bound for a class allowing several recurrent sources AND targets. The optional
single-not-contains formulation is not an unimplemented decision oracle: the
native solver uses only finite graph searches and explicit pattern avoidance.
Last-aligned synchronization and terminal periodicity build on prior C036-C038
and the September 8 synchronized-tail work, with their prior evidence levels.

## Claims

<a id="c077"></a>

### C077 — Last-target collapse and a quadratic native decision

**Statement.** In a normalized k-state terminal slice with sole final f and
flags exactly `{(p,t):t in T, p!=t, p!=f}`, an accepted word is a witness iff it
avoids T or the suffix at its LAST T cut has no earlier occurrence. Existence
is decidable natively. Every positive slice has a witness of length at most
`k^2+k-2` for k>=2; k=1 is direct. Existence for this class has an NP upper bound.
No sharpness or hardness statement is made.

**Proof mechanism.** For each t consider all accepting tails with no positive
T cut. A productive cycle gives arbitrary tail length. With a shortest prefix
X of length m<=k-1, a tail of length between k*m and k*m+k-1 cannot occur earlier:
that would impose a period d<=m on a terminal accepted word of length >=k*d.
If the tail language is finite, its productive graph is acyclic and every tail
has length <=k-1. For each tail Y, exhaust the finite product of the original
DFA and the Y-pattern-avoidance DFA, checking Y absent from X Y[:-1].

**General positive corollary.** Unique last-target suffixes suffice for arbitrary
G. A productive target-free accepting tail after any reachable target therefore
supplies an original witness with the same quadratic bound even without the
complete-column or coloring hypothesis. Failure of this test is UNKNOWN.

**Evidence and limits.** [Proof Sections 2-4](../notes/2026-09-13-target-anchoring.md),
[native implementation](../experiments/target_anchor.py), E050.
Written proof, not Lean or independent mathematical review. Finite-tail cases
overlap C037; no claim of separation from every previous solver. This is not a
polynomial bound for unrestricted witnesses or C075 scheme cost. The current
implementation may store exponentially many finite tails.

<a id="c078"></a>

### C078 — Static transition coloring certifies sparse target completion

**Statement.** Build the finest transition coloring preserving every path in
the productive last-aligned comparison graph. Colors retain their original
letters. If the colored synchronized graph has no entirely unflagged path
from an ordered target-root pair to a terminal endpoint, completing target
columns preserves witnesshood. C077 then decides the slice. State count and
word length are unchanged, giving the same original quadratic witness bound.
The sufficient certificate is polynomial-time to construct and check.

**Proof mechanism.** Colored comparisons decode to raw comparisons; a raw bad
word retains a last-aligned violation. A new complete-column comparison is
already G-bad at its root or at an aligned descendant; otherwise it contradicts
the certificate's exhausted graph. Words and state runs are shared throughout.

**Scope.** Multiple recurrent sources/targets and nonflat graphs are allowed.
Boundary slices handle Bad, diagonal/empty flags and multiple finals. A failed
certificate is UNKNOWN, not NO. The raw (2,3) modular positive instance and the
six-state marking-barrier NO instance both fail it. No complete finite-history
cover, automatic general reduction or unrestricted NP membership is implied.
The internal colored alphabet changes no subtype constructor.

**Evidence.** [Proof Section 5 and failures](../notes/2026-09-13-target-anchoring.md),
[implementation](../experiments/target_anchor.py), E050.
Written proof + differential checks; independent review pending, not Lean.

## Experiment

<a id="e050"></a>

### E050 — Target anchoring, native solutions and negative-certificate replay

**Commands.**

```sh
python3 experiments/check_target_anchor.py --output /tmp/target-anchor.json --full-output /tmp/target-anchor-full.json
cmp results/target-anchor.json /tmp/target-anchor.json
python3 experiments/target_anchor.py --fixture recurrent_yes
python3 experiments/target_anchor.py --fixture recurrent_no --certificate-output /tmp/target-anchor-no.json
python3 experiments/target_anchor.py --fixture sparse_cycle_yes
python3 experiments/target_anchor.py --fixture modular_positive_unknown
```

[Checker and independent literal negative replay](../experiments/check_target_anchor.py),
[compact results](../results/target-anchor.json). Full colored tables, original
inputs, witnesses and finite negative proofs regenerate with `--full-output`.
No network, chat attachment, SMT solver or third-party package is required.

**Coverage.** All 1,024 partial three-state terminal table/proper-flag combinations
return 564 YES and 460 NO; 436 slices have no accepted path, and 588 nonempty
certified slices agree with complete bounded oracles invoking the proved bound.
Additional corpora: 320 boundary instances / 40,640 words; 289 productive dense
column instances; 386 productive larger sparse instances (298 certified,
88 uncertified) / 6,765 words; 150 complete acyclic languages; 31,682 KMP/literal
comparisons; 5,400 periodic-prefix cases; 58 independent negative-product replays.
A deliberately incomplete negative certificate is rejected. Seed 20260913122.

**Fixtures.** The six-state recurrent sparse YES is `0110`; a seven-state
recurrent sparse NO has a one-letter last-target tail and a four-state closed
prefix-product certificate. Each contains several source/target states in one
nonflat SCC. An eight-state sparse cycle case returns an 18-letter witness even
though static coloring fails. The known positive modular instance remains
UNKNOWN and its 14-letter witness is retained as an explicit scope regression.

**Status.** Deterministic local suites and byte-for-byte replay passed. These
are finite code/certificate checks, not independent mathematical review or Lean.
Dedicated read-only CI checks the integrated index/links and both solver commands;
its remote status must be read before claiming that it passed.

## Handoff

A017: audit last-target necessity, the terminal period bound, overlap at the
X/Y junction, the underlying-letter map of colors and the no-spurious-target-match
certificate. The native solver does not assume a word-equation backend or
source-scheme bound. Then investigate an existence-preserving generalization
which permits distinct legal target suffixes while keeping one shared word.
Static completion fails even on a known positive example; Q004 stays OPEN.

## Concurrent integration

Main advanced to `83baaf84486a84bb056272ee8bf895ba31a71d7a` during integration.
Its [ranked-suffix audit](../notes/2026-09-13-ranked-suffix-audit.md) is preserved.
That separate attempt uses nondeterministic occurrence ranks and records its
own unresolved consistency/termination obligation. The present deterministic
color certificate does not turn that decoration into a decision procedure,
nor independently certify its proof. No conflicting C/E IDs were allocated
in that checkpoint. The research base above remains the tested base; the
integration includes the concurrent note without changing it.
