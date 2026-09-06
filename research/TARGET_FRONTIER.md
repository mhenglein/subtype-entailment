# Target-frontier continuation: proposed C054-C056 / E035

Date: 2026-09-06. Base: PR #9 (`df54d87`).
**Unrestricted Problem 1.7 is not settled.** These records contain written
proofs with reproducible checks, not independent review or Lean verification.

<a id="c054"></a>
## C054 - Finite pending-mask normalization before a fixed reference suffix

Fix r delimited reference blocks containing all flag targets of a witness.
Earlier blocks avoid every second endpoint of G. Relative to those references,
a block is summarized by full-word equalities E and equal-tail flag hits H.
A finite pending-pattern monitor has at most K*2^(r-1) boundary memories.
Deleting repeated memories preserves the reference suffix and witnesshood for
G. Hence at most K*2^(r-1)-1 earlier blocks suffice. This is G-specific
preservation, not full agreement-profile domination or a k-2 budget bound.

<a id="c055"></a>
## C055 - Exact powerset solver with unknown reference words

A reverse convolution chooses the reference words while a powerset retains ALL
possible target-free source-block observations relative to that same tuple.
After the references finish, longer source prefixes reduce to finite data
reachability. A finite pending-pattern search joins the original start to the
reference cut. Soundness and completeness hold for each supplied reference
schema. With b=binom(r,2), the combined state bound is

    2*(K+1)^r * 2^(2*b + 2*K^2*4^r).

The full note derives an explicit witness-length bound as well. Caps remain
UNKNOWN; None disables them. No unrestricted finite-quotient theorem is claimed.

<a id="c056"></a>
## C056 - Automatic certificate allowing unbounded early marker cycles

For the verified paired or unary token format, forbid a productive marker
cycle only if it is reachable from a relevant flag target. Target-free cycles
before that region are permitted. A target-free accepting path is immediately
a witness; otherwise the block containing the first target starts a reference
suffix of at most K-1 blocks. Its finite schema cover combined with C055 is
exact for this checkable raw-input class. C054 gives the existential total-block
bound K*2^(K-2)+K-2 for K>=2, despite unbounded marker counts among candidates.

Two 21-allocated-state binary fixtures (seven macro states, eighteen live raw
states) are YES and NO respectively. C053 returns UNKNOWN for both; the new
solver decides both. Target-reachable marker cycles and unaligned formats
still give UNKNOWN. No delimiters are inserted into original words.

[Full proofs and scope](../notes/2026-09-06-target-frontier.md).
[Implementation](../experiments/target_frontier.py).

<a id="e035"></a>
## E035 - Reproduction

```sh
python3 experiments/check_target_frontier.py
```

[Checker](../experiments/check_target_frontier.py),
[result](../results/target-frontier.json).

160 complete acyclic raw-input oracles (65 YES/95 NO); 160 previous exact-schema
comparisons (63/97); all 256 selected cyclic-prefix flag relations (88/168),
checked using 512 independent old-schema calls. Also 140 exact source-observation
sets, 700 logical/raw predicate comparisons, two three-reference solver fixtures,
207 successful normalizations,
eight canonical-model path checks, four scope guards, five intentional caps,
and two uncapped fixtures. No unintentional UNKNOWN or oracle mismatch.

The original core border regression and E033/E034 were reproduced byte-for-byte.
No full repository or Lean build was run. Independent review remains pending.

## Remaining obligation

Bound or represent recurrent flag targets, without identifying distinct suffix
words merely because their DFA states agree. The proof normalizes arbitrary
early marker loops only because those loops have no flag targets. Coverage of
all terminal inputs has not been established.
