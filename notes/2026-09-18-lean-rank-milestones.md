# Lean: literal ranks, first-return milestones, and failure-target confinement

Date: 2026-09-18. Workstreams A018/A017. Author: ChatGPT.
Base main: `9e9d3ecfe1277bd6e7ea6aeffdf035c12e477f89`.
Foundation base: `2fe18864e39a26f6dd256bf05bea166c8c6b3d20`.
[Targeted route](2026-09-18-lean-milestones-route.md).

**Kernel-checked structural interface of the proposed rank-query proof, not a
Lean-verified unrestricted decision procedure. No global claim status is promoted.**
The ordinary rank and first-return arguments are prior candidate work. This
contribution formalizes those dependencies using the existing word/run semantics
and adds their exact interface to the next graph-surgery obligation.

## 1. What the formal statements actually say

[RankMilestones.lean](../lean/Subtail/RankMilestones.lean) imports the checked
[TerminalRank foundation](../lean/Subtail/TerminalRank.lean), which in turn reuses
`Subtail.Instance`, `runFrom` and `Agrees` from the existing core. Words are finite
binary lists. No new witness predicate or tree semantics replaces the original.

For a word x, `borderLengths x` is its literal list of prefix/suffix matching
lengths, including zero and the full length. Define:

    failureParent x = largest proper border length (zero for empty x),
    rank x = number of nonempty border lengths.

Both are executable finite-list operations. In particular the rank recurrence
is NOT inserted as an assumed field or an axiom. It is proved from the literal
border decomposition:

    borders(x) = {length(x)} disjoint-union borders(take(parent(x),x)), x != empty;
    rank(x) = rank(take(parent(x),x)) + 1.

`borders_below_border` proves that all shorter borders nest exactly. A nodup-list
permutation yields the cardinality equation. `rank_lt_of_proper_border` proves
strict rank growth above every proper border, not only the longest one.

`FirstMilestone w h m` means m is within the word, the rank at prefix m is at
least h, and every earlier prefix has rank strictly below h. For h>0,
`first_milestone_exact` proves the rank there is EXACTLY h; a skipped threshold
is not excluded by fiat. `exists_first_milestone` supplies the first milestone
whenever a threshold is reached at any bounded prefix. Classical reasoning is
used only in this erased existence proof, not the executable word operations.

If m and n are successive first milestones for h and h+1, h>0, then:

    parent(w[:n]) = m;
    m < n;
    w[:m] occurs as the suffix ending at n;
    no such occurrence ends at j with m < j < n.

These are `first_milestones_parent`, `first_milestones_first_return` and
`milestones_are_first_returns`. There is NO nonoverlap assumption. For example,
`0`, `010`, `01010` are successive rank milestones in `01010`; the last
return overlaps the old length-three reference.

The key index in the proof is j = n - p + m. If the new milestone had a proper
border of length p>m, the first m letters of its final occurrence would give a
complete old-reference return ending at j<n. This raises the rank to h+1 too
early. `shifted_border` proves that transfer with all natural subtraction bounds.

`no_return_after_maximal_rank` also excludes a return ending exactly at the
last letter: the final endpoint is not a free, uncounted extra rank increase.

## 2. The actual automaton bound is connected

`mem_borders_reverse` and `rank_reverse` prove exact invariance under reversal.
The previous terminal theorem on accepted forward suffixes now gives
`reversed_prefix_rank_le`:

    TerminalFinals I -> runFrom I q w = some f -> I.final[f] = true ->
    for every i, rank(take(i,reverse(w))) <= k-1.

Here q and f are ORIGINAL states of the k-state partial deterministic automaton.
This is proved for any accepted run, not just a particular generated annotation.
Flags and Bad-state conditions are unnecessary for the structural bound; actual
witnesses satisfy the stronger original conditions. Empty words and multiple
terminal finals are admitted. The theorem does not bound the word's length or
number of source visits. It is the finite rank-level dependency of the candidate,
not the separate theorem bounding the complexity within each level.

## 3. A first piece of the graph-surgery proof

`FirstReturn w m n` is a literal word property: m<n, n is within w, the prefix of
length m returns at n, and it does not return at an intermediate ending cut.
For ANY such first return (not merely one selected as a rank milestone),
`first_return_failure_targets` proves:

    parent(w[:n]) = m,
    for every m<j<n, parent(w[:j]) < m.

If an internal parent were at least m, the same shifted-border construction
would produce an earlier complete return. Therefore new failure links land
strictly inside the old reference until the new endpoint, which returns to the
old endpoint itself. This covers singleton extensions and overlapping copies.

This proves the F-edge confinement used in the ordinary first-return graph
construction. It does NOT yet formalize the full S/K0/K1 edge identities,
old-end recolouring, wrap edges, border masks or observer/query semantics.
Those obligations must be proved, not inferred from this narrower invariant.

## 4. Executed evidence and precise scope

The exact source blob `8cefde96f871d0f9c1389529e520f8e77742fabb` at commit
`0a8883dff181664ea3aa480055db479c1d1158cd` passed the pinned Lean 4.33.1 build,
bundled kernel replay, all 32 new public declaration dependency audits, and the
existing `scripts/check_lean.py` suite with its recorded output unchanged.
The [checked run](https://github.com/mhenglein/subtail/actions/runs/35308545464)
is an actual completed GitHub Actions execution. The check rejects research
axioms, unfinished-proof axioms and native-evaluation axioms; runtime definitions
also reject Classical.choice. Logical axioms permitted by the repository's
standard policy remain explicit. Kernel replay uses Lean's own kernel, not a
second external implementation.

The initial proof drafts had missing definition unfolding, explicit arithmetic
premises and one incorrect Std library theorem name. These were repaired without
weakening the target statements or adding mathematical assumptions. They are
retained in branch history and are not presented as counterexamples.

The [separate finite checker](../experiments/check_lean_rank_milestones.py)
compares literal slicing with a KMP prefix-function/depth implementation on
all 8,191 binary words of length at most 12, including 98,305 prefix checks,
16,434 successive milestones and 25,966 arbitrary first returns. This covers
5,096 overlapping milestone pairs, 6,228 overlapping arbitrary first returns,
8,166 singleton extensions and 446 milestones ending at the final position.
These are finite regression counts, not the justification for the all-word
Lean theorems. With `--lean`, it separately compares native Lean border lists,
ranks and parents on all 2,047 words through length 10; that mode reports PASS
only after the actual pinned executable succeeds. Its new CI replay and any
saved combined results must be read at the revision being claimed.

No local Lean installation was available in the chat container. The Lean
executions described above were on the repository's runner. Local Python
checks do not substitute for them. The semantic readback in Sections 1-3 was
by the same assistant who wrote the formalization, not an independent human
review. Source agreement, kernel checks, runtime comparisons and semantic
review are different evidence layers.

## 5. Handoff to the central formalization

These are completed dependencies, not a complete formalized solver. The next
precise obligation is the literal coloured prefix-graph update for a first
return: use the failure-target theorem above, then prove all successor/KMP
edges and colour equations, including the old endpoint and the singleton wrap.
After that, formalize the observer language and shared-interval diagram compiler
and prove BOTH uniform preimage directions. All observers of a physical interval
must use one shared word, and compilation must preserve the finite syntax for
iteration. The quantitative witness bound and arbitrary-tree semantic transfer
remain later formal obligations; neither is assumed by this module.

The proposed ordinary proof may still fail at one of these later steps.
Successful verification here does not certify the remaining compiler argument,
provide a percentage complete, or promote unrestricted subtype entailment to
an established result. All existing candidate and C/Q statuses are preserved.

```sh
cd lean
lake build +Subtail.RankMilestones
lake env leanchecker Subtail.RankMilestones
cd ..
python3 experiments/check_lean_rank_milestones.py --lean --output /tmp/lean-rank-milestones.json
python3 scripts/check_lean.py
python3 scripts/research_index.py --check
```

The dedicated workflow records the exact axiom-audit commands. Integration
imports the new modules through `lean/Subtail.lean` as well as checking the
explicit target, so the default build does not silently omit these proofs.
