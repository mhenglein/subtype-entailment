# Research tracker

Problem 1.7 is open. This is the current map of approaches, including unsuccessful work.

**13 tried · 4 not tried · 1 blocked · 0 active**

Read [the problem and notation](problem.md), [claims and evidence](claims.md), and [the experiment index](../experiments/README.md).

Use [the research plan](PLAN.md) for the eleven proposed angles, priorities, and dependencies, including the Lean workstream.

Choose a record below to see its scope, attempt history, evidence, and limitations. All unowned work is available to discuss; nobody has been assigned automatically.

## How to read the status

- **Not tried:** a proposed approach; reading a related paper does not count as trying it.
- **Active:** someone is currently working on it and is named as owner.
- **Blocked:** a specific dependency prevents the next step; the record says whether any prior attempt exists.
- **Tried:** an attempt and evidence are recorded. This does not mean the problem is solved.

Outcomes are separate: **supported** applies to the stated limited claim, **refuted** to the exact failed claim, **inconclusive** to an attempt without a verdict, and **open** to unresolved work. Proof status is recorded in the claims ledger.

## Active work

None currently.

## Not tried

| ID | Approach | Finding / next step | Owner |
|---|---|---|---|
| A011 | [Complete the converse with regular annotations](approaches/A011.md) | State the desired converse precisely and construct a reduction preserving the regular restriction. | Unassigned |
| A012 | [Make NO certificates complete](approaches/A012.md) | Find a precise invariant or instance that separates current NO certificates from full nonexistence. | Unassigned |
| A014 | [Apply cap and period-language saturation techniques](approaches/A014.md) | Choose one closure property, test small instances, and preserve all endpoint flags. | Unassigned |
| A016 | [Implement and audit fixed-skeleton checkability](approaches/A016.md) | Audit and implement the one-block exponent test, then check two interacting blocks. | Unassigned |

## Blocked

| ID | Approach | Finding / next step | Owner |
|---|---|---|---|
| A007 | [Reproduce the original memo's code and census](approaches/A007.md) · [#1](https://github.com/mhenglein/subtail/issues/1) | The original analysis-2026 folder has not been supplied. Next: Import original sources unchanged, record provenance, and cross-check against the independent implementation. | Unassigned |

## Tried: results and dead ends

| ID | Approach | Finding / next step | Owner |
|---|---|---|---|
| A001 | [Audit the top-free characterization](approaches/A001.md) | Supported: Theorem 2.6 supports canonical regular countermodels under its satisfiability premise. Next: No new work assigned; use the audited statement as a dependency. | Unassigned |
| A002 | [Replace prefix reachability with a regular language](approaches/A002.md) | Refuted: The old formula disagrees on 4,017 words through length 11; the all-length family is nonregular. Next: Do not reuse the old formula; retain the corrected cap decomposition. | Unassigned |
| A003 | [Bound all rigid witnesses using nonmerging runs](approaches/A003.md) | Refuted: Two states admit rigid words 0^n with unbounded repeated suffixes, while the runs merge. Next: Use minimal witnesses and stronger cuts instead. | Unassigned |
| A004 | [Transfer the shorter word's repeated suffix](approaches/A004.md) | Supported: C008 has a written proof and a checked binary Lean proof; earlier bounded cuts also pass. Next: Use C008 and the stronger C013 context rule in A008. | Unassigned |
| A005 | [Weaken state equality to incoming flag-set inclusion](approaches/A005.md) | Supported: C009 has a written proof and a checked binary Lean proof with the incoming-flag direction verified. Next: Compare witnesses resistant to C009 and C013 in A008. | Unassigned |
| A006 | [Calibrate small-budget expectations](approaches/A006.md) | Refuted: A singleton 0^n language has exact B=n-1 at n+1 states; the checked 13-state instance has B=11. Next: Use this baseline before searching for harder growth in A009. | Unassigned |
| A008 | [Bound minimal witnesses after stronger truncation](approaches/A008.md) · [#2](https://github.com/mhenglein/subtail/issues/2) | Supported: Written proof decides at most three states: shortest length at most six and budget at most two, both sharp; the global bound remains open. Next: Formalize the three-state classification and study the actual terminal-path loop obstruction in A013. | Unassigned |
| A009 | [Find budget growth beyond the regular-language baseline](approaches/A009.md) | Supported: A one-flag k-state family has exact B=2k-4 and shortest length 3k-3; five states refute B<=\|K\|. Next: Any universal abstract bound must allow 2k-4. Separate abstract growth from actual summary outputs, which satisfy absorption. | Unassigned |
| A010 | [Build the exact top-free constraint-to-automata pipeline](approaches/A010.md) · [#3](https://github.com/mhenglein/subtail/issues/3) | Supported: Implemented actual W/Wrev summaries with S/F annotations; independent audit fixed two API errors and found no known comparison mismatch. Next: Generate actual subtype-derived instances and test joint summary invariants in A013. | Unassigned |
| A013 | [Exploit restrictions shared by actual summary automata](approaches/A013.md) | Supported: Proved summary absorption and B-prefix denial safety; decided infinitely extendable witnesses. An actual terminal example requires a pre-final loop. Next: Decide terminal safe witnesses with unbounded pre-final histories; preserve the shared B/A/D structure and formalize the periodic-suffix monitor. | Unassigned |
| A015 | [Strengthen truncation using occurrence context](approaches/A015.md) | Supported: Proved three context refinements and formalized the binary visited-state rule; strict examples and exhaustive two-state checks pass. Next: Use the visited-state summary to classify shortest witnesses resisting every admissible cut in A008. | Unassigned |
| A017 | [Bound essential repeated blocks](approaches/A017.md) | Inconclusive: An exact border-lifting condition makes loop deletion sound; a three-state example refutes deletion from state repetition alone. Next: Find a finite join-context summary that guarantees border lifting and bounds essential blocks. | Unassigned |
| A018 | [Work backwards from an executable Lean theorem](approaches/A018.md) | Supported: Lean checks direct budget predicates, reversal, and an exact two-state decision, in addition to the previous truncation and conditional proofs. Next: Formalize the finite Sufficient automaton and its exact nonemptiness procedure; the global bound remains open. | Unassigned |

## Updating the record

1. Add a dated attempt to the approach's Markdown record; preserve previous failed and inconclusive attempts.
2. Update its status, outcome, owner, evidence links, and next step in [approaches.json](approaches.json).
3. Update the claims ledger or experiment index if a result changed.
4. Run `python3 scripts/research_index.py` from the repository root, complete the relevant checks, then commit and push authorized updates to `main`. Use a pull request only when requested.

Use [the contribution guide](../CONTRIBUTING.md). GitHub issues hold discussion; this registry holds the current research status. Closing an issue does not establish a theorem.

<!-- Generated by scripts/research_index.py. Edit approaches.json and approach records, then regenerate. -->
