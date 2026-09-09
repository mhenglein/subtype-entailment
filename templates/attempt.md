### YYYY-MM-DD — Brief attempt title

Author / agent:
Approach ID:
Claim / conjecture IDs:
Experiment IDs, if applicable:
Base commit / branch:
Owned paths or worktree:

**Question and dependencies.** State one exact target, quantifiers, model,
and assumptions. Link the required statements and their evidence levels.
Separate open assumptions from established results. Name relevant failed
attempts and explain what this attempt changes.

**Reasoning direction and route.** Identify decidability or undecidability and
forward or backward reasoning (or both). Link the shared end-to-end outline;
use [the outline template](proof-outline.md) for a new route before substantial
supporting implementation/formalization. State which final implication this
attempt addresses and whether its target is stronger than necessary. A cheap
falsification attempt need not wait for a complete outline.

**Construction contract.** Give exact objects, quantifiers and invariants.
For each automaton specify states, alphabet, transitions, initial and accepting
conditions, and effective finiteness. Identify every imported theorem and map
its hypotheses to these objects; mark an unproved transfer as a gap.

**Acceptance and limits.** State what would count as a proof, a validated
counterexample, useful bounded evidence, or an inconclusive result. Give the
command, seed, inputs, word/state caps, and time or compute budget where relevant.

**Method and result.** Record the argument or exact commands actually run,
checked revision, result, and evidence links. A stopped search is UNKNOWN.
A conditional proof does not establish its assumptions.

**Independent check.** Name the reviewer or independent predicate, the exact
scope checked, and any unresolved disagreement. If not reviewed, say so.

**Adversarial check and opposing implication.** Separate acceptance, selected
equality/cut-state preservation, full witnesshood, and global coverage or
termination. Test new comparisons and overlapping occurrences where allowed.
Minimize failures without dropping the target hypotheses. State what the
obstruction suggests for the opposing decidability/undecidability route.

**Formalization decision.** Maintain existing checks. For new Lean work name
the precise mathematical uncertainty or critical dependency it resolves;
otherwise defer it. Do not infer correctness from an idea feeling robust.

**What failed or remains uncertain.** Preserve the smallest obstruction,
failed strengthening, and uncovered scope. Keep unsuccessful attempts after
recording a repair.

**Handoff.** State the next discriminating action and enough detail to resume:
remaining obligation, relevant paths, command/seed/limits, and partial outputs.
Report which mathematical obligation was discharged and which remains; a count
of remaining lemmas is not a proximity estimate. Update `approaches.json` if
current status, owner, evidence, or next step changed;
update the claim/experiment/Q index and `STATE.md` only where the result warrants it.
