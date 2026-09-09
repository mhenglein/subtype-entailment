"""Apply the approved research-method changes to a pinned checkout.

Temporary integration helper; not included in the resulting main commit.
"""
from pathlib import Path
import json
import subprocess
import textwrap

BASE = '23f508b9c1b2ba5e36bfb0e5e5b576ebdf8c7a24'
ROOT = Path.cwd()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() == BASE
assert not subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip()
changed = set()


def read(path):
    return (ROOT / path).read_text(encoding='utf-8')


def write(path, content):
    target = ROOT / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding='utf-8')
    changed.add(path)


def replace(path, old, new):
    content = read(path)
    assert content.count(old) == 1, (path, content.count(old), old[:90])
    write(path, content.replace(old, new, 1))


def block(content):
    return textwrap.dedent(content).strip() + '\n'


method = block('''
## Research method: discovery before verification

Precise mathematics is required from the start; complete formalization is not.
The default sequence is a conceptual end-to-end sketch, targeted falsification,
a precise ordinary proof, independent mathematical review, and selective Lean
formalization. These stages may iterate. An intuitive or apparently robust idea
is a reason to investigate a gap, not permission to assume it is repairable.

Before substantial supporting implementation or formalization, write or update
one route outline using [the proof-outline template](templates/proof-outline.md).
Give the exact final claim, every unresolved implication, and how a restricted
result would contribute to it. Reuse that outline across related attempts;
inexpensive falsification does not need to wait for a complete sketch. Do not
replace a missing global argument with an expanding inventory of local lemmas.

Keep both decidability and undecidability live. Identify whether an attempt is
forward from existing results, backward from a desired conclusion, or both.
For each significant obstruction, state what question it suggests for the
opposing route. Current priorities and concrete handoffs are in
[the research plan](research/PLAN.md), not an implicit preference in one chat.

## Mathematical precision and falsification

- Define every construction before using it. For an automaton give the state
  set, alphabet, transition function or relation, initial configuration, and
  accepting states or output condition. Specify partial transitions and why
  the construction is finite and effective from the input. A monitor or
  transition system without acceptance should be identified as such. Explain
  the state invariant; phrases such as "tracks everything simultaneously" do
  not define a construction.
- An imported theorem needs an exact source/theorem identifier, its hypotheses,
  an explicit mapping to our objects, and the conclusion actually obtained.
  If that transfer is unproved, record it as an open obligation. Name all
  quantifiers and preserve arbitrary-tree semantics and shared word parameters.
- Test the weakest statement that would suffice. An existential replacement
  theorem need not preserve every candidate or its complete agreement profile.
  A counterexample to a stronger universal statement does not refute the weaker
  target. Preserve the hypothesis under test when minimizing an example;
  shortestness and mere resistance to selected cuts are different properties.
- For a word transformation, separate preservation of acceptance, selected
  equalities and cut-state information, full witnesshood (including newly
  created forbidden comparisons), and global coverage/termination. Proving one
  does not prove the next. Include overlapping occurrences, empty/diagonal
  boundary cases, and recurrent structure whenever the statement allows them.
- Prefer a direct independent witness predicate to a second implementation of
  the same optimization. Save minimal obstructions with commands, seeds and
  limits. Search exhaustion is NO only when a proved completeness argument
  covers the entire stated input; a bounded failure remains UNKNOWN.

## Selective formalization

Maintain the existing Lean core and its checks. New formalization is not the
default next research milestone: name the disputed implication, semantic risk,
or stable critical dependency it is meant to resolve. Early Lean work is useful
when it can answer such a question, not merely because a local result exists.
A conditional decision theorem does not discharge its bound or reduction
hypotheses. Formalize a mature end-to-end argument preferentially, while keeping
its intended semantics independently reviewable in ordinary mathematics.

Report mathematical progress by the obligations discharged and remaining,
including their difficulty and uncertainty. Counts of commits, lemmas, tests,
or agreeing agents do not establish proximity to a solution. "One lemma left"
is not evidence that the final step is small.
''')
replace('AGENTS.md', '## Collaboration model\n', method + '\n## Collaboration model\n')
replace('AGENTS.md', '## Recover context and choose work\n', block('''
Use differentiated roles when multiple workers are useful: a constructive
researcher, an adversarial counterexample researcher, an undecidability
researcher, and a reviewer of definitions and critical implications. These are
roles, not a requirement for four simultaneous agents. Give initial independent
attempts the same exact definitions and evidence without forcing the same
preferred argument. Exchange explicit claims, proof sketches, counterexamples
and checkable results. Record what each reviewer actually checked and whether
they inherited the original argument; model diversity or agreement alone is
not independent validation. Compare parallel work with sequential separate
contexts by useful results surviving review per unit of effort, not output
volume. Do not claim workers were launched or reviews performed unless they were.
''') + '\n## Recover context and choose work\n')
replace('AGENTS.md', '6. Link all evidence and list exactly what remains unproved.\n', '''6. Link all evidence and list exactly what remains unproved.
7. When a conjecture is refuted or a statement repaired, update its individual
   C/Q lookup entries and add visible corrections at known original entry points.
   Inspect known dependents and distinguish invalid uses from valid conditional
   lemmas. Record any unaudited dependency scope; do not silently erase history
   or declare every associated theorem false. Separate code review, mathematical
   review, and formal verification in the evidence record.
''')

priorities = block('''
## Current research priorities (2026-09-09)

This is an organizational change following collaborator feedback, not a new
proof, experiment, or change to the decidability status. The operating rules
are in [AGENTS.md](../AGENTS.md); ownership and execution status remain solely in
[approaches.json](approaches.json). No investigator is assigned by this plan.

### The target, not a stronger substitute

Keep terminal-final BorderAvoid as the principal mathematical testing ground,
using the recorded C030/C031 bridge at its stated evidence level. The leading
constructive hypothesis is an existence-preserving normalization, an effective
finite symbolic cover, or another terminating exact procedure. A witness-bound
route would suffice if it establishes

```text
there exists a total computable F such that, for every finite binary
terminal instance I with k states,
    (there exists w with Witness_I(w))
    implies (there exists v with Witness_I(v) and |v| <= F(k)).
```

Here `Witness_I` is the exact existing predicate, including Bad states,
diagonal flags and the empty suffix; see [the problem](problem.md) and
[the checked binary definition](../lean/Subtail/Basic.lean). This is an
existential target, not a claim that every candidate can be shortened, that
all agreement profiles can be preserved, or that the witness language is
regular. Q002/Q003 and the modular family already refute several stronger
substitutes. A new proposal must survive those examples without assuming its
missing completeness or termination argument.

The single-source case remains a focused subproblem, not an automatic route
through the multi-source case. The current root-length and new-border
obligations are in the [single-source handoff](../notes/2026-09-08-strategy-review-and-period-state-form.md).
C042 rules out a source-wise viability shortcut. The [overlap audit](../notes/2026-09-09-overlap-deletion-audit.md)
repairs selected-equality preservation, not full witnesshood or a global bound.

### Two hypotheses, forward and backward

| Hypothesis | Forward from existing evidence | Backward from the final conclusion |
|---|---|---|
| SEP is decidable | Combine normalization, arithmetic and shared-word tools into an existence-preserving invariant. | State exactly what effective bound, complete finite cover, or terminating exact procedure would finish the reduction. |
| SEP is undecidable | Test whether recurrent copying and shared-word interactions enforce transformations or computation steps. | Start with a named undecidable source problem; specify the finite encoding and both directions of correctness in our exact terminal fragment. |

An obstruction in either row must yield a question for the other row. The
constructive route remains the lead hypothesis, not a presumption of the
answer. Block equality, nonregularity, a failed pump, or an undecidable more
expressive relation is not by itself an undecidability reduction here. A
failed encoding only rules out its stated gadget or construction class unless
a broader impossibility theorem is proved.

### Next research cycle: concrete handoffs

Use one [end-to-end outline](../templates/proof-outline.md) per route, with all
open implications named, before investing heavily in supporting machinery.
A short falsification attempt can start immediately. The next assignments are:

1. **Constructive and adversarial pair — A017/A008, with A016 support.** Choose
   one replacement or finite-cover obligation. For the single-source root
   pump, test the complete witness predicate after alignment-compatible
   deletion, including new borders and primitivity; acceptance and selected
   equality checks are not enough. Minimize counterexamples while preserving
   the exact hypotheses. Explain how a surviving restricted lemma enters the
   general outline, rather than assuming different sources compose.
2. **Opposing investigation — A011.** Use the terminal converse to test a
   specific computation/word-transformation gadget. Write both implications
   of a proposed reduction and the missing gadget before building a solver.
   Return a proved encoding, a precise obstruction to that encoding class,
   or an explicitly unresolved obligation; feed the structural finding back
   to A017/A012. This is a real research target, not a token negative route.
3. **Coverage and critical review — A012, with selective A018 support.** Make
   certificate soundness, coverage of all relevant instances, and termination
   separate obligations. Audit exact construction definitions and critical
   transfers in the leading outlines. New Lean work must resolve a specific
   uncertainty or verify a stable critical dependency; maintain existing
   checks without automatically extending the conditional framework.

These are proposed handoffs, not reports of launched agents or completed
research. Separate contexts may run sequentially or in parallel. Use an
independent first attempt where useful, exchange checkable artifacts, and
compare results surviving review per unit of effort. Different model families
may diversify search but do not establish independence or correctness.

### Review and stopping rules

The default order is conceptual sketch, targeted falsification, precise
ordinary proof, independent mathematical review, then selective formalization;
iterate when a test or review exposes a gap. Exact definitions and openly
labelled assumptions are required at every stage. Keep failed arguments and
small counterexamples, and distinguish a local repair from the missing global
existence/coverage theorem. Report which obligations were discharged, not how
many lemmas remain or how close a result feels. A strategy-only update must
not promote evidence labels, mark unperformed work active, or claim new checks.
''')
replace('research/PLAN.md', 'Updated: 2026-09-04', 'Updated: 2026-09-09 (current priorities; historical programme retained)')
replace('research/PLAN.md', '''This plan preserves the ten research angles and adds working backwards from a
Lean theorem as angle 11. Current execution status, owners, evidence, and next
steps live in the [research tracker](README.md). The entries describe each
investigation's target; dated approach records distinguish proposals from
executed attempts.
''', '''Current priorities appear first. The original eleven-angle programme is
preserved below as history, not as the current order of work. Execution status,
owners, evidence, and exact next steps live in the [research tracker](README.md).
Dated approach records distinguish proposed handoffs from executed attempts.
''')
replace('research/PLAN.md', '## September 4 starting order (historical)\n', priorities + '\n## September 4 starting order (historical)\n')
replace('research/PLAN.md', '## Eleven angles\n', '## Eleven angles (historical programme)\n')

replace('STATE.md', '# Subtail — current research state\n', '# Subtail — current research state\n\n' + block('''
## September 9 research-method update (organizational)

Current priorities now require an end-to-end conceptual route, targeted
falsification, and a genuine opposing undecidability investigation alongside
the leading terminal existence-preserving approach. Exact definitions remain
mandatory; new Lean work is selective rather than the default milestone.
[Current plan](research/PLAN.md#current-research-priorities-2026-09-09),
[operating rules](AGENTS.md), [outline template](templates/proof-outline.md).

The C041/C044/C045 entries and the known Q002/Q003 source-note entry points
now distinguish the refuted universal conjectures from surviving identities,
equivalences and conditional local lemmas. This is status synchronization, not
a new proof or complete dependency re-audit. No mathematical evidence level,
problem status, or worker ownership is promoted by this update.
''') + '\n')

replace('CONTRIBUTING.md', '''The [research plan](research/PLAN.md) preserves the original programme; use
`STATE.md` and the conjecture records for the current frontier.''', '''The [research plan](research/PLAN.md) gives current priorities first and preserves
the original programme as history; use `STATE.md` and the conjecture records
for the current mathematical frontier.''')
replace('CONTRIBUTING.md', '## Pick and claim work\n', block('''
For a new route, reuse or complete [the proof-outline template](templates/proof-outline.md)
before substantial supporting implementation or formalization. Exact definitions
and named gaps are required from the beginning; a cheap counterexample search
need not wait for a complete outline. New Lean work needs a specific semantic
risk, disputed implication, or stable critical dependency to resolve; existing
checks remain maintained. See [the operating rules](AGENTS.md).
''') + '\n## Pick and claim work\n')
replace('CONTRIBUTING.md', 'If a claim changed, update its ledger entry in the same commit.', 'If a claim changed, update its individual ledger and Q lookup entries in the same commit, correct known original entry points, and record which dependent uses were checked or remain unaudited.')
replace('CONTRIBUTING.md', '| Historical research programme | `research/PLAN.md` |', '| Current research priorities and historical programme | `research/PLAN.md` |')
replace('CONTRIBUTING.md', 'For a new theorem, ask a reviewer to check the argument independently.', 'Separate implementation checks, ordinary mathematical review, and formal verification. For a new theorem, ask a reviewer to check the argument independently, with exact construction definitions, quantifiers, imported theorem hypotheses, and both directions of any claimed reduction.')

replace('lean/README.md', '## Build and check\n', block('''
## Role in the research process

This core remains maintained. Extending it is not the default research
milestone while the global mathematical argument is missing. Under
[the current plan](../research/PLAN.md), a new formalization task must name the
specific semantic uncertainty, disputed implication, or stable critical
dependency it resolves. Early formalization is welcome when it answers that
question; otherwise prioritize a conceptual route, falsification and ordinary
mathematical review. Existing checks are still required for Lean changes.
Conditional theorem hypotheses below remain open mathematics, not progress
obtained merely by extending the formal framework.
''') + '\n## Build and check\n')

replace('templates/attempt.md', '**Acceptance and limits.**', block('''
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
''') + '\n**Acceptance and limits.**')
replace('templates/attempt.md', '**What failed or remains uncertain.**', block('''
**Adversarial check and opposing implication.** Separate acceptance, selected
equality/cut-state preservation, full witnesshood, and global coverage or
termination. Test new comparisons and overlapping occurrences where allowed.
Minimize failures without dropping the target hypotheses. State what the
obstruction suggests for the opposing decidability/undecidability route.

**Formalization decision.** Maintain existing checks. For new Lean work name
the precise mathematical uncertainty or critical dependency it resolves;
otherwise defer it. Do not infer correctness from an idea feeling robust.
''') + '\n**What failed or remains uncertain.**')
replace('templates/attempt.md', 'Update `approaches.json` if current status, owner, evidence, or next step changed;', 'Report which mathematical obligation was discharged and which remains; a count\nof remaining lemmas is not a proximity estimate. Update `approaches.json` if\ncurrent status, owner, evidence, or next step changed;')

assert not (ROOT / 'templates/proof-outline.md').exists()
write('templates/proof-outline.md', block('''
# End-to-end research outline

Date / author:
Approach and existing claim/conjecture IDs:
Base commit:
Status: exploratory outline / ordinary proof / reviewed proof (choose one).

Keep this short and reuse it across related attempts. Exact definitions and
visible gaps matter more than length. This is not a requirement to formalize
an unfinished idea or to delay an inexpensive falsification test.

## Exact input and intended conclusion

State the finite input, constructors, tree semantics and quantifiers. Is the
conclusion a general decision, a restricted theorem, a counterexample, or an
encoding? Define witnesshood by reference to its exact canonical predicate.
For a restricted result, explain its proposed contribution to the general
problem and name the missing extension; do not assume composition.

## Objects and construction contracts

Define all symbols before use. For an automaton give the actual state set,
alphabet, transition function/relation, initial configuration and accepting
states or output condition. Define missing-transition behavior and the run
invariant. Explain effective construction and finiteness from the input; do
not hide arbitrary histories or trees inside a supposedly finite state.
Preserve shared assignments when multiple comparisons concern the same word.

## Route from start to finish

Write the complete proposed chain of implications in ordinary mathematics.
Label each link as recorded evidence, a proved step in this attempt, or a
named open obligation. An intuitive idea may motivate a gap but cannot
silently discharge it. State the exact theorem and assumption mapping for
any imported result. For a reduction give both implications and effectiveness;
for a decision procedure separate soundness, completeness and termination.

## Necessary target versus convenient strengthening

State the weakest result sufficient for the route. Identify any extra demands
such as preserving every candidate, all agreement profiles, or all accepted
words rather than some witness. A failure of the stronger statement is not a
failure of the weaker one. For transformations separately address acceptance,
selected equalities and cut states, full witnesshood including new forbidden
comparisons, and availability/coverage of the transformation at the global scale.

## Most discriminating falsification

Name the precise hypothesis, existing regressions, adversarial input family,
independent predicate, bounds and minimization invariants. Include overlapping
occurrences and boundary cases when in scope. An arbitrary accepted-word
counterexample need not refute a shortest-witness statement. Bounded failure
is UNKNOWN unless a separate completeness proof covers the entire search.

## Opposing route and next decision

What does success or failure suggest for the other decidability hypothesis?
Which observation would change the preferred route? For a proposed negative
encoding distinguish word equality from a transformation/computation gadget;
an obstruction only rules out its proved construction class.

## Review and formalization

List what has actually been independently reviewed, by whom or by which
independent algorithm, and what remains unaudited. Distinguish mathematical
review, software checks and Lean verification. Identify a specific uncertainty
or stable critical dependency before proposing new formalization; otherwise
leave it deferred while maintaining existing checks. End with the one next
mathematical obligation, not a claim that few remaining steps imply closeness.
'''))

replace('.github/pull_request_template.md', '## Integration checklist\n', block('''
## Route and precision review

For mathematical work, link the end-to-end outline and name the implication
this result discharges. Give exact construction definitions and imported
theorem hypotheses. Distinguish the necessary existential target from any
stronger statement tested. For transformations, separate acceptance, selected
equalities, full witnesshood and global coverage/termination. Explain what
failures suggest for the opposing route. Organization-only changes may mark
this section not applicable; do not invent mathematical progress.

New formalization must name the uncertainty or critical dependency it resolves.
Record implementation review, mathematical review and formal verification
separately; consensus among agents is not independent proof.
''') + '\n## Integration checklist\n')
replace('.github/pull_request_template.md', '- [ ] Failed/inconclusive paths preserved rather than overwritten.', '''- [ ] Failed/inconclusive paths preserved rather than overwritten.
- [ ] Refuted/repaired claims corrected in individual lookup entries and known source entry points; dependency-review scope stated.
- [ ] Construction definitions, quantifiers and theorem transfers explicit; unresolved implications labelled.
- [ ] No inference of proximity from numbers of lemmas, tests, commits or agreeing agents.''')

replace('research/claims.md', 'Index updated: 2026-09-06.', 'Index updated: 2026-09-09.')
replace('research/claims.md', '''**Status / scope.** `WRITTEN PROOF` for the exact word-level identity. It
reframes the terminal `B<=k-2` candidate but does not prove that candidate.''', '''**Status / scope.** `WRITTEN PROOF` for the exact word-level identity.
The terminal `B<=k-2` candidate it originally reframed is now REFUTED; see
[Q002](conjectures/Q002.md) and the
[modular counterexample](../notes/2026-09-05-modular-synchronization.md).
That refutation does not refute this word-level identity.''')
replace('research/claims.md', '''**Status / scope.** `WRITTEN PROOF`; C034 establishes `TB(k)` and hence
`PD(k)` for `k<=4`, while the budget statement remains open for larger `k`.
The linked bounded searches are falsification evidence only.''', '''**Status / scope.** `WRITTEN PROOF` for the equivalence, not for either
universal bound. C034 establishes `TB(k)` and hence `PD(k)` for `k<=4`.
**Q002 is REFUTED:** the eight-state modular instance violates the `k-2`
budget and the corresponding profile-domination statement. See
[Q002](conjectures/Q002.md) and the
[counterexample](../notes/2026-09-05-modular-synchronization.md).
This does not refute the equivalence or claim failure for every individual
`k>4`. Earlier bounded searches remain historical evidence.

**Status correction (2026-09-09).** Replaces the stale larger-state OPEN
commentary. No new proof review or evidence-level promotion is claimed.''')
replace('research/claims.md', '''**Status / scope.** `WRITTEN PROOF + REPRO`; this is a local theorem under its
three hypotheses. The uniqueness condition is essential, and Q003 remains a
conjecture.''', '''**Status / scope.** `WRITTEN PROOF + REPRO` for this local theorem under
its three hypotheses. The uniqueness condition is essential.
**Q003 is REFUTED:** see [Q003](conjectures/Q003.md) and the
[modular counterexample](../notes/2026-09-05-modular-synchronization.md).
That refutation does not refute C045 or establish its hypotheses for arbitrary
witnesses; unconditional strict profile descent must not be inferred.

**Status correction (2026-09-09).** Replaces the stale conjecture commentary.
The local proof and its recorded evidence are unchanged. This is not a new
independent mathematical review or a full audit of every dependent use.''')
replace('notes/2026-09-05-profile-and-fractional-power.md', '''Unrestricted Problem 1.7 remains open. The profile-normalization statement in
Section 2 is a conjecture, not a proved all-state theorem.''', '''Unrestricted Problem 1.7 remains open.

**Status correction (2026-09-09).** The universal profile-normalization
conjecture discussed below is REFUTED; see [Q002](../research/conjectures/Q002.md)
and the [modular counterexample](2026-09-05-modular-synchronization.md).
C044 records an equivalence, not a proof of either refuted universal claim;
C043 and that equivalence retain their recorded evidence levels. The original
argument and bounded-search discussion below are preserved as history. This
correction is not a new independent review of their proofs.''')
replace('notes/2026-09-05-unbordered-gap-normalization.md', '''**Status: C045 has a written proof plus bounded independent reproduction. Q003
is a conjecture with falsification evidence only. Unrestricted Problem 1.7
remains open.**''', '''**Status: C045 retains its written proof plus bounded independent reproduction
under its exact hypotheses. Unrestricted Problem 1.7 remains open.**

**Status correction (2026-09-09).** Q003 is REFUTED; see
[Q003](../research/conjectures/Q003.md) and the
[modular counterexample](2026-09-05-modular-synchronization.md).
The unconditional descent conjecture and the conditional C045 lemma are
separate statements. The refutation does not refute C045, and C045 does not
supply its hypotheses for arbitrary witnesses. Original conjectural discussion
below is retained as history, not a live target. No new proof review is claimed.''')

next_steps = {
    'A008': 'Falsify precise shortest-witness replacement hypotheses against the complete witness predicate, including new borders after overlapping deletions. Minimize while retaining the stated hypotheses; use a surviving lemma in the A017 route outline rather than defaulting to more census formalization.',
    'A011': 'Run an opposing undecidability investigation: choose a named undecidable source problem, specify a transformation/computation gadget in the exact terminal fragment, and expose both reduction directions through C030/C031. Return an encoding, a scoped gadget obstruction, or an explicit gap; feed it back to A017/A012.',
    'A012': 'Seek a complete symbolic NO cover that may change or discard candidates with proof. Separate certificate soundness, global coverage and termination; use A017 obstructions and A011 gadget failures as inputs, rather than only increasing finite-state separator memory.',
    'A016': 'Use the exact supplied-skeleton solver to test finite-cover hypotheses for nonflat terminal inputs. Audit any critical arithmetic transfer; add Lean formalization only for a specific uncertainty or stable dependency. A supplied-schema solver is not a complete cover, and caps remain UNKNOWN.',
    'A017': 'Write a complete conditional route outline, then attack one existence-preserving replacement or finite-cover obligation. For the single-source root pump, test full witnesshood and primitivity after alignment-compatible deletion. Feed obstructions to A011/A012; do not assume source-wise results compose.',
    'A018': 'Maintain the checked Lean core. Select new formalization only to resolve a named semantic uncertainty, disputed implication or stable critical dependency in an end-to-end outline; otherwise prioritize falsification and ordinary proof review. The global bound and subtype reduction remain open.'
}
data = json.loads(read('research/approaches.json'))
original = json.loads(json.dumps(data))
for row in data['approaches']:
    aid = row['id']
    if aid not in next_steps:
        continue
    row['next_step'] = next_steps[aid]
    row['updated'] = '2026-09-09'
    if aid == 'A018':
        row['title'] = 'Maintain the Lean core and verify critical obligations'
    record = row['record']
    write(record, read(record).rstrip() + '\n\n' + block(f'''
### 2026-09-09 — Research-method priority update (organizational)

Recorded by: ChatGPT, applying the user-approved strategy assessment.
Base main: `{BASE}`. Workstream: {aid}.

**Scope and result.** Updated the current handoff under
[the research plan](../PLAN.md#current-research-priorities-2026-09-09).
This is a proposed next investigation, not a newly executed proof attempt,
experiment, formalization, independent review, or worker assignment. Existing
mathematical outcomes and evidence labels are unchanged.

**Next discriminating action.** {next_steps[aid]}

**Limits.** Follow [the operating rules](../../AGENTS.md) and reuse the
[proof outline](../../templates/proof-outline.md). Exact definitions and
assumptions are required even in exploratory sketches. Historical tasks above
are retained; current execution metadata remains in `approaches.json`.
'''))
for before, after in zip(original['approaches'], data['approaches']):
    for key in set(before) - {'next_step', 'updated', 'title'}:
        assert before[key] == after[key], (before['id'], key)
write('research/approaches.json', json.dumps(data, indent=2, ensure_ascii=False) + '\n')
replace('research/approaches/A011.md', 'No attempt evidence yet. References and prerequisites are context, not proof that this approach has been tried.', 'The terminal-converse attempt above has written-proof and reproduction evidence. The new undecidability handoff is a proposal, not a completed encoding or a newly executed experiment.')
replace('research/approaches/A018.md', '# A018: Work backwards from an executable Lean theorem', '# A018: Maintain the Lean core and verify critical obligations')
replace('research/approaches/A018.md', 'The initial deliverable is a core for finite words, BorderAvoid witnesses, the stronger truncation lemmas, and the conditional finite-search argument. Full pushdown formalization comes later. Python remains the rapid counterexample-search tool.', 'The original deliverable and milestone sequence below are historical. The current priority is maintaining the checked core and selectively verifying critical obligations under [the research plan](../PLAN.md). Python remains the rapid counterexample-search tool; extending the formal framework is not the default next task.')

replace('scripts/test_research_index.py', 'from pathlib import Path\n', 'from pathlib import Path\nimport json\n')
new_tests = block('''
class CurrentClaimStatusTests(unittest.TestCase):
    """Guard known status corrections, not the truth of mathematical proofs."""

    def setUp(self):
        root = Path(__file__).resolve().parents[1]
        with patch.object(index, "ROOT", root):
            data = json.loads((root / "research/approaches.json").read_text())
            self.records = index.research_records(data)

    def test_c044_keeps_equivalence_distinct_from_refuted_q002(self):
        claim = self.records["C044"]["content"]
        self.assertIn("Status: REFUTED", self.records["Q002"]["content"])
        for text in ("WRITTEN PROOF", "equivalence", "C034", "Q002 is REFUTED"):
            self.assertIn(text, claim)
        self.assertNotIn("remains open for larger", claim)

    def test_c045_keeps_conditional_lemma_distinct_from_refuted_q003(self):
        claim = self.records["C045"]["content"]
        self.assertIn("Status: REFUTED", self.records["Q003"]["content"])
        for text in ("WRITTEN PROOF + REPRO", "three hypotheses", "Q003 is REFUTED"):
            self.assertIn(text, claim)
        self.assertNotIn("Q003 remains a", claim)
''')
replace('scripts/test_research_index.py', 'if __name__ == "__main__":\n', new_tests + '\n\nif __name__ == "__main__":\n')

subprocess.run(['python3', 'scripts/research_index.py'], check=True)
changed.add('research/README.md')
actual = set(subprocess.check_output(['git', 'diff', '--name-only'], text=True).splitlines())
actual.update(subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], text=True).splitlines())
assert actual == changed, ('unexpected changed paths', sorted(actual ^ changed))
assert all(path.endswith('.md') or path in ('research/approaches.json', 'scripts/test_research_index.py') for path in actual)
print('APPROVED_CHANGED_PATHS=' + json.dumps(sorted(actual)))
print('No solver, Lean declaration, result artifact, source paper, or main-branch workflow changed.')
