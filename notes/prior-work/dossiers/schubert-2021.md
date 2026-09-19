# PW-SCH21: withdrawn solution-extension attempt

**Source:** Aleksy Schubert, *On non-structural subtype entailment*. [Version/status record](https://arxiv.org/abs/2109.02458), [v1 PDF](https://arxiv.org/pdf/2109.02458v1). v1 was submitted 6 September 2021; v2 is dated 20 December 2021 and withdraws the paper because a formulation error in Lemma 5.5 invalidates the further construction. The old abstract's PSPACE claim is not an established upper bound.

**Inspection:** selected primary text around Definition 11, Proposition 5.4 and Lemma 5.5; the extension definition and lemma occur on printed pp. 15–16. No independently reconstructed concrete counterexample to this lemma is supplied here.

## The actual object being changed

Definition 11 extends a ground solution substitution by replacing selected constant leaves with homogeneous binary products, also changing linked positions. In the paper's indexed notation, `bottom_0` is bottom and `bottom_1` is top. Lemma 5.5 claims that, under its position-decoration and leaf assumptions, the extended substitution still solves the full constraint set; it also claims preservation of the stated constant-avoidance property. This is a global solution-preservation claim, not merely an automaton normal form.

## Comparison with C080: an audit map, not a reduction

| Dimension | Withdrawn attempt | Subtail obligation to examine |
|---|---|---|
| Changed object | A substitution assigning type trees | A first-return extension of a prefix/reference word and its literal graph |
| Global property | All original constraints hold together after extension | All query atoms hold together on one reconstructed extension |
| Coupling risk | Linked positions must be changed consistently | Shared physical intervals must use common generators and compatible endpoints/colors |
| Coverage | Later reduction relies on extension/pumping | Forward coverage must produce a valid bounded diagram from every allowed extension |
| Semantic domain | The paper's bottom/top signature and finite/regular types | The exact top-free arbitrary-tree problem after the audited bridge |

The common *question* is whether local modifications preserve all simultaneously quantified requirements. That resemblance does not prove the methods equivalent, establish a common counterexample, or certify that C080 avoids the failure.

At the preserved repository baseline, `closure_reverse` is already recorded as checked; the older 'an extension exists but query preservation is missing' description is an intermediate historical checkpoint, not the final state of that branch. Read current STATE before assigning a repair task.

## What a real failure reconstruction must contain

Supply a finite constraint set `E`, a substitution `S` satisfying it, the chosen variable/position/index, evaluation of every premise of Lemma 5.5, the exact extended substitution, and a specific original constraint that fails afterwards. Distinguish a false conclusion from an undefined construction or an omitted hypothesis. Then test whether any analogous premises are actually present in C080; do not transfer a failure by vocabulary alone.

Until that artifact exists, the justified statements are the official withdrawal and the identified preservation obligation. Definitions or earlier lemmas may remain useful after separate inspection. A downstream theorem using the faulty step is unsupported by this proof, not necessarily false as a mathematical proposition.
