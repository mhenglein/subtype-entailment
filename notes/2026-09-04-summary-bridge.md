# Actual summary bridge

Date: 2026-09-04

This note records the next A010 stage. It constructs the finite summary classes
and the `BorderAvoid` instance from one normalized propagation system `W`.
The stage remains a reduction component. It does not decide the unbounded
border-avoidance problem or Problem 1.7.

## Pop summaries

For a pushdown system `P`, define

```text
Pop_P(p, q) = { w : <p, w> ->*_P <q, epsilon> }.
```

`build_pop_summary` creates an NFA whose states are the control states of `P`.
It first adds epsilon edges for epsilon rules and letter edges for pop rules.
For every push rule `p --push a--> q`, it adds an epsilon edge `p -> r` when
the current graph has a path `q --epsilon* a epsilon*--> r`. Repeating this
operation reaches the least fixed point. An NFA path from `p` to `q` spelling
`w` is then the finite summary of a balanced run from `<p,w>` to
`<q,epsilon>`.

The orientation is checked against the direct stack semantics. A pop edge
consumes the leftmost stack letter. A push creates that letter, so a later
summary path must consume it before the original residual stack can be
returned. An empty stack cannot trigger a pop. The push/pop regression in
`check_summary_bridge.py` checks these cases directly.

### Saturation invariant

At every fixed-point stage, every NFA path from `p` to `q` labelled `w` has a
corresponding PDS run `<p,w> ->* <q,epsilon>`. The base edges are one-step
rules. A derived push edge uses a summary path that consumes the pushed letter,
so concatenating the push and that path leaves the residual stack unchanged.
Epsilon edges preserve the stack.

For completeness, take the first push, pop, or epsilon step of a shortest
balanced run. A pop or epsilon is represented by its base edge. For a push,
the portion of the run that first returns to the same residual stack consumes
the pushed letter and gives the `q --epsilon* a epsilon*--> r` path used by
saturation. Induction on the run proves the converse at the fixed point. This
is an audit of the standard summary argument; Lean has not checked it.

## Actual class construction

Set `A = W^rev`. For a query `alpha <= beta`, after reading a word `u`, the
construction retains the two exact endpoint subsets

```text
B(u) = { q : u in Pop_W(alpha, q) }
A(u) = { q : u in Pop_A(beta, q) }.
```

It also retains the subset reached by the denial-predecessor NFA described
below. Determinizing all three NFAs together gives a finite DFA. Empty `B` or
`A` subsets are retained as ordinary classes; they can arise after an
undefined summary transition and must not be discarded.

For two generated classes `c_i` and `c_j`, the flag relation is exactly

```text
G(c_i, c_j) iff B(c_i) intersect A(c_j) is nonempty.
```

This is the relation from Section 5, with the two summary directions kept
separate. The resulting DFA is converted to the existing `border_lab.Instance`:
its direct witness predicate checks all suffix agreements and therefore checks
the `B` condition after reversal of the propagation machine.

## Side conditions S and F

`F` is encoded in the final-state set. A word is final exactly when its `A`
endpoint subset is disjoint from `BF`, the variables forced to have product
roots by lower-product constraints. This says that no forced root can reach
`beta` at the candidate path in `W`, equivalently that no candidate path is
already forced into `beta` by the unconditional facts.

`S` is retained as a bad-state predicate. Construct an NFA with an accepting
state that loops on both letters. Add epsilon edges from every denial state to
that accepting state. Saturate predecessor configurations under the original
`W`. The language from `alpha` is exactly

```text
{ u : exists denial delta and stack z,
      <alpha,u> ->*_W <delta,z> }.
```

The determinized subset is bad whenever it contains that accepting state.
Because the DFA visits every prefix, rejecting any bad state enforces the
memo's requirement that no prefix seed reaches a denial. This construction
does not replace `S` with an assumption or omit it.

The same predecessor-saturation invariant applies: the accepting loops model
an arbitrary residual stack, and each saturated edge is justified by the
corresponding first PDS rule. A formal proof of this NFA construction remains
open.

## Reproducible check

Command:

```sh
python3 experiments/check_summary_bridge.py
```

Current result:

```json
{
  "status": "PASS",
  "scope": "actual W/Wrev pop summaries, S/F annotations, and witness cross-check",
  "witness_comparisons": 762,
  "max_word_length": 6,
  "c0_summary": {
    "control_states": 2,
    "w_pop_eps_edges": 0,
    "w_pop_letter_edges": 0,
    "a_pop_eps_edges": 0,
    "a_pop_letter_edges": 2,
    "summary_classes": 4,
    "flag_pairs": 1,
    "bad_classes": 0,
    "final_classes": 2
  },
  "empty_stack_pop": "validated",
  "push_pop_summary": "validated",
  "generator_rule_input": "validated",
  "actual_flag_relation": "validated",
  "unsat_precondition": "validated",
  "absent_query_variables": "validated",
  "s_annotation": "exact denial predecessor NFA",
  "f_annotation": "exact forced-root endpoint condition",
  "global_claim": "not a decision procedure for Problem 1.7"
}
```

The 762 comparisons cover six satisfiable systems and every binary word of
length at most six. Each summary witness result was compared with the exact
regular canonical-countermodel checker in `topfree_bridge.py`. The comparison
is bounded in word length, but both model checks use complete finite-automata
operations. It is evidence for this implementation stage, not an all-length
proof. A generator-valued rule input is tested before saturation, so push
rules cannot disappear during the base scan. Bridge construction raises an
explicit `ValueError` for unsatisfiable constraints; unconstrained query
variables remain valid and produce an empty-system bridge.

## Remaining dependencies

1. Formalize the path-set semantics and normalized constraint rules.
2. Formalize the pop-summary fixed-point invariant and the denial predecessor
   construction.
3. Prove that the actual class annotation is sufficient for all flags in the
   cap decomposition, including empty and full borders.
4. Prove that the `border_lab.Instance` conversion preserves `S`, `F`, and
   `B` for every word.
5. Solve the resulting unbounded `BorderAvoid` search, or prove a bound or
   complete `NO` certificate for classes arising from subtype systems.
