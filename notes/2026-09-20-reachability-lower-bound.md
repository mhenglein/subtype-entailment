# Directed reachability already occurs in variable-only entailment

Date: 2026-09-20. A010/A017, C083, #53/#37.
Status: ordinary proof with independent read-only review. No Lean claim.

## Exact reduction

Take a finite directed graph on explicitly listed vertices `0,...,n-1`, with
n>=1, edge list E and distinguished vertices s,t. Introduce one variable x_v
per vertex. Output the finite constraint list

```text
G_E = [x_u <= x_v : (u,v) in E],     query x_s <= x_t.
```

There are no bottom constants or products in this **input syntax**. The values
still range over the exact C081 bottom/product tree domain. The reduction
copies the edges and distinguished indices; it never computes reachability.
Duplicate edges and isolated vertices do not affect the argument.

**Theorem.** A directed path from s to t, allowing the zero-length path,
exists iff G_E entails x_s <= x_t. This holds separately for arbitrary,
regular and finite tree valuations.

If such a path exists, apply the corresponding premise inequalities in order.
Transitivity gives the query; when s=t, reflexivity gives it without a premise.
This direction is valid in every one of the three tree domains.

For the converse, suppose t is not reachable from s. In the proof, let R be
the set reachable from s. Assign the finite root-only product tree
`P=bottom*bottom` to x_v when v is in R, and bottom otherwise. For an edge
u->v, if u is in R then v is in R, so its inequality is P<=P. If u is not
in R, its left value is bottom, which is below either possible right value.
Thus every premise holds. But s is in R and t is not; the query would require
P<=bottom, which fails at the empty address. Both values are finite, hence
regular and arbitrary as well. This is a countervaluation in each domain.
Reachability is used only to prove the countervaluation exists; it is not
computed by the reduction.

The domain contains at least these two ordered distinct values. This does
not transfer C081's general decidability theorem to finite trees: only this
variable-only sublanguage has the same reachability characterization there.

## Encoding and resource claim

Use the standard explicit-vertex graph encoding for directed s-t reachability,
so n is at most the input length up to a fixed encoding factor. A logspace
transducer copies each edge as one variable inequality and writes the two
query indices. Counters and endpoint indices need O(log n) bits; the output
has O((n+|E|) log(n+1)) bits with explicit declarations, or less if the target
stores n and index pairs directly. It is a polynomial-size output and the
transducer needs logarithmic work space. No reachability oracle or tree
construction occurs in this translation.

The imported result is the standard **PATH is NL-complete under logspace
many-one reductions** theorem. Primary teaching source: Michael Sipser,
MIT 18.404J (Fall 2020), [Lecture 20: L and NL, NL = coNL](https://ocw.mit.edu/courses/18-404j-theory-of-computation-fall-2020/resources/lecture-20-l-and-nl-nl-conl/).
That lecture explicitly introduces logspace transducers/reducibility and proves
the PATH completeness theorem. Source checked 2026-09-20.

Composing its reductions with the exact map above proves **NL-hardness of full
C081 entailment**, already on variable-only inequalities. The same modest
lower bound holds for finite- and regular-tree entailment by the explicit
finite countervaluation. It supplies no PSPACE-hardness, superpolynomial
lower bound, or useful lower bound for the current implementation's observed
running time. This is a routine inherited order-theoretic lower bound, not a
novelty claim about the new terminal construction.

## Relation to the other bounds

The [complete input-resource account](2026-09-20-c081-input-complexity.md)
gives a much larger upper bound for a specified reference decision algorithm.
The gap is large and no tight complexity class is claimed. Earlier statements
that no lower bound was transferred describe their original checkpoints;
C083 supplies this modest one. The proposed transfer of NP99 PSPACE-hardness
still needs a separate reduction preserving the exact tree domain and
bottom/denial semantics. The existing guarded NP99 map goes in the other
direction and gives an upper bound only for inputs without bottom constants.

## Independent review

A separate researcher derived the two directions from the exact variable-only
problem, checked the finite countervaluation, reflexive/empty-edge cases and
logspace translation, and reported no obstruction.
[Exact argument and released scope](https://github.com/mhenglein/subtail/issues/53#issuecomment-5746374079).
The imported standard NL theorem was checked separately against the primary
source above. No Lean build, bounded graph census or timing test is claimed;
the argument covers all finite input graphs.
