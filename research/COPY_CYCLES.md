# Unbounded copy cycles and length-series limits

Date: 2026-09-10. Base: `2e431ff3d74d3ab1268866f86e24fd835ffe7fda`.
Independent mathematical review pending; written proofs with reproducible tests,
not Lean verification. No solution of unrestricted Problem 1.7 is claimed.

## Canonical claims

<a id="c069"></a>
### C069 - Nonsemilinear witness lengths and nonrational raw counts

An explicit eleven-state binary terminal automaton with three flags has exact
witness language `{(1^(2n)00)^m 01 1^(2n)00 : n,m>=1}`. At bit length 2N+2 it
has exactly tau(N)-2 witnesses for N>=2, with zero in the remaining cases.
Thus its length support encodes the composite integers and is not ultimately
periodic or semilinear; its length-counting series is not rational. Removing
one of the flags still leaves a nonrational counting series. Retaining only
(2,4) also gives a nonrational RAW witness-counting series, through an explicit
sum with infinitely many distinct poles.

**Scope:** these refute a rational/semilinear description of every full witness
language. They do not refute C065's counting AFTER return-free normalization,
C067's source-capture decision, any computable existential witness bound, or
existence-preserving finite symbolic covers. The three-flag fixed instance
has a ten-letter witness and an always-satisfiable 23-variable C030 image.
Multiplication in length projection does not by itself encode an undecidable
arithmetic problem.

**Status:** WRITTEN PROOF + REPRO. [Full argument and tables](../notes/2026-09-10-copy-cycles-and-length-series.md).

<a id="c070"></a>
### C070 - Exact acceleration of one unchanged shared-block cycle

An explicit thirteen-state, eight-flag binary terminal instance has witnesses
exactly `{B^m 01 B : B=E(u)00, u nonempty, m>=1}`, with E(0)=10,E(1)=11.
Every such B is unbordered/primitive, so the unbounded repetition can be
represented exactly by `UB=BU`, `U nonempty`, and `W=U01B`. The block is one
SHARED variable, not independent choices at each occurrence.

For a supplied data DFA L with ell states and whole-output DFA D with d states,
nonemptiness of this family subject to u in L and W in D is decided by a finite
action-product and positive-power-orbit search. A coarse search-state bound is
`2*ell*(d+1)^d`; a positive output has length at most
`(d+1)*(4*ell*(d+1)^d+2)+2`. No external SMT backend is required.

**Scope:** a complete supplied-family decision and a concrete copy-only cycle
acceleration, not a decomposition theorem for arbitrary inputs. Generic
PCP-capable template iteration is not accelerated by this construction.
Practical caps are UNKNOWN. The returned word need not be shortest.

**Status:** WRITTEN PROOF + REPRO. [Proof](../notes/2026-09-10-copy-cycles-and-length-series.md),
[implementation](../experiments/copy_cycle.py),
[route and remaining coverage obligation](../notes/2026-09-10-copy-cycle-route-outline.md).

## Canonical experiment

<a id="e044"></a>
### E044 - Copy-cycle language, counting and filter checks

**Command:** `python3 experiments/check_copy_cycle.py`.

The deterministic run records 131,071 raw general-data words and 1,048,568
unary word/annotation comparisons; 10,926 completely enumerated accepted unary
candidates through length 42; exact coefficient comparisons under three, two
and one flags; 500 divisor coefficients; and 12,282 commutation checks.
313 complete filter oracles comprise all 64 total two-state binary filters,
136 modular filters, 90 finite dictionary/data filters and 23 exact lengths.
They return 196 YES and 117 NO. Eight exact canonical-model paths, the
single-target one-visit counterexample, and deliberate cap/guard cases are
retained. Finite tests support implementation; the all-length claims are proved
separately.

[Checker](../experiments/check_copy_cycle.py), [saved result](../results/copy-cycle.json).

## Current implication

C067 has already removed the old single-source pumping obligation. This
continuation shows why simply broadening full-language rational counting is
not the right replacement for multi-source synthesis. One fixed shared-block
cycle can nevertheless be summarized and filtered exactly. The general route
still needs an effective existence-preserving cover or a terminating treatment
of cycles whose shared word parameters change. No such theorem is supplied.
