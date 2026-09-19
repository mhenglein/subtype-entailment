# C030 independent review: direct terminal realization proof

Date: 2026-09-19. Workstreams: A011/A013; claim C030; coordination #37.

**Verdict: the recorded C030 construction is correct for terminal-final binary
partial deterministic automata, with arbitrary ordered flags, Bad and initial
state.** This note gives a direct same-word proof over arbitrary product-address
trees. It does not invoke the forward subtype bridge or a saturation theorem.

**Evidence level: WRITTEN PROOF + independent bounded REPRO, not LEAN.**
No C029 result, forward-decision completion, new witness bound, arbitrary-final
converse, or complexity equivalence is claimed.

## Provenance and scope

Original inspected revision: `064fc7306b679bf607b91e7d8de259823f200c62`.
Publication base: `e1e8f635f0374d5c8112c8ee25c4220fc10198be`.
GitHub comparison at publication showed that the two intervening commits changed
only `notes/prior-work/**`; the inspected C030 sources below were unchanged.

The original advisory review read `Basic.lean` and `TreeSemantics.lean` before
the realization note and derived the suffix-transport requirement and ordered
flag direction before reading the author's argument. The explicit countermodel
below was developed in that review. This publication inherits that completed
argument; its fresh replay is not a second blind mathematical review.

The owner subsequently requested publication of all findings. This contribution
adds only this note, the preserved independent checker, a replay wrapper and one
consolidated result record. Existing proof modules, definitions, original notes,
shared ledgers, indexes and workflows are unchanged. Navigation/ledger proposals
are recorded at the end for the coordinating integrator.

- [Original C030 ledger entry](../research/claims.md#c030)
- [Original terminal realization argument](2026-09-05-terminal-realization.md)
- [Independent checker](../experiments/check_c030_independent.py)
- [Replay and separate finite-set mutation checker](../experiments/replay_c030_independent.py)
- [Archived evidence, hashes and fresh publication replay](../results/c030-independent-review.json)

"Separation at exactly address w" is interpreted as membership of w in the
left queried product-node set and nonmembership in the right one. It does NOT
require w to be the only separating address.

## 1. Definitions and construction

Let Sigma = {0,1}, and let I = (Q, delta, s, Fin, G, Bad) be a finite partial
binary deterministic automaton. Write delta*(q,u) = r for a defined run.
The only extra hypothesis is

    q in Fin ==> delta(q,0) and delta(q,1) are undefined.             (T)

The initial state is an element of Q, so k = |Q| >= 1; this excludes no instance
of `Basic.Instance k`, whose `initial : Fin k` already imposes nonemptiness.
Other terminal states need not be accepting. No disjointness or safety
hypothesis is imposed on Fin, Bad, G, or s.

For a defined run of w, put n = |w|, q_i = delta*(s,w[:i]) and u_i = w[i:].
`Subtail.Basic.Witness I w` is exactly:

1. All states q_i for 0 <= i <= n are defined and not in Bad.
2. q_n belongs to Fin.
3. Whenever 0 <= i <= j <= n and u_j is a prefix of u_i, (q_i,q_j) is not in G.

The later suffix is the prefix being compared with the earlier suffix. The
start, diagonals i=j and empty suffix j=n are included. A missing transition
fails `safeCheck`; an undefined run is not a witness.

In `TreeSemantics`, a type is a prefix-closed set of its product-labelled
addresses. Bottom is the empty set, subtyping is inclusion, and

    X x Y = {epsilon} union 0X union 1Y.

The empty product-node set is the bottom tree, not a missing root. Arbitrary,
possibly infinite trees are permitted. The clauses below are inequalities,
not product equations or a finite-tree approximation.

Introduce distinct variables a_q, v_q (q in Q), and b. Use a_undef = v_undef = b
as notation only. The normalized constraint list C_I is

    b <= bottom
    a_q <= a_delta(q,0) x a_delta(q,1)             for every q
    v_delta(q,0) x v_delta(q,1) <= v_q             for q not in Fin
    a_p <= v_q                                    for (p,q) in G
    a_q <= bottom                                 for q in Bad.

Query a_s <= v_s. This is exactly `terminal_realization.realize`. There are
2k+1 variables and 1+k+(k-|Fin|)+|G|+|Bad| clauses. The construction is total and
effective on finite inputs satisfying (T), leaves the alphabet and word
unchanged, and appends no marker. Arbitrary G can contain k^2 pairs; the count
is linear in k plus the number of explicitly listed annotations, not always
linear in k alone.

A recurring consequence of (T) is:

> Every state at a proper prefix of a defined run is nonaccepting, because
> the next letter of that run uses an outgoing transition.

## 2. Always satisfiable, including infinite lower trees

For every q define

    R_q = {x : delta*(q,x) is defined and its endpoint is not in Fin}.

This set is prefix-closed. A proper prefix of such a run cannot end in Fin:
otherwise the nonempty remaining suffix would use a transition out of a final.

Assign a_q = bottom, b = bottom and v_q = R_q. Upper constraints, denials and
flag inequalities hold because all a-sets are empty. If q is nonaccepting,
epsilon belongs to R_q, satisfying the lower product's root obligation.
For delta(q,c)=r, t in R_r implies ct in R_q. An undefined child denotes b and
contributes no nodes. Therefore every lower clause holds as well.

This is an explicit model of C_I for every permitted I. The R_q may be infinite;
no assumption of finite solvability or top constructor has been introduced.

## 3. Separation at w implies Witness I w

Take any model rho of C_I with w in rho(a_s) and w not in rho(v_s).

### 3.1 Defined run and every-prefix safety

Following the upper product clauses along w yields

    u_i in rho(a_q_i)                                             (1)

at every position. At the first undefined transition it would instead force
the remaining suffix into rho(b)=empty, a contradiction. Thus the entire run
is defined. If any q_i is Bad, its denial a_q_i <= bottom contradicts (1).
This includes i=0: a bad initial state cannot have a separating word.

### 3.2 Acceptance and lower-copy transport

Every q_i with i<n is nonaccepting by (T), so all lower clauses along the run
are available. Repeated child inclusions give, for every 0 <= j <= n,

    t in rho(v_q_j) ==> w[:j] t in rho(v_s).                       (2)

If q_n were nonaccepting, its lower product would force epsilon in rho(v_q_n).
Equation (2) would then force w in rho(v_s), contrary to separation. Hence
q_n is accepting. This argument distinguishes nonaccepting terminal states
from accepting terminal states.

### 3.3 Ordered suffix flags

Suppose i<=j, u_j is a prefix of u_i, and (q_i,q_j) belongs to G. From (1) and
prefix closure, u_j belongs to rho(a_q_i). The flag clause is

    a_q_i <= v_q_j,

so u_j belongs to rho(v_q_j). Applying (2) forces w=w[:j]u_j into rho(v_s), a
contradiction. Therefore every ordered comparison required by Witness holds.
The argument works without modification for i=j, j=n, and w=epsilon.

## 4. Witness I w implies separation at the same w

Assume w is a witness, with q_i and u_i as above. We construct a genuine model
rather than invoke a summary-to-model transfer. Let Pref(u) contain all prefixes
of u, including u and epsilon.

### 4.1 Upper-copy trees

Define

    A_q = union over i with q_i=q of Pref(u_i).                     (3)
    B   = empty.

These sets are prefix-closed. If q is Bad it is not visited, so A_q is empty.
If ct belongs to A_q, then ct is a prefix of u_i for some q_i=q. Consequently
i<n, delta(q,c)=q_(i+1), and t is a prefix of u_(i+1). Thus

    ct in A_q ==> t in A_delta(q,c).

This proves all upper constraints and rules out an obligation at an undefined
child. All denials hold.

### 4.2 Flag seeds and lower-copy trees

Collect the flag-injected nodes by

    S_r = union over p with (p,r) in G of A_p.                     (4)

Each S_r is prefix-closed. Define

    V_q = R_q union
          union over all defined delta*(q,x)=r of x S_r,           (5)

where x S_r = {xt : t in S_r}, and R_q is from Section 2.

The interpretation is explicit: propagate forced nonaccepting roots along
transition paths, and propagate all flag seeds along the same paths.

### 4.3 Prefix closure

R_q is prefix-closed. For xt in x S_r, a prefix is either a proper prefix of x,
or has the form xt' for a prefix t' of t. A proper prefix of x has a nonaccepting
run endpoint by (T), and hence belongs to R_q. In the second case t' belongs
to S_r by prefix closure. Thus each V_q is a legitimate tree.

### 4.4 Satisfaction of the lower and flag constraints

For q not in Fin, epsilon is in R_q and hence V_q. For delta(q,c)=r,

    c V_r is a subset of V_q,

by prepending the transition q --c--> r both to the R_r part and to every
path x in (5). Undefined children are empty. This proves every lower clause.
If (p,r) belongs to G, then A_p is a subset of S_r, which is a subset of V_r
using the zero-length run from r. Hence all flag clauses hold.

Therefore rho(a_q)=A_q, rho(v_q)=V_q, rho(b)=B is a model of C_I.

### 4.5 Separation

Since q_0=s, w belongs to A_s. It does not belong to R_s, because its endpoint
is accepting. If w belonged to the other part of (5), write w=xt with

delta*(s,x)=r and t in S_r. For j=|x|, determinism gives r=q_j and t=u_j.
Equations (3)-(4) yield an i with (q_i,q_j) in G and u_j a prefix of u_i.
The lengths imply n-j <= n-i, hence i<=j. This is precisely a forbidden
Witness comparison, a contradiction. Thus w does not belong to V_s.

Combining Sections 3 and 4 proves, for EVERY finite binary word w,

    Witness I w <-> exists rho,
      Models C_I rho and w in rho(a_s) and w not in rho(v_s).

The model can depend on w; this does not assert one common model realizing the
whole witness language as a set difference.

## 5. Audit of saturation and the written summary argument

This section checks the old argument but is not a dependency of Sections 2-4.
In `denial_bridge.normalize`, upper products produce pop edges, lower products
produce push edges and forced roots, and leq clauses produce epsilon edges.

In W, pops start only in the a-copy; pushes end only in the v-copy; nontrivial
epsilon edges go only a -> v. A push endpoint has no pop and no epsilon route
to a pop source. No push/pop cancellation therefore adds an epsilon edge.
Existing nontrivial epsilon edges cannot compose to create further ones.

In W^rev, pops start only in v, pushes end only in a, and nontrivial epsilon
edges go v -> a. The same argument applies. Shared b does not invalidate it:
b has no outgoing pop or nontrivial epsilon edge in the relevant cancellation
position. It is incorrect to regard b as a third copy carrying new pop paths.

For a defined run on u ending at q, the two saturated subsets are exactly

    Bhat(u) = {a_q} union {v_r : (q,r) in G}
    Ahat(u) = {v_q} union {a_p : (p,q) in G}.

The identities include u=epsilon. Old flag attachments have no next pop edge,
so each letter discards them and acquires the endpoint's attachments. The
Ahat induction uses the lower clause at each proper-prefix state, which is
nonaccepting by (T).

Disjointness of copies gives

    Bhat(w[:i]) intersects Ahat(w[:j]) <-> (q_i,q_j) in G.

An intersection via a_q_i or via v_q_j expresses the SAME ordered flag, never
its converse. The forced roots are exactly v_q for nonaccepting q; denials are
b and a_q for bad q. On defined runs, finality and safety therefore match.

At the FIRST undefined transition, Bhat reaches b. On the next letter it can
become empty. The earlier prefix must still disqualify the word. An endpoint-only
denial check would be unsound; every-prefix checking is essential. The direct
proof detects the same failure by upper-copy propagation into the empty b-tree.

Forced v-roots propagate only to v-variables; they cannot reach a denial.
The explicit model in Section 2 independently establishes satisfiability, so
this saturation observation is not an unproved satisfiability transfer.

The audited implementation here is the older `denial_bridge.py`. This note
does not identify its concrete summary state space with the later Lean
`SummaryAutomaton.summaryInstance`, and does not certify that Python code via
the latter's theorem. No forward bridge theorem is used to finish C030 here.

## 6. Boundary cases and explicit examples

For w=epsilon, the conditions reduce to s in Fin, s not in Bad and (s,s) not in
G. A nonfinal s forces the v_s root, a bad s makes a_s empty, and a diagonal
flag gives a_s<=v_s. No additional assumption on the initial state is needed.
A later diagonal uses i=j in Section 3.3. A flag into the final state uses
j=n, since the empty suffix is a prefix of every suffix.

Both accepting and nonaccepting terminal states have a_q<=b x b. Only a
NONACCEPTING terminal has b x b<=v_q, which forces its lower-copy root and
prevents separation at such an endpoint. Flags may still force a final's
v-root, exactly as the witness comparisons require.

The executable named corpus contains all of the following. Unspecified
transitions are undefined. `one_edge` is 0 --0--> 1 with final {1}.

| Fixture | Word | Witness/separation |
|---|---|---|
| One terminal accepting state, no annotations | epsilon | yes |
| One terminal nonaccepting state | epsilon | no |
| Bad initial accepting state | epsilon | no |
| Diagonally flagged initial accepting state | epsilon | no |
| one_edge with G={(0,1)} | 0 | no, empty-suffix flag |
| one_edge with G={(1,0)} | 0 | yes, orientation preserved |
| one_edge, first transition undefined | 11 | no |
| one_edge with no accepting states | 0 | no |
| one_edge with Bad={1} | 0 | no |
| 0 --0--> 1 --0--> 2, final {2}, Bad={1} | 00 | no, proper-prefix denial |
| 1 --0--> 0, start 1, final {0} | 0 | yes |
| 0 --0--> 0, 0 --1--> 1, final {1} | 0001 | yes; infinite lower tree |
| one_edge plus unreachable bad state 2, G={(2,2),(2,1)} | 0 | yes |
| Four-state example below, proper agreement | 0101 | no |
| Same four-state example, agreement avoided | 01001 | yes |
| 0 --0--> 0, 0 --1--> 1, final {1}; repeated returns | 001 | yes |

The four-state proper-suffix example has transitions

    0: (0,1), 1: (2,undefined), 2: (2,3), 3: (undefined,undefined)
    start=0, Fin={3}, G={(0,1)}, Bad=empty.

The preserved JSON records each fixture's actual failed model check when its
word is negative. Such failure alone is not an all-model NO certificate;
Section 3 supplies the universal implication.

### Infinite trees are genuinely required in a small case

For s --0--> s and s --1--> f with final {f} and no annotations, choose

    V_s={0^m : m>=0}, V_f=B=empty.

The lower clause v_s x v_f<=v_s forces epsilon and then every 0^m into v_s in
EVERY model, so no finite-tree model exists. The system is still satisfiable.
For w=0001, (3) supplies finite upper-copy trees and w is absent from V_s.
This is a separating model over the required arbitrary-tree semantics.

### Terminality cannot simply be removed

This is a hypothesis-mutation example, NOT a C030 counterexample. Let

    s --0--> t, Fin={s}, G=Bad=empty,

where t is nonaccepting and terminal. Word 0 is not accepted, but applying the
construction outside its scope admits

    A_s={epsilon,0}, A_t={epsilon}, V_s=empty, V_t={epsilon}, B=empty.

These finite prefix-closed sets satisfy all four generated clauses and
separate at 0. The missing lower clause at accepting s stops backward transport
of the forced root at t. The replay wrapper validates these sets by direct
finite-set inclusion, independently of the regular-language model machinery.
The preserved original checker contains a historical comment mentioning a
one-state mutation; this actual archived and replayed example has TWO states.

## 7. Reproducible evidence and limits

The independent checker imports no repository implementation. It separately
implements the literal word predicate, the clause construction and (3)-(5).
Its derivative states represent unions of V_q residual languages and finitely
many suffix singleton languages. Inclusion and prefix closure exhaust finite
derivative graphs, so the semantic tree checks have no depth cutoff.

| Corpus | Input occurrences | Query words | Positive words |
|---|---:|---:|---:|
| All one-state terminal-final inputs; length <=4 | 20 | 620 | 1 |
| All two-state terminal-final inputs; length <=3 | 12,800 | 192,000 | 360 |
| Seeded inputs with 3-6 states; length <=5 | 120 | 7,560 | 48 |
| Named fixtures | 16 | 16 | 7 |
| Total | 12,956 | 200,196 | 416 |

The exhaustive encodings include every partial transition table, permitted
final set, ordered G, Bad set and initial state. For k states there are
((k+1)^2+1)^k choices of transition rows and terminal-final indicators,
2^(k*k) flag relations, 2^k bad sets and k starts; these yield 20 and 12,800
inputs for k=1,2. Named fixtures may duplicate other inputs. Counts are input
occurrences, not globally distinct automata.

Every input also passed its exact baseline satisfiability-model check.
All 200,196 word comparisons and the separate mutation fixture passed again
during publication. The replay matched every archived semantic field, ignoring
only elapsed times. This is a fresh execution of the SAME checker, not a new
independent implementation. The checker bytes are preserved exactly with SHA256
`6c35e4e518f3db0e432ca0c66b58d7164e222e5cd24b06521b34229dfe220146`.
All eight original artifact checksums were verified before consolidation.

Fresh replay: Python 3.13.5, Linux x86_64, standard library, seed 2026091930.
The wrapper uses a 120-second limit per suite subprocess and no explicit memory
ceiling. The original run's elapsed times remain under `archived_results`;
fresh timings and environment are separate under `publication_replay`.
No timed-out or partial run is represented as PASS or NO.

From the repository root, with Python 3.10 or newer:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/replay_c030_independent.py \
  --output /tmp/c030-independent-replay.json
```

The wrapper refuses to overwrite its tracked baseline record, requires
assertions enabled and checks the preserved checker hash. To reproduce the
original suites individually, use scratch output paths:

```sh
python3 experiments/check_c030_independent.py --suite fixtures --output /tmp/c030-fixtures.json
python3 experiments/check_c030_independent.py --suite k1 --length 4 --output /tmp/c030-k1.json
python3 experiments/check_c030_independent.py --suite k2 --length 3 --output /tmp/c030-k2.json
python3 experiments/check_c030_independent.py --suite random --length 5 --output /tmp/c030-random.json
```

Do not run the original assertion-based checker with Python -O. The added replay
wrapper is a publication convenience, not part of the mathematical reduction.

E021 was source-inspected, NOT rerun. Its recorded output reports 166 inputs,
10,458 word comparisons, 2,985 exact canonical-model checks, 83,664 budget
predicate comparisons, 2,416 summary identities and 1,023 additional terminal
restriction words. These are historical repository results, not this replay.

Also NOT RUN here: Lean compilation/kernel replay, the repository budget
differential, and repository-wide index/navigation/CI checks. No theorem or
implementation has been promoted to Lean status. Tests concern a bounded
input/word corpus; the all-word result rests on Sections 2-4, not extrapolation.

## 8. Dependencies, budget qualification and converse consequence

| Dependency | Exact role |
|---|---|
| `lean/Subtail/Basic.lean` | `Instance`, `Witness`, `Agrees`, undefined/safe/final conventions |
| `lean/Subtail/TreeSemantics.lean` | `Tree`, `PrefixClosed`, `product`, `bottom`, `Below`, `Constraint`, `Models`, `Entails`, separating semantics |
| `experiments/terminal_realization.py` | Confirms the recorded construction and counts; not a proof dependency |
| `experiments/denial_bridge.py` | Source of the saturation algorithm inspected in Section 5 only |
| `experiments/border_lab.py` | Word and budget predicate definitions compared with the summary identities |
| `experiments/check_terminal_realization.py`, `results/terminal-realization.json` | Historical E021 source/output inspected, not rerun |
| `research/claims.md`, `research/TERMINAL.md`, original realization note | Statement, scope and recorded proof status |
| Elementary word/run reasoning | Prefix closure, determinism, path concatenation and finite induction in the direct proof |

No forward subtype bridge, pushdown saturation theorem, canonical-model theorem,
C029, C031, decision algorithm, finite-tree assumption or witness bound is used
in the direct realization proof. In particular there is no hidden unproved
mapping from this Python summary construction to a Lean summary theorem.

The ledger also claims preservation of budgets. Equality of witness languages
alone does not imply equality of arbitrary budget approximations. Here Section 5
supplies the stronger pointwise identification of admissibility and every
ordered suffix comparison, and the word is unchanged. Thus the inspected
`necessary(I,w,L,D)` and `sufficient(I,w,L,D)` predicates agree for every fixed
w,L,D; their minimal successful budgets agree as well. This is a written
consequence of those identities; no fresh budget differential is claimed.

Quantifying the proved equivalence over finite w gives

    (exists w, Witness I w) <-> not Entails C_I a_s v_s.

`TreeSemantics.not_entails_iff_separating` expresses exactly this arbitrary-tree
non-entailment semantics; the consequence also follows immediately by unfolding
entailment. This is a converse reduction to NON-entailment, not an automatic
complexity equivalence with entailment or with the forward compiler.

## 9. Handoff and follow-up proposals (not reservations)

The highest-value C030-specific next step is a small, separately owned Lean
formalization of the direct argument, only if checked certification of the
converse is wanted. Agree a module and interfaces with #37 first. Suggested
proof order: define C_I on 2k+1 variables; prove proper-prefix nonfinality and
lower-copy transport; prove the explicit R/A/S/V sets prefix-closed and satisfy
all clauses; prove same-word separation equivalence and satisfiability; derive
the non-entailment corollary. Audit dependency closures and replay the theorem
against the named empty/diagonal/undefined/infinite-tree fixtures. These are
proposed obligations, not declarations that have been written or compiled.

Keep this OPTIONAL converse certification outside the forward-decision critical
path. At the inspected publication base, STATE identifies C029, finite-expression
normalization and final executable composition as forward obligations; C030 is
not a prerequisite for them. C080's quantitative bound and performance remain
separate. Consult current issues before taking any of those already active tasks.

A useful later executable cross-check would feed the preserved independent
fixtures through the actual `terminal_realization.realize` implementation and
compare all emitted clauses and, where feasible, native separation checks.
Keep that differential distinct from certifying this mathematical proof or from
replaying E021; neither is claimed in this publication.

Proposed integration-only navigation edits, not applied by this worker:

- C030 ledger: add this note and result as an independent direct arbitrary-tree
  proof plus fresh bounded evidence; retain WRITTEN PROOF + REPRO, not LEAN.
- Original realization note: link this direct proof as an alternative that does
  not invoke the forward bridge, without rewriting the historical argument.
- Experiments registry: link the checker/replay and exact 200,196-word scope;
  distinguish it from E021 and retain all NOT RUN qualifications.

Do not mark C031, C029, C080 or Problem 1.7 complete on the strength of this
review. No new E/C/A identifier is allocated. The PR/coordination handoff names
the actual pushed commit and releases this publication session's four new paths;
no background work or continuing file reservation is implied.
