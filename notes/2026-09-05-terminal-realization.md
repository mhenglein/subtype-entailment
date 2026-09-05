# Terminal realization, exact converse, and a nonregular subtype language

Date: 2026-09-05. Continues A011/A013 at commit 7edc9f7.

**Status: WRITTEN PROOF + REPRO. Not Lean-checked.** No unrestricted decision
is claimed. The subtype semantics are arbitrary, possibly infinite trees.
The interpretation of summary witnesses as separating paths uses the existing
audited forward bridge. No literature-priority claim is made.

## 1. Every terminal-final abstract instance is realizable (C030)

Let I=(Q,delta,s,Fin,G,Bad) be a finite partial deterministic binary automaton.
Assume every f in Fin is terminal: delta(f,0)=delta(f,1)=undefined.
Other states may also be terminal. G, Bad, s, and Fin are otherwise arbitrary.
Write k=|Q|. Construct 2k+1 subtype variables:

    a_q, v_q (q in Q), and b.

Put b<=bottom. For every q add

    a_q <= A(delta(q,0)) x A(delta(q,1)),

where A(r)=a_r for defined r and A(undefined)=b. For every q NOT in Fin add

    V(delta(q,0)) x V(delta(q,1)) <= v_q,

where V(r)=v_r and V(undefined)=b. Do not add a lower product for final q.
For each (p,q) in G add a_p<=v_q. For each q in Bad add a_q<=bottom.
Ask whether a_s<=v_s.

**Theorem.** The constructed constraint system is satisfiable, and for every
binary word w:

    w separates a_s from v_s in some model iff w is a witness of I.

The word is unchanged. The construction does not append a marker, change the
alphabet, or alter the equality comparisons. It uses

    2k+1 variables and 1+k+(k-|Fin|)+|G|+|Bad| constraints.

### Proof: saturation has no hidden cross-copy edges

In W, upper products provide pop edges only from the a-copy. Lower products
provide push edges only into the v-copy. The only variable inequalities are
a_p -> v_q. There are no pop edges from a v-variable, and none from b.
Consequently a push cannot be followed by a pop-summary path consuming its
pushed letter; pop-summary saturation creates no new epsilon edges.

In W^rev, pops start only in the v-copy, pushes end only in the a-copy, and
epsilon edges go v_q -> a_p. Again there are no pop edges from a-variables
or b, so saturation creates no additional epsilon edges.

For each word u having a defined I-run ending at q, the two saturated subsets
are therefore exactly

    B(u) = {a_q} union {v_r : (q,r) in G},
    A(u) = {v_q} union {a_p : (p,q) in G}.

This includes u=epsilon. The identities follow by induction on u: a copied
flag target has no next letter edge, so each step discards the old epsilon
attachments and acquires precisely the new state's attachments.

For two defined prefixes ending in p and q, disjointness of the copies gives

    B(prefix_i) intersects A(prefix_j) iff (p,q) in G.

There are exactly two ways to intersect: a_p is in the second set, or v_q is
in the first. Both express the SAME ordered flag, not its converse.

### Finality, undefined transitions, and safety

The forced-root variables are exactly {v_q : q not in Fin}. Thus, on defined
runs, A(u) avoids forced roots exactly when q is final.
The denial variables are {b} union {a_q : q in Bad}. Hence B(u) meets a denial
exactly when the original state q is Bad. An undefined transition sends the
upper copy to b; that prefix is unsafe, regardless of what later subsets do.
Every-prefix checking is essential here.

Forced v-roots can reach only v-variables under W: their pushes stay in that
copy, and no epsilon edge leaves it. They cannot reach b or any denied
upper variable. This proves satisfiability. Equivalently, take every a_q and
b to be bottom, and take the least lower-product solution for the v-copy;
it may be infinite, which is permitted.

The final predicate, every-prefix safety, and every ordered suffix flag are
therefore identical to I's predicates. The audited forward bridge finishes
the separating-path statement. The same argument preserves Necessary(L,D)
and Sufficient(L,D) on every word, for every fixed L,D; their tests use the
same admissibility and flagged suffix comparisons. In particular minimum
successful instance budgets are preserved.

### Why terminality is necessary for THIS construction

If an original final state had an outgoing transition, its lower-copy pop
summary would stop there, because no forced lower product was added at that
state. Adding one would make that state non-final under F. Thus this is a
converse for terminal-final automata, not the missing arbitrary-annotation
converse for unrestricted BorderAvoid.

## 2. This terminal decision problem captures the remaining subtype problem (C031)

For an absorbing instance, call a state safe if it is neither Bad nor
diagonal-flagged. Remove transitions into unsafe states. Keep as accepting
only the original safe final states with no remaining outgoing transition.
This effective terminal restriction J has exactly the original safe terminal
witnesses. Incoming flags and the original start remain unchanged.

C029 decides existence of an infinitely extendable witness. If its exact
answer is positive, the original subtype entailment fails. Otherwise any
remaining witness has no infinite safe future. Its reachable safe graph is
acyclic; safe extension preserves witnesshood by absorption. Extending it
to a terminal vertex takes at most k-1 letters and yields a witness of J.
Conversely any witness of J is a witness of the original instance.

Thus a decider for terminal-final BorderAvoid, combined with C029 and the
existing forward bridge, decides the full normalized subtype problem.
C030 gives the reverse reduction. **Their decidability is equivalent**, with
the qualifications that C029 and the forward bridge retain their recorded
proof statuses. This is NOT a complexity equivalence: the reductions and
C029 may substantially increase state counts and runtime.

The consequence for A013 is important: shared B/A/D structure cannot rule
out arbitrary terminal abstract instances. They all have linear-size subtype
realizations. The useful remaining target is a terminal-automaton theorem,
not an unsupported claim that only easier terminal flags arise from subtypes.

## 3. A nine-variable terminal separating language is nonregular (C032)

Use the following four-state abstract instance:

| q | 0 | 1 |
|---|---|---|
| 0 | 0 | 1 |
| 1 | 2 | undefined |
| 2 | 2 | 3 |
| 3 | undefined | undefined |

Start=0, Fin={3}, Bad=empty, G={(0,1)}. Its accepted words are

    0^m 1 0^(n+1) 1,  m,n >= 0.

State 1 occurs exactly once, before the second zero block. Its suffix is
0^(n+1)1. Earlier state-0 positions run through the first zero block, including
the position before its following 1. Such a suffix occurs from one of them
iff n+1<=m. There are no other flags. Therefore the exact witness language is

    L = {0^m 1 0^(n+1) 1 : m,n>=0 and n>=m}.

All witnesses terminate at state 3. They have no positive-length safe future.

Applying C030 gives variables a0,a1,a2,a3,v0,v1,v2,v3,b and these constraints:

    b <= bottom
    a0 <= a0 x a1          v0 x v1 <= v0
    a1 <= a2 x b           v2 x b  <= v1
    a2 <= a2 x a3          v2 x v3 <= v2
    a3 <= b x b
    a0 <= v1

The query is a0<=v0. This always-satisfiable construction has separating
language exactly L.

**Nonregularity proof.** For any integers a<b, append the suffix
1 0^(a+1) 1 to the two prefixes 0^a and 0^b. The first resulting word is in
L (n=m=a); the second is not (n=a<b=m). Thus every two members of the infinite
family {0^a:a>=0} have different right residual languages. A finite automaton
cannot recognize L.

This refutes a finite automaton representing ALL terminal separating words,
not a finite procedure deciding whether at least one exists. Here existence
is immediate, and the exact two-counter inequality is decidable. It also
illustrates why unbounded counters can be useful even when the underlying
candidate graph has only simple-cycle recurrent components.

## 4. Evidence and limitations

E021: `python3 experiments/check_terminal_realization.py` checks 166 instances,
10,458 words, 83,664 necessary/sufficient comparisons, 2,416 explicit summary
identities, and 2,985 exact canonical regular-model checks. It also realizes
the earlier terminal obstruction and checks all 1,023 words through length 9.

E022: `python3 experiments/check_terminal_nonregular.py` checks all 2,047 words
through length 10, 266 exact canonical models, 441 exponent pairs, and 465
finite representatives of the residual-language argument.

The all-length claims follow from the written arguments, not sampling.
No Lean formalization, arbitrary BorderAvoid converse, general witness bound,
or unrestricted decision is claimed.
