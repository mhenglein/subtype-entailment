# Three-way regular-middle cut certificates

Date: 2026-09-08. Continues the regular-decoration barrier by extracting its
all-length NO proof into a reusable finite certificate rule.

**Status: written proof + exact finite verifier; independent mathematical review pending; not Lean-checked. This is a sufficient NO rule, not a complete calculus and not a solution of Problem 1.7.**

## 1. Rule

Fix distinct binary letters `a,b`. Let `M` be a regular language such that every
nonempty word of `M` begins with `a`. Suppose the complete boundary-normalized
candidate language is exactly

    a^n b u a^m b a

with `n>=0`, `m>=1`, and `u in M`.

No stabilization of the unary `a`-runs is required. Let

    P = { delta(s0,a^d) : d>=1 }

be the finite positive leading `a`-orbit from the start state `s0`. Require that
reading `b` from `s0` and every state of P reaches one common anchor `q0`.

The accepted middle words may induce finitely many effects

    E = { delta(q0,u) : u in M }.

For each `q in E`, let

    R_q = { delta(q,a^d) : d>=1 }

be its finite positive trailing `a`-orbit. Require every positive power above to
be defined, and for every `r in R_q` require that `r --b a--> final`.

Finally require the finite flag families

    (s0,r)   for every q in E and r in R_q,
    (s0,q)   for every q in E,
    (p,q)    for every p in P and q in E.

Then the candidate language has no witness.

This strictly generalizes the earlier stable-state rule: finite unary orbits may
contain preperiods and cycles, so the certificate already handles all eventual
residue classes of the two unary parameters.

## 2. All-length proof

Write a candidate as

    w = a^n b u a^m b a

and put `q=delta(q0,u)`. Since `m>=1` and every nonempty `u` begins with `a`,
the symbol immediately after the first `b` is always `a`: if `u` is nonempty
this is its first symbol; if `u` is empty it is the first symbol of `a^m`.

There are three exhaustive arithmetic cases.

### Case n < m

Put `d=m-n>=1`. Use source cut `i=0`. In the trailing `a^m` block choose the
target cut after exactly d trailing `a`s. The target state is

    r = delta(q,a^d) in R_q,

and the target suffix and source suffix both begin `a^n b a`. The required flag
`(s0,r)` witnesses a forbidden prefix agreement.

### Case n = m

Use source cut `i=0` and target cut at the start of the trailing `a^m` block.
Both suffixes begin `a^n b a`; their states are `(s0,q)`, which is flagged.

### Case n > m

Put `d=n-m>=1`. Use source cut `i=d`, inside the leading `a` block, and target
cut at the start of the trailing `a^m` block. The source state is

    p = delta(s0,a^d) in P,

while the target state is q. Both suffixes begin `a^m b a`, and the required
flag `(p,q)` witnesses the violation.

The selected p, q, and r vary with the unary residues and the regular middle,
but all lie in finite effect/orbit sets checked by the verifier. Thus every
candidate is bad. QED.

## 3. Why the proof object is finite

`experiments/three_way_cut_certificate.py` verifies every premise effectively.

### Exact candidate-language equality

The family `a* b M a+ b a` is represented by an epsilon-NFA formed by
concatenating the regular pieces. The verifier explores the product of the
terminal candidate DFA with epsilon-closed subsets of this NFA. A reachable
acceptance disagreement gives a concrete symmetric-difference word. Exhaustion
proves exact language equality for all lengths.

### Middle first-letter condition

The verifier asks whether the middle DFA has any accepting path after consuming
`b` as its first symbol. This is ordinary finite reachability.

### Finite unary orbits and middle effects

Repeated application of one deterministic letter on finitely many states has a
finite orbit. The verifier follows `a` until a state repeats; encountering an
undefined transition invalidates the certificate. It separately explores the
product of the middle DFA with the terminal automaton from `(middle.start,q0)`
to enumerate E exactly. Thus all residue-sensitive state possibilities are
finite and explicit.

For each q in E and r in R_q it checks the terminal `ba` suffix, and it checks
the complete finite flag families above. Hence `VERIFIED_NO` is an all-language
finite certificate verdict. Bounded enumeration is used only as an independent
regression of the implementation.

## 4. Two strict examples

### Six-state regular-marking barrier

For the original barrier use `a=0`, `b=1` and `M=(0+11)*`. Here the leading
orbit is `{1}`, E is `{2}`, and the trailing orbit is `{3}`. The required flags
reduce to exactly `(0,3), (0,2), (1,2)`.

### Periodic/multi-effect fixture

The checker also uses the exact candidate language

    0* 1 (epsilon | 011) 0+ 1 0.

Its middle has two terminal-automaton effects, and one effect has positive
trailing orbit `2 -> 3 -> 3`. Therefore the former one-step-stabilization rule
is inapplicable, while the orbit rule verifies NO. This is a strict regression
for both finite middle effects and nontrivial unary preperiods.

## 5. Significance and limit

This is the first installed NO certificate in this continuation whose
termination does **not** come from a bounded comparison length, bounded gap,
bounded marker count, or candidate-covering finite decoration. It handles an
arbitrary recurrent regular middle, finitely many middle effects, and arbitrary
finite unary eventual periodicity while choosing violating cuts by the affine
differences `m-n` and `n-m`.

So the rule is already a small **affine/residue cut-selector calculus**:

- Presburger partition: `n<m`, `n=m`, `n>m`;
- affine selectors: 0, `m-n`, `n-m`;
- finite residues: encoded by unary transition orbits;
- arbitrary regular middle: summarized by finitely many transition effects.

Completeness is not claimed. The natural next generalization is to replace
single letters `a` by fixed periodic words and then allow several parameterized
blocks. A016's fixed-skeleton Presburger compiler already supplies exact
state/letter formulas for repeated fixed words; the remaining interface problem
is how to let affine selectors cross arbitrary recurrent regular pieces without
expanding those pieces into fixed words.

If every terminal NO instance admitted a finite affine/residue selector cover,
dovetailing its verifier with positive witness enumeration would decide terminal
BorderAvoid. The regular-decoration barrier does not block this route because
the certificate may select different violations in different arithmetic cells.

## 6. Reproduction

Run

    python3 experiments/check_three_way_cut_certificate.py

The checker verifies the infinite-language barrier certificate exactly,
independently compares it with the family parser on all 32,767 binary words
through length 14, confirms required-flag sensitivity, rejects an enlarged
middle language, and separately verifies the strict periodic/multi-effect
fixture with another 32,767 bounded language comparisons.

Implementation: `experiments/three_way_cut_certificate.py`.
Checker: `experiments/check_three_way_cut_certificate.py`.
Recorded result: `results/three-way-cut-certificate.json`.
