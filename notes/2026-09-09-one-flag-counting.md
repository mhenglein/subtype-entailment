# Exact terminal one-flag existence by rational length counting

Date: 2026-09-09. Base main: `05b20ee73841d0e7105a44beb761e553a7081a8d`.
Workstreams A008/A017, with A012 implications. Proposed C065-C066 / E042.

**Status: written proof plus reproduced finite checks; independent mathematical
review pending, not Lean-checked.** This decides every binary terminal instance
with at most one forbidden ordered pair. It does NOT decide arbitrary multiple
flags, or unrestricted Problem 1.7. No literature-priority claim is made.

## 1. Latest work read, and the end-to-end route

The September 8 consolidation and repaired supplements retain the terminal
realization at its recorded written/audited level. The current plan selects
existence-preserving normalization and keeps an opposing undecidability route.
The single-source shape note leaves a root/new-border obligation. Its separate
primitivity correction removes the unnecessary primitivity requirement, and
the overlap audit repairs alignment of selected equalities but explicitly does
not prove full witness preservation. The semantic-tail/regular-decoration
barrier blocks a much broader candidate-preserving marker strategy. The
arithmetic cut-selector and recovered flag-inference notes give other exact
negative subroutines, not a completeness theorem.

This attempt does not repeat those pumps. It uses terminal nonmerging to make
COUNTING forbidden periods unambiguous. A rational series then supplies a
complete zero test without requiring a regular witness language. See the
[route outline](2026-09-09-one-flag-route-outline.md). The primitive-root shape
lemmas, corrected deletion lemma, and any unproved root bound are not premises.

## 2. Exact setting and source reduction

An instance is a finite partial deterministic binary automaton on Q, |Q|=k,
with start s, terminal accepting states F (no outgoing defined transitions),
Bad subset Q, and G subset Q x Q. A defined safe accepted word w with states
c(0),...,c(|w|) is a witness iff no i<=j has G(c(i),c(j)) and w[j:] a prefix
of w[i:]. Empty suffixes and diagonal comparisons are included.

First suppose every flag leaves one state p; write T={q:G(p,q)}. A shortest
safe accepted path avoiding p is already a witness. Otherwise any witness
visits p. Take its suffix from the LAST visit to p. That suffix has no return
to p and remains a witness: its comparisons are unchanged suffixes of the
original word. Conversely, prepend any safe simple s-to-p path with no earlier
p to such a return-free witnessing suffix. The head contains no flag source;
all flagged comparisons are precisely those within the suffix. The resulting
word is a witness. This is an existence equivalence, not preservation of every
original word or its complete agreement profile.

Implement the reduction by deleting Bad states/edges, deleting every transition
into p, taking p as the new start, and removing T from the accepting set.
The latter removes exactly the forbidden empty-suffix endpoints. If p is Bad
or p belongs to T, only the previously checked p-avoiding case can succeed.
A missing safe head or missing surviving accepted suffix gives NO. Cases with
no flags are ordinary finite reachability. Empty words are tested explicitly.

For the counting core we therefore have a k-state safe partial table, no
transition into p, terminal final states F, and internal targets T disjoint
from {p} union F. A nonempty accepted word w is bad iff it has a proper period

    1 <= d < |w|,  w[d:]=w[:|w|-d],  c(d) in T.

Unreachable/dead-end targets may be dropped. All k-state bounds below may keep
unused original states; trimming only improves them.

## 3. Uniqueness per target and bounded exponent

### Lemma 1: one target state supports at most one period

Suppose d1<d2 are periods of the same accepted w and c(d1)=c(d2)=q.
The shorter suffix w[d2:] is a prefix of w[d1:], because both are prefixes of
w. Reading w[d2:] from c(d1)=q therefore reaches the same terminal final as
from c(d2)=q, but at position d1+|w|-d2 < |w|. This contradicts continuation
of the defined accepted run. Thus the target states of distinct periods are
distinct. In particular, if T={q}, every candidate has zero or ONE bad period.

The conclusion also holds for a multi-element T when no productive safe path
connects two distinct T states: two such period positions would supply exactly
that path. This is a sufficient decidable unambiguity certificate, not a claim
that it is necessary. The implementation uses it as an optional extension.

### Lemma 2: canonical periodic parametrization

For a proper period d, let N=|w|, e=floor(N/d), r=N mod d, and

    u=w[:r], v=w[r:d].

Then v is nonempty and

    w=(uv)^e u.                                                   (1)

Conversely every such expression with v nonempty has period d=|uv| whenever
d<N. Its exponent and u,v are uniquely determined by (w,d). Consequently this
is a bijection with period INCIDENCES, not just a cover of bad words.

Along an accepted terminal run of (1), the states after (uv)^i for i=0,...,e
are distinct: a repeated state would let the remaining periodic suffix reach
the terminal final early. Therefore

    1 <= e <= k-1.                                                (2)

Qualifying (1) by c(d) in T automatically rules out the exceptional d=N case:
then e=1,u=epsilon and c(d) is final, whereas T is internal.

No primitivity hypothesis is needed. Each different period has its own unique
representation, even when uv is a proper power. This matters to counting.

## 4. Rational series for period incidences

Complete the safe partial table with an absorbing sink. Let S be the finite
transition monoid, identity 1 included, and m=|S|. Every action fixes the sink,
so

    m <= (k+1)^k.                                                 (3)

For A in S define the ordinary length series

    f_A(z) = sum_{u: action(u)=A} z^|u|.

Let M be the m by m integer matrix of the monoid automaton: its (A,B) entry
counts how many binary letters take action A to action B by right extension.
Thus entries can be 0,1,2. Starting at identity, the vector of fibre series is

    e_1 (I-z M)^(-1).

Put D(z)=det(I-z M). Then D(0)=1, deg(D)<=m, and for each A,

    f_A(z)=P_A(z)/D(z),  deg(P_A)<=m-1,                            (4)

by the adjugate formula. These are formal power series over the integers;
no analytic convergence or floating-point approximation is used.

The series counting safe accepted candidates is

    C(z)=sum_{A: A(p) in F} f_A(z).

For actions A=action(u), B=action(v), put Y=B composed with A. For exponent e
call (A,B) qualifying when

    Y(p) in T,  A(Y^e(p)) in F.                                  (5)

The sink completion makes definedness part of finality: any undefined prefix
stays in the sink and cannot accept. By (1)-(2), the series counting bad-period
incidences is exactly

    J(z) = sum_{e=1}^{k-1} sum_{(A,B) qualifying for e}
              f_A(z^(e+1)) [f_B(z^e) - 1_{B=1}].                (6)

The subtraction removes the empty v, including the case that a NONEMPTY word
has identity action; those nonempty words are retained. The exponents e+1 and
e count the actual numbers of copies of u and v, respectively. No copies of
a shared word are chosen independently.

Equation (6) is valid for an arbitrary internal T. Only the NEXT subtraction
needs unambiguity. Under Lemma 1's one-period hypothesis,

    W(z)=C(z)-J(z)                                                (7)

counts actual witnesses by length, with nonnegative integer coefficients.
It need not be the series of a regular language.

## 5. Complete zero test and explicit witness bound

For k>=2, a common denominator of (7) is

    Q(z)=product_{j=1}^k D(z^j),  Q(0)=1.

Write W(z)=P(z)/Q(z). Set

    B0=m*k*(k+1)/2.

We have deg(P)<B0. This degree claim does not assume deg(D)=m or that the
fraction is reduced. To verify it, let h=deg(D)<=m. The candidate summand's
numerator after multiplication by Q has degree at most

    (m-1) + (k(k+1)/2-1)*h <= B0-1.

A period summand for e has two numerators: P_A(z^(e+1)) of degree at most
(e+1)(m-1), and P_B(z^e)-1_{B=1} D(z^e) of degree at most e*m. Multiplying by
the remaining factors gives degree at most

    (e+1)(m-1) + e*m + (k(k+1)/2-(2e+1))*h
       <= B0-e-1 < B0.

Here k(k+1)/2 >= 2e+1 for 1<=e<=k-1 and k>=2. The empty/vacuous and k=1
cases are handled directly by finite reachability.

Because Q(0)=1, P and W have the same first nonzero coefficient index. Thus

    W is identically zero iff its first B0 coefficients are zero.         (8)

When W is a witness-counting series, (8) is an EXACT existence decision and
not a guessed search cutoff. A positive return-free suffix has length <B0.
Adding the safe simple head of length <=k-1 proves the explicit all-input
one-flag bound

    F_one(k) = [k(k+1)/2]*(k+1)^k + k-2,  k>=2,                 (9)
    F_one(1)=0.

This bound is generous. No optimality or polynomial bound is asserted.

### Theorem C065

Every finite binary terminal BorderAvoid instance with at most one forbidden
ordered state pair has an effective terminating decision procedure. A positive
k-state instance has a witness bounded by (9). Bad states, multiple terminal
finals, arbitrary initial/flag-source states, diagonal flags and final-column
flags are included through Section 2. The same counting method decides the
single-source class certified to have mutually unreachable distinct internal
targets, with the same bound.

The implementation enumerates the finite monoid and computes exact integer
coefficients directly; it need not construct symbolic determinants. A positive
coefficient is followed by a finite accepted-path search at that exact length
and both existing word predicates validate the reconstruction. Its explicit
monoid, coefficient, arithmetic-work and reconstruction caps return UNKNOWN.
Passing None disables each cap. No performance claim for huge monoids is made.

This theorem is independent of a full single-source coloured-Anderson bound.
It is not a theorem about every annotation with several interacting targets,
and it does not supply a decision for arbitrary normalized subtype constraints.
The existing C030 construction transfers the decidable subclass to its exact
subtype image at C030's recorded proof status, not to all subtype inputs.

## 6. Examples and a rigorous boundary of the counting argument

An infinite negative example has table

    ((-1,1),(1,2),(-1,-1)), start=0, final={2}, G={(0,1)}.

Its candidates are 1 0* 1 and every candidate has its unique flagged one-letter
border. C(z)=J(z)=z^2/(1-z). The exact checker exhausts 42 coefficients for its
seven-element monoid and returns NO.

The other agent's five-state extremal table

    ((-1,1),(-1,2),(-1,3),(2,4),(-1,-1)), G={(0,1)}

has candidates 111(01)*1. Only 1111 is bad, so

    W(z)=z^6/(1-z^2).

The checker returns 111011, the shortest witness, at length six. The recorded
six-state extremal table similarly returns 00001000 at length eight.

A five-state example with G={(0,2)} and table

    ((-1,1),(2,1),(-1,3),(4,3),(-1,-1))

has exact witness language {1^n0 1^m0:n,m>=1,n!=m}, which is nonregular. Its
length series is still the rational difference

    z^4/(1-z)^2 - z^4/(1-z^2).

Nonregularity follows, for instance, by distinguishing the prefixes 1^n0 with
the suffix 1^n0. Rational length counting is not a finite recognizer for words.

### C066: exact cancellation already occurs with two targets

Use start 0, final 6, and

    delta=((1,-1),(2,4),(3,-1),(6,-1),(-1,5),(6,-1),(-1,-1)),
    G={(0,1),(0,2)}.

There are exactly TWO accepted candidates, both of length four:

* 0000 has two flagged periods, 1 and 2;
* 0110 has no flagged period and is a witness.

Therefore C(z)=2z^4 and J(z)=2z^4. Their difference is identically zero,
although the true witness series is z^4. No amount of additional coefficient
checking repairs the wrong subtraction. The unambiguity guard is essential.
This is a counterexample to first-moment subtraction, not to decidability or
all rational-series methods. The compiler refuses this uncertified case.

## 7. Remaining end-to-end obligations, including the opposing route

For single-source targets T, let J_S(z) count candidate words whose period
endpoints include every state in S subseteq T, with J_empty=C. Each target
can occur at most once by Lemma 1, so exact inclusion-exclusion would give

    W(z)=sum_{S subseteq T} (-1)^|S| J_S(z).

This attempt computes J_S only for |S|<=1. It does not prove that the higher
joint-incidence series are rational, effectively comparable, or covered by a
bounded representation. Intersecting separate length series counts different
words, not common candidates, and is not a repair. Even a complete treatment
of every single-source input would need a further argument for interactions
between different sources; C042 prevents a source-local viability shortcut.

This is the next precise counting-route obligation. It offers an alternative
to the current root-pumping programme, not a replacement for its unresolved
multi-source theorem. One can also exploit the one-flag theorem immediately
as a sound filter in a larger portfolio: YES for one chosen flag alone does
not certify all flags, and a negative relaxation is an unrestricted negative.

On the opposing route, an undecidability reduction into binary terminal
instances cannot use only one forbidden pair after this normalization. It
must exploit additional flag interactions (or leave the stated fragment).
This is not evidence that multiple flags are undecidable; the cancellation
example is acyclic and trivial to decide directly. No imported undecidability
classification is used as a premise.

## 8. Executed verification and limits

`python3 experiments/check_one_flag_counting.py` (seed 2026090917) passes:

* All 2,304 three-state terminal tables/one-flag choices with fixed initial and
  final states (256 tables times nine pairs): 800 YES and 1,504 NO. The
  independent length-six oracle uses the separately recorded <=3-state theorem.
* 320 additional four-state queries, including arbitrary initial/source states
  and Bad sets, compared with the complete existing terminal length-four oracle.
* 300 acyclic instances with multiple terminal finals and every candidate
  enumerated: 165 YES, 135 NO, 376 candidate words.
* 111,413 raw word checks, 760 accepted candidates and 187 period incidences;
  1,831 exact length-coefficient comparisons, including the cancellation fixture.
* 120 cyclic random tables for separate coefficient/period checks, not guessed
  negative decisions; all 81 no-return three-state tables are also included.
* Independent determinant/Newton-identity checks on 321 series coefficients;
  these exercise the common-denominator argument, not just YES/NO outputs.
* Five semantic/input guards and four intentional caps. The antichain example
  with candidates 0 1* 0 and 1 0* 1 is an exact two-target NO extension.

An initial test expectation incorrectly called the words 0+1 and 1+0 a
negative antichain fixture; they have immediate unbordered witnesses. The test
was corrected to the analytic language in the preceding paragraph before the
saved PASS run. No algorithm counterexample or mathematical conclusion was
drawn from that incorrect fixture expectation.

The direct/reversed checker is unchanged at Git blob
1144ae52379e0417772e79582269cacd91c5bc17. The complete core regression is replayed
separately. There is no new Lean proof, independent human review, or claim of
running every repository experiment. Recorded finite checks validate the code;
the all-size decision and bound depend on the explicit arguments above.
