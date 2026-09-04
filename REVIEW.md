# Problem 1.7: review, findings, and research plan

Reviewed 4 September 2026. Source: `sep-topfree.pdf`, 31 August 2026, 19 pages.

**Problem 1.7 remains unsolved in this work.** The memo gives a useful reduction and a practical search framework. This review finds a false equivalence in its proposed next attack, proves a stronger truncation rule, and supplies independent executable checks. These are concrete steps toward a better research program, not a decision procedure for subtype entailment.

The PDF is the only supplied research source. Its earlier notes and `analysis-2026` scripts were unavailable during this review. The experiments here were written independently. They do not reproduce the memo's full reported census or formally verify its proofs.

## 1. What the problem actually asks

The signature is `{bottom, binary covariant product}`. Types may be infinite. A type is represented by the prefix-closed set `X(t)` of paths at which it has a product node. Subtyping is inclusion of these sets.

Removing the top constructor does not remove the greatest type: the infinite full binary tree `Omega = mu t. t × t` remains greatest. It does remove the competing top label that complicates the broader problem.

For a finite constraint set `C`, Problem 1.7 asks whether **every** substitution satisfying `C` also satisfies `alpha <= beta`. A counterexample needs just one finite path belonging to `X(alpha)` but not `X(beta)`. The types witnessing that difference can themselves be infinite.

The memo's useful chain is:

1. Normalize constraints into product lower bounds, product upper bounds, variable inequalities, and bottom denials.
2. Express these as implications between path memberships. Product lower bounds also force a product at the root.
3. Build the pushdown system `W`, which propagates memberships by prepending, removing, or retaining a path letter.
4. Seed the prefixes of a proposed separating path `p` in `alpha`. Close under `W`, together with the forced root facts.
5. Check that this closure avoids bottom denials **(S)** and that neither forced facts **(F)** nor the seeded prefixes **(B)** reach `beta,p`.
6. The languages for S and F are effectively regular. B is the difficult part.
7. Reverse `W` and decompose a run at its minimum stack height. The remaining comparison has the form `u` is a prefix of `zu`, hence a periodicity condition.
8. Reverse the word. Periodicity becomes a border of a prefix: a prefix repeated at the end of that prefix. A finite automaton determines which pairs of endpoint states forbid such a repetition.

This is why ordinary pushdown reachability is insufficient. It can compute the closure for a **chosen** path. It does not give a bound on all possible separating paths.

### The part I would retain

The direct arguments for Lemmas 1.8 and 2.4 and Theorem 2.6 are sound on inspection, with the stated satisfiability premise. All three side conditions matter. The construction also explains why regular infinite trees suffice as countermodels: reachability from the finite seed produces regular configuration languages.

Theorem 2.6 should explicitly invoke satisfiability and Proposition 2.5 when checking denials reached from unconditional root facts. S alone only protects the seeds coming from alpha. This is a repair to the written proof, not a counterexample to its statement.

The corrected minimum-stack argument in Theorem 4.2 retains exactly the missing overlap condition. Theorem 3.2 genuinely defeats the earlier regularity claim.

For example, let `C = {alpha × beta <= alpha}` and ask whether `beta <= alpha`. A countermodel is

```
beta  = bottom × ((bottom × bottom) × bottom)
alpha = mu t. t × beta
```

Path `10` is a product node in beta and a bottom node in alpha. In path-set form:

```
X(beta)  = {epsilon, 1, 10}
X(alpha) = 0* {epsilon, 1, 11, 110}
```

This example also shows why finite-tree semantics must stay separate. No finite alpha can satisfy `alpha × beta <= alpha`, while infinite solutions exist.

### What the budget theorem gives

`N''(L,D)` checks only borders whose length is at most L or whose induced period is at most D. Its emptiness certifies that no witness exists.

`S''(L,D)` adds a condition preventing all unchecked long-border/long-period repetitions. Its nonemptiness supplies a real witness.

Theorem 8.9 correctly characterizes decidability of abstract BorderAvoid by a computable upper bound on the least successful budget `B(I)=min(L+D)`. It does **not** supply that bound. Such an equivalence is possible for general effective witness-search problems; the substantive work is proving a bound using this problem's structure.

Without a bound or a separate NO certificate, exhausting a finite range of budgets means **UNKNOWN**, not NO.

## 2. The main defect: rigidity does not imply nonmerging

Remark 8.17 says that the two runs entering the earliest and last occurrence of each repeated suffix never merge. That is stronger than the definition of rigidity and is false.

Consider this fixed partial DFA over the binary alphabet:

| State | On 0 | On 1 |
|---|---|---|
| q0 | f | undefined |
| f | f | undefined |

Start at q0, accept at f, and let Bad be empty. Either choose an empty flag relation, or use the nonempty relation `G={(f,q0)}`.

For every `n >= 1`, the word `pi=0^n` is a witness. Its state sequence is `q0,f,...,f`, so the flagged ordered pair `(f,q0)` never occurs in the required order.

Its longest repeated suffix has length `n-1`. For every `0 <= ell <= n-1`:

```
e1(ell) = ell
c(e1(ell)-ell) = q0
c(n-ell) = f
```

Thus every one of these words is rigid by Definition 8.16. But, for `ell >= 1`, the runs starting at q0 and f merge after reading their first 0.

**Consequences:**

- The claimed equivalence in Remark 8.17 is false.
- There is no bound on the longest repeated suffix of **all rigid witnesses** as a function of the number of states. Two states already give an unbounded family.
- This does not refute a bound for shortest witnesses, nor an existential bound on B. The same instance has shortest witness `0` and budget zero.
- A finite graph of off-diagonal state pairs cannot simply replace the occurrence bookkeeping using that equivalence.

Theorem 8.15 itself survives this objection. Its equal-start-state hypothesis gives a valid sufficient truncation rule.

There is also an empty-word boundary case: a witness `epsilon` can never satisfy the stated rigidity definition. The strict shortening claim in 8.15 needs a nonempty original word. Handle `epsilon` before applying 8.15/8.16.

## 3. A stronger truncation rule

The following lemma is derived in this review. Its literature novelty has not been established.

**Lemma: transfer only the shorter word's repeated suffix.** Let pi be a witness of length n. Choose `0 <= e < n`, let `v=pi[1..e]`, and put `h=lrs(v)`. Suppose:

1. The length-h suffix of v equals the length-h suffix of pi; this is automatic when h=0.
2. `c(e-h)=c(n-h)`.

Then v is a witness.

**Proof.** Determinism and the shared suffix give `c(e-lambda)=c(n-lambda)` for every `0 <= lambda <= h`. In particular `c(e)=c(n)`, so v ends in an accepting state. Its states avoid Bad because they are states of pi.

Every suffix of v that occurs earlier has length at most h. It is also a suffix of pi, and every earlier occurrence in v is an occurrence in pi. The required target class is unchanged by the displayed equality. Therefore each such flag obligation follows from the corresponding obligation for pi.

Longer suffixes occur only at the end of v, so only diagonal obligations remain. These already hold at the same states of pi. Empty-suffix obligations follow from the endpoint law and `c(e)=c(n)`. Hence all witness conditions hold.

This implies the nonempty-word case of Theorem 8.15. For its proposed prefix, minimality of the occurrence gives `h < ell`; the memo's equality at ell implies the equality needed here at h. The new condition can hold even when the old condition does not.

For the rigid family above, choose `e=1`, so `v=0` and `h=0`. Since `c(1)=c(n)=f`, every longer rigid witness collapses to `0`.

**Further sufficient weakening.** Define `Pred_G(q)={r : G(r,q)}`. Replace condition 2 by

```
c(e) is accepting, and
Pred_G(c(e-lambda)) is a subset of Pred_G(c(n-lambda))
for every 0 <= lambda <= h.
```

The same proof works: any flag forbidden at the earlier endpoint would also be forbidden at the corresponding original endpoint. Equality of states is unnecessary.

This gives a useful direction for a finite abstraction: compare incoming flag sets along repeated suffixes. It still does not prove that the remaining words admit a computable size bound. Any shortest witness resists these cuts, but that observation alone is not a pumping theorem.

## 4. Independent experiments

Run from this directory:

```
python3 experiments/run_experiments.py
```

The standard-library implementation contains two independently written word predicates, direct N/S predicates, and finite reverse-reading automata for N/S. A resource limit returns UNKNOWN. NO requires exhaustion of the finite state graph.

The deterministic seed is `17082026`. Results are in `results/independent-checks.json`.

| Check | Coverage | Result |
|---|---:|---|
| Forward suffix condition versus reversed border condition | 10,160 words across 80 instances, lengths 0–6 | No mismatch |
| Direct N/S predicates versus finite automata | 121,920 comparisons | No mismatch |
| Sandwich implications | 121,920 checks | No failure |
| Original truncation hypotheses that applied | 2,142 cuts | All outputs were witnesses |
| New equal-state truncation hypotheses that applied | 3,504 cuts | All outputs were witnesses |
| New incoming-flag-set truncation hypotheses that applied | 4,755 cuts | All outputs were witnesses |
| New equal-state cuts on words already rigid in the memo's sense | 789 cuts | All outputs were witnesses |
| Finite-state N/S searches | 480 | 282 nonempty, 198 empty, no resource-limit exits |
| Theorem 3.2's language | All 4,095 binary words of length at most 11 | Exactly 4,017 disagreements with the old formula, matching the memo |

The tests also independently refute Examples 8.13(i) and (ii), by empty N automata at `(L,D)=(0,1)` and `(1,0)` respectively.

The random checks are finite regression evidence. The proofs above establish the all-length family and truncation statements. These checks do not constitute a formal proof of the entire implementation or of the original memo.

### A necessary calibration missing from the reported census

Use an `(n+1)`-state partial DFA whose only accepted word is `0^n`, with G empty. Then its **exact instance budget is `n-1`**.

For `L<n`, the reversed prefix `0^(L+1)` occurs at shifts `0,...,n-L-1`. The sufficient condition holds exactly when `D >= n-L-1`. Thus every successful budget has `L+D >= n-1`, and equality is attainable.

| Accepted word length n | States | Exact B |
|---:|---:|---:|
| 5 | 6 | 4 |
| 8 | 9 | 7 |
| 12 | 13 | 11 |

All lower-budget S automata were exhausted for these examples. This refutes a constant budget conjecture for arbitrary abstract instances. It does not suggest undecidability: the family has only a linear lower bound and no difficult flags. It also does not contradict the memo's observations about the instances it actually sampled.

Keep **the budget of a particular word**, **the minimum budget of an instance**, and **the budget at which a search found a NO certificate** separate. They measure different things.

## 5. Keep the reductions and negative claims precise

- The bounded public-source search found no surviving decision procedure for this exact semantic fragment. [Niehren and Priesnitz](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_01.pdf) give the cap-set/word-equation characterization for the signature containing both bottom and top. Their [1999 restricted result](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf) removes those constants from the constraint syntax while retaining them in valuations; that is a different restriction. Schubert's later PSPACE claim is explicitly [withdrawn because of an error in Lemma 5.5](https://arxiv.org/abs/2109.02458v2). See `notes/literature-check.md` for the bounded source audit.
- The proven direction is `top-free SEP <= PrefixAvoid <= BorderAvoid`. The memo explicitly leaves the converse with arbitrary regular annotations unfinished. A decision procedure for BorderAvoid would solve 1.7. Undecidability of arbitrary BorderAvoid would not, by itself, settle 1.7.
- Nonregularity blocks the proposed exact finite-automaton representation. It does not prove that all methods using rational relations, automata, or decidable logical fragments are exhausted. The broad wording in Section 6 goes beyond its counterexamples.
- The algebraic shape `G(i,j) iff B_i intersects A_j` is not by itself restrictive. Every finite relation H has such a representation: take `B_i={i}` and `A_j={i:H(i,j)}`. Any useful restriction must come from which summary languages and state transitions arise jointly from the same pushdown system.
- General non-structural PSPACE-hardness should not be silently promoted to a theorem for this exact signature and tree domain without the corresponding reduction. A computable B bound would establish decidability; it would not automatically establish PSPACE membership.
- Finite-depth checks of an infinite constructed model are regression evidence, not a global model proof. The eventual implementation should use exact regular-language checks for prefix closure, constraint satisfaction, and separation.

## 6. Research plan with concrete targets

### First: repair and reproduce

Correct Remark 8.17 and the empty-word case. Retain Theorems 2.6, 4.2, 8.7, and the nonempty case of 8.15 as the working foundation. Add the stronger lemma above, with a separate proof review.

When the original folder arrives, compare its predicates and witness certificates against this implementation. Reproduce the census with instance files, seeds, exact state counts, and explicit UNKNOWN outcomes. Include the two-state rigid family and the singleton-word budget family as mandatory calibrations.

**Deliverable:** a corrected claim ledger and an independently checked set of example inputs and outputs.

### Main proof direction: strengthen the minimal-witness argument

The target is an **existential computable bound on B**, preferably proved for the actual SEP-derived instances. Do not try to bound every rigid witness.

Use the stronger cut to study shortest witnesses or witnesses minimal under a stated pair of measures. Record the repeated suffix, the state trace through it, and incoming flag-set inclusions. A finite-state pair argument needs an explicit treatment of which earlier occurrence is being compared; two states alone lose that information.

The missing lemma should have a concrete form: beyond a specified bound, a witness either has an accepted proper prefix whose obligations transfer, or has a periodic block that can be shortened while preserving every flag obligation. For the second case, use period-overlap results together with the automaton's transition behavior. Prove preservation of new repetitions at a deletion boundary, rather than assuming it.

**Success:** a rigorous bound for a meaningful restricted class, a justified general normalization lemma, or a finite counterexample to the proposed lemma.

### Parallel experiment direction: search for genuinely difficult budgets

Construct instances deliberately, then use random mutations around them. Optimize exact B only after all lower budgets are proved empty by S searches. An unfinished search gives a lower-bound interval, not an exact score.

Separate growth forced solely by the regular language from growth caused by flags. Start with the linear family above, then seek stronger growth at similar state counts. Record shortest accepted-word length separately from shortest witness length.

Use symbolic constraint solving for finite candidate generation if exhaustive generation becomes too large. Every generated candidate must pass the independent checker. For a proposed upper bound, a single certified counterexample is more useful than thousands of random easy cases.

**Success:** a reusable hard family with an explicit budget lower-bound proof. Non-elementary growth alone would still not disprove computability.

### Protect the link to subtype entailment

Build an exact pipeline from normalized top-free constraints to the two regular side conditions and the summary classes. Verify produced countermodels by automata operations. Study transition restrictions shared by summaries of one W; merely imposing the intersection shape on G does not capture these restrictions.

Do not make a full converse reduction a prerequisite for an upper-bound attack. It becomes essential if an abstract impossibility result is supposed to settle Problem 1.7.

**Success:** a restricted structural invariant actually satisfied by SEP-derived inputs, or a complete converse with the regular annotation preserved.

### Give the NO side its own target

Neither enumeration of witnesses nor increasing S budgets supplies a general stopping rule. Investigate when N emptiness or a finite good-tree search certifies NO, and which examples resist both. A finite good tree certifies NO only after confirming that it contains no accepting target node.

Any proposed finite abstraction needs a soundness argument that rules out **all** witnesses. Keep UNKNOWN as an ordinary research outcome.

## 7. Astra and GLM agent roles

I can lead the next phase with the tools available here. This review used three independent Astra agents for the proof audit, occurrence-form audit, and literature check. Their agreement is useful review evidence, not proof.

GLM-5.3-Flash is not callable through the agent tools in this session. I did not send the memo to a GLM service. The developer's [official model card](https://huggingface.co/zai-org/GLM-5.3-Flash) does not give a basis for estimating its probability, or Astra's probability, of solving this open problem.

I would use two to four additional agents for bounded work:

- Search for a counterexample to one exact candidate lemma and minimize it.
- Build or audit one independent finite-state checker.
- Generate instances designed to violate a named budget bound.
- Check one proof line by line, especially changes of quantifiers and tree domain.

Keep one lead responsible for definitions, accepted lemmas, and the overall proof. Assign a separate reviewer to challenge each proposed theorem. Avoid giving every worker the same broad instruction to solve SEP; that encourages repeated unverified arguments.

Before using GLM extensively, test it on a small held-out set of precise true and false claims with executable checks. Judge it by valid proofs, reproducible counterexamples, and correct UNKNOWN handling. More workers are optional support; they are not a prerequisite for the next useful step. There is no sound basis here for claiming that Astra alone is more likely to finish the theorem.

The immediate next step is to incorporate the stronger truncation rule into the original engine and search the remaining minimal witnesses, while maintaining the exact connection to top-free constraints.
