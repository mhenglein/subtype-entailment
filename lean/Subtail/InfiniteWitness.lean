import Subtail.AbsorbingTerminal
import Subtail.PeriodicTail

/-!
# Finite extraction for C029

This module connects literal finite Witness comparisons to finite prefixes of
an infinite labelled run. It does not yet define the C029 decision procedure.
No finite horizon is silently treated as an all-input witness bound.
-/
namespace Subtail.InfiniteWitness

open AbsorbingTerminal

variable {k : Nat}

/-- The first n symbols of an infinite word, in their original order. -/
def wordOf (s : Nat → Bool) (n : Nat) : Word :=
  List.ofFn (fun t : Fin n => s t.val)

@[simp] theorem wordOf_length (s : Nat → Bool) (n : Nat) :
    (wordOf s n).length = n := by simp [wordOf]

@[simp] theorem wordOf_get (s : Nat → Bool) (n t : Nat) (ht : t < n) :
    (wordOf s n)[t]'(by simpa using ht) = s t := by simp [wordOf]

@[simp] theorem wordOf_zero (s : Nat → Bool) : wordOf s 0 = [] := by
  simp [wordOf]

theorem wordOf_succ (s : Nat → Bool) (n : Nat) :
    wordOf s (n+1) = wordOf s n ++ [s n] := by
  simpa [wordOf] using (List.ofFn_succ_last (f := fun t : Fin (n+1) => s t.val))

theorem wordOf_take (s : Nat → Bool) {i n : Nat} (hi : i ≤ n) :
    (wordOf s n).take i = wordOf s i := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hi]
  · intro t ht hu
    simp at hu
    simp [List.getElem_take, wordOf]

/-- The original deterministic run, including its initial control. -/
def Trace (I : Instance k) (s : Nat → Bool) (q : Nat → Fin k) : Prop :=
  q 0 = I.initial ∧ ∀ t, step I (q t) (s t) = some (q (t+1))

theorem trace_run (I : Instance k) {s : Nat → Bool} {q : Nat → Fin k}
    (h : Trace I s q) (n : Nat) :
    runFrom I I.initial (wordOf s n) = some (q n) := by
  induction n with
  | zero => simp [runFrom, h.1]
  | succ n ih =>
    rw [wordOf_succ, runFrom_append, ih]
    simpa [runFrom] using h.2 n

theorem trace_stateAt (I : Instance k) {s : Nat → Bool} {q : Nat → Fin k}
    (h : Trace I s q) {i n : Nat} (hi : i ≤ n) :
    stateAt I (wordOf s n) i = some (q i) := by
  unfold stateAt
  rw [wordOf_take s hi]
  exact trace_run I h i

/-- Literal suffix agreement on a finite prefix is exactly this finite test. -/
theorem agrees_wordOf_iff (s : Nat → Bool) {i j n : Nat}
    (hij : i ≤ j) (hjn : j ≤ n) :
    Agrees (wordOf s n) i j ↔
      ∀ t, t < n-j → s (j+t) = s (i+t) := by
  constructor
  · intro h t ht
    have he := h.getElem (i := t) (by simp; omega)
    simpa [List.getElem_drop, wordOf] using he
  · intro h
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simp; omega, ?_⟩
    intro t ht
    have ht' : t < n-j := by simpa using ht
    simpa [List.getElem_drop, wordOf] using h t ht'

/-- A finite comparison horizon suffices once all later target columns are
empty. The hypothesis explicitly contains EVERY old ordered comparison. -/
theorem witness_of_finite_suffix_test (I : Instance k)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    (N T : Nat)
    (hsafe : ∀ i, safeState I (q i) = true)
    (hfinal : I.final.get (q (N+T)) = true)
    (hzero : ∀ j, N < j → ∀ p, (I.flags.get p).get (q j) = false)
    (hcompare : ∀ i j, i < j → j ≤ N →
      (∀ t, t < T → s (i+t) = s (j+t)) →
      (I.flags.get (q i)).get (q j) = false) :
    Witness I (wordOf s (N+T)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ≤ N+T := by simpa using hi
    rw [trace_stateAt I htrace hi']
    simpa [safeCheck] using (safeState_iff I _).mp (hsafe i) |>.1
  · rw [wordOf_length, trace_stateAt I htrace (Nat.le_refl _)]
    exact hfinal
  · intro j hj i hij hag
    have hj' : j ≤ N+T := by simpa using hj
    rw [trace_stateAt I htrace (Nat.le_trans hij hj'), trace_stateAt I htrace hj']
    have heq : (I.flags.get (q i)).get (q j) = false := by
      by_cases hdiag : i = j
      · subst j
        exact ((safeState_iff I _).mp (hsafe i)).2
      · by_cases hold : j ≤ N
        · apply hcompare i j (by omega) hold
          intro t ht
          exact ((agrees_wordOf_iff s hij hj').mp hag t (by omega)).symm
        · exact hzero j (by omega) (q i)
    simp [unflaggedCheck, heq]

/-- Every comparison already excluded by an original finite witness stays
excluded for equal suffixes of any infinite word extending that witness. -/
theorem witness_unflagged_of_sameSuffix (I : Instance k)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    {n : Nat} (hw : Witness I (wordOf s n))
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ n)
    (heq : ∀ t, s (i+t) = s (j+t)) :
    (I.flags.get (q i)).get (q j) = false := by
  have ha : Agrees (wordOf s n) i j :=
    (agrees_wordOf_iff s hij hj).mpr (fun t _ => (heq t).symm)
  have hf := hw.2.2 j (by simpa using hj) i hij ha
  rw [trace_stateAt I htrace (Nat.le_trans hij hj), trace_stateAt I htrace hj] at hf
  simpa [unflaggedCheck] using hf

/-- The labelled run law also applies to a segment that starts away from the
original initial state. -/
theorem run_wordOf_from (I : Instance k) {s : Nat → Bool} {q : Nat → Fin k}
    (hstep : ∀ t, step I (q t) (s t) = some (q (t+1))) (n : Nat) :
    runFrom I (q 0) (wordOf s n) = some (q n) := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    rw [wordOf_succ, runFrom_append, ih]
    simpa [runFrom] using hstep n

theorem safeRun_wordOf (I : Instance k) {s : Nat → Bool} {q : Nat → Fin k}
    (hstep : ∀ t, step I (q t) (s t) = some (q (t+1)))
    (hsafe : ∀ t, safeState I (q t) = true) (n : Nat) :
    SafeRun I (q 0) (wordOf s n) (q n) := by
  refine ⟨run_wordOf_from I hstep n, ?_⟩
  intro i hi
  have hi' : i ≤ n := by simpa using hi
  refine ⟨q i, ?_, hsafe i⟩
  rw [wordOf_take s hi']
  exact run_wordOf_from I hstep i

/-- A witnessed finite prefix of a safe infinite labelled run satisfies the
existing InfWitness definition. This is finite pigeonhole, with no oracle for
infinite runs in an executable definition. -/
theorem infWitness_of_safe_trace (I : Instance k)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    (hsafe : ∀ t, safeState I (q t) = true) {n : Nat}
    (hw : Witness I (wordOf s n)) : InfWitness I := by
  let s' : Nat → Bool := fun t => s (n+t)
  let q' : Nat → Fin k := fun t => q (n+t)
  have hstep' : ∀ t, step I (q' t) (s' t) = some (q' (t+1)) := by
    intro t
    simpa [q', s', Nat.add_assoc] using htrace.2 (n+t)
  have hsafe' : ∀ t, safeState I (q' t) = true := fun t => hsafe (n+t)
  have hv := safeRun_wordOf I hstep' hsafe' k
  have hbig : k ≤ (wordOf s' k).length := by simp
  obtain ⟨i, j, p, hij, hj, hiRun, hjRun⟩ := safeRun_repeat_cut I hv hbig
  apply infWitness_of_repeat I hw (q := q' 0) (v := wordOf s' k) (r := q' k)
    (p := p) (i := i) (j := j)
  · simpa [q'] using trace_stateAt I htrace (Nat.le_refl n)
  · exact hv
  · exact hij
  · exact hj
  · exact hiRun
  · exact hjRun

/-- Eventual periodicity makes the finite horizon explicit. No primitive
period, witness bound or classical decision instance is assumed. -/
theorem witness_of_periodic_noConflict (I : Instance k)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    {N d : Nat} (hd : 0 < d)
    (hper : ∀ t, N ≤ t → s (t+d) = s t)
    (hsafe : ∀ i, safeState I (q i) = true)
    (hfinal : I.final.get (q (N+(N+d))) = true)
    (hzero : ∀ j, N < j → ∀ p, (I.flags.get p).get (q j) = false)
    (hno : ∀ i j, i < j → j ≤ N → PeriodicTail.SameSuffix s i j →
      (I.flags.get (q i)).get (q j) = false) :
    Witness I (wordOf s (N+(N+d))) := by
  apply witness_of_finite_suffix_test I htrace N (N+d) hsafe hfinal hzero
  intro i j hij hj hwindow
  exact hno i j hij hj (PeriodicTail.sameSuffix_of_eventually_periodic hd hper hwindow)

/-- The extracted witness still has a safe infinite continuation, expressed
using exactly the existing finite stem/nonempty-cycle InfWitness predicate. -/
theorem infWitness_of_periodic_noConflict (I : Instance k)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    {N d : Nat} (hd : 0 < d)
    (hper : ∀ t, N ≤ t → s (t+d) = s t)
    (hsafe : ∀ i, safeState I (q i) = true)
    (hfinal : I.final.get (q (N+(N+d))) = true)
    (hzero : ∀ j, N < j → ∀ p, (I.flags.get p).get (q j) = false)
    (hno : ∀ i j, i < j → j ≤ N → PeriodicTail.SameSuffix s i j →
      (I.flags.get (q i)).get (q j) = false) : InfWitness I := by
  exact infWitness_of_safe_trace I htrace hsafe
    (witness_of_periodic_noConflict I htrace hd hper hsafe hfinal hzero hno)

/-- Strong absorption supplies finality at every later cut of a trace. -/
theorem trace_final_after (I : Instance k) (hA : Absorbing I)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    {N : Nat} (hf : I.final.get (q N) = true) :
    ∀ t, I.final.get (q (N+t)) = true := by
  intro t
  induction t with
  | zero => simpa using hf
  | succ t ih =>
    have h := (hA (q (N+t)) ih (s (N+t)) (q (N+t+1)) (htrace.2 (N+t))).1
    simpa [Nat.add_assoc] using h

/-- Every positive successor of a final cut has an empty incoming flag column,
including all future positions in the same repeated cycle. -/
theorem trace_emptyIncoming_after (I : Instance k) (hA : Absorbing I)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    {N : Nat} (hf : I.final.get (q N) = true) :
    ∀ j, N < j → ∀ p, (I.flags.get p).get (q j) = false := by
  intro j hj p
  have hjEq : j = N + (j-N-1) + 1 := by omega
  have hf' := trace_final_after I hA htrace hf (j-N-1)
  have h := (hA (q (N+(j-N-1))) hf' (s (N+(j-N-1)))
    (q (N+(j-N-1)+1)) (htrace.2 (N+(j-N-1)))).2 p
  simpa [← hjEq] using h

/-- Complete finite-extraction implication under the actual Absorbing
hypothesis. The unresolved algorithmic task is to decide existence of the
trace/prefix with `hno`, not to assume `hno` in a final C029 checker theorem. -/
theorem infWitness_of_absorbing_periodic_trace (I : Instance k)
    (hA : Absorbing I)
    {s : Nat → Bool} {q : Nat → Fin k} (htrace : Trace I s q)
    {N d : Nat} (hd : 0 < d)
    (hper : ∀ t, N ≤ t → s (t+d) = s t)
    (hsafe : ∀ i, safeState I (q i) = true)
    (hfinal : I.final.get (q N) = true)
    (hno : ∀ i j, i < j → j ≤ N → PeriodicTail.SameSuffix s i j →
      (I.flags.get (q i)).get (q j) = false) : InfWitness I := by
  exact infWitness_of_periodic_noConflict I htrace hd hper hsafe
    (trace_final_after I hA htrace hfinal (N+d))
    (trace_emptyIncoming_after I hA htrace hfinal) hno

end Subtail.InfiniteWitness
