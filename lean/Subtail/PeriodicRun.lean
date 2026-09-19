import Subtail.InfiniteWitness

/-!
# Concrete finite-prefix and repeated-cycle streams

This module fixes the stream interface used by the C029 reverse monitor.  A
finite prefix is followed by a (possibly non-primitive) cyclic word.  The
definitions are total on all words; the theorems which use a period assume
that the cycle is nonempty.
-/

namespace Subtail
namespace PeriodicRun

open AbsorbingTerminal
open InfiniteWitness

variable {k : Nat}

/-- The infinite stream obtained by repeating `c`.  The empty word is mapped
to the constant false stream only to keep this definition total; all period
lemmas require `c ≠ []`. -/
def periodicStream (c : Word) (t : Nat) : Bool :=
  (c[t % c.length]?).getD false

/-- The stream obtained by reading `w` and then repeating `c`. -/
def prefixStream (w c : Word) (t : Nat) : Bool :=
  if t < w.length then (w[t]?).getD false
  else periodicStream c (t - w.length)

/-- The monitor's semantic acceptance predicate for an old prefix. -/
def PrefixGood (I : Instance k) (w c : Word) : Prop :=
  ∀ i j, i < j → j ≤ w.length →
    PeriodicTail.SameSuffix (prefixStream w c) i j →
      unflaggedCheck I (stateAt I w i) (stateAt I w j) = true

@[simp] theorem periodicStream_eq (c : Word) (t : Nat) :
    periodicStream c t = (c[t % c.length]?).getD false := rfl

theorem prefixStream_eq_prefix {w c : Word} {t : Nat} (ht : t < w.length) :
    prefixStream w c t = (w[t]?).getD false := by
  simp [prefixStream, ht]

theorem prefixStream_eq_tail {w c : Word} {t : Nat} (ht : w.length ≤ t) :
    prefixStream w c t = periodicStream c (t - w.length) := by
  simp [prefixStream, Nat.not_lt.mpr ht]

theorem prefixStream_eq_wordOf {w c : Word} {t : Nat} (ht : t < w.length) :
    prefixStream w c t = w[t]'(by omega) := by
  simpa [prefixStream, ht] using (List.getElem?_eq_getElem ht)

theorem periodicStream_periodic {c : Word} (hc : c ≠ []) :
    PeriodicTail.Periodic (periodicStream c) c.length := by
  intro t
  simp only [periodicStream]
  rw [show (t + c.length) % c.length = t % c.length by
    exact Nat.add_mod_right t c.length]

theorem prefixStream_periodic_tail {w c : Word} (hc : c ≠ []) :
    ∀ t, w.length ≤ t →
      prefixStream w c (t + c.length) = prefixStream w c t := by
  intro t ht
  rw [prefixStream_eq_tail (by omega), prefixStream_eq_tail ht]
  have hper := periodicStream_periodic hc
  have hidx : t + c.length - w.length = (t - w.length) + c.length := by
    omega
  rw [hidx]
  exact hper (t - w.length)

theorem wordOf_periodic_prefix {c : Word} {n : Nat} (hn : n ≤ c.length) :
    wordOf (periodicStream c) n = c.take n := by
  apply List.ext_getElem
  · simp [wordOf, List.length_take, Nat.min_eq_left hn]
  · intro i hi hright
    have hi' : i < n := by simpa [wordOf] using hi
    have hc' : i < c.length := by
      simp only [List.length_take, Nat.min_eq_left hn] at hright
      omega
    simp only [wordOf, List.getElem_ofFn]
    simp only [periodicStream, Nat.mod_eq_of_lt hc']
    rw [List.getElem?_eq_getElem hc']
    rw [List.getElem_take]
    rfl

theorem wordOf_periodic_append {c : Word} (hc : c ≠ []) (n : Nat) :
    wordOf (periodicStream c) (c.length + n) =
      c ++ wordOf (periodicStream c) n := by
  apply List.ext_getElem
  · simp [wordOf]
  · intro i hi hright
    have hleft : i < c.length + n := by simpa [wordOf] using hi
    simp only [wordOf, List.getElem_ofFn]
    rw [List.getElem_append]
    split
    · next hlt =>
        simp only [periodicStream, Nat.mod_eq_of_lt hlt]
        rw [List.getElem?_eq_getElem hlt]
        rfl
    · next hge =>
        have hidx : i - c.length < n := by omega
        simp only [List.getElem_ofFn]
        rw [show i = c.length + (i - c.length) by omega]
        rw [show c.length + (i - c.length) = (i - c.length) + c.length by omega]
        simpa using periodicStream_periodic hc (i - c.length)

theorem runFrom_periodic_append (I : Instance k) {q : Fin k} {c : Word}
    (hc : c ≠ []) (hcycle : SafeRun I q c q) (n : Nat) :
    runFrom I q (wordOf (periodicStream c) (c.length + n)) =
      runFrom I q (wordOf (periodicStream c) n) := by
  rw [wordOf_periodic_append hc n, runFrom_append, hcycle.1]
  rfl

theorem safeRun_periodic_prefix (I : Instance k) {q : Fin k} {c : Word}
    (hc : c ≠ []) (hcycle : SafeRun I q c q) :
    ∀ n, ∃ r, SafeRun I q (wordOf (periodicStream c) n) r := by
  have hcpos : 0 < c.length := by
    cases c with
    | nil => exact False.elim (hc rfl)
    | cons a c => simp
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : n < c.length
      · have hrun : ∃ r, runFrom I q (c.take n) = some r := by
          rcases hcycle.2 n (by omega) with ⟨r, hr, hs⟩
          exact ⟨r, hr⟩
        rcases hrun with ⟨r, hr⟩
        have hsafe : SafeRun I q (c.take n) r :=
          safeRun_prefix I hcycle (by omega) hr
        refine ⟨r, ?_⟩
        rw [wordOf_periodic_prefix (n := n) (by omega)]
        exact hsafe
      · have hlen : c.length ≤ n := by omega
        have hsub : n - c.length < n := by omega
        rcases ih (n - c.length) hsub with ⟨r, hr⟩
        have happ := safeRun_append I hcycle hr
        refine ⟨r, ?_⟩
        rw [show n = c.length + (n - c.length) by omega]
        rw [wordOf_periodic_append hc]
        exact happ

theorem wordOf_prefixStream {w c : Word} {n : Nat} (hn : n ≤ w.length) :
    wordOf (prefixStream w c) n = w.take n := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hn]
  · intro t ht htw
    have htn : t < n := by simpa [wordOf] using ht
    have htw' : t < w.length := by
      simp only [List.length_take, Nat.min_eq_left hn] at htw
      omega
    simp only [wordOf, List.getElem_ofFn]
    rw [prefixStream_eq_prefix htw']
    simp only [List.getElem?_eq_getElem htw']
    simp [List.getElem_take]

theorem wordOf_prefixStream_length (w c : Word) :
    wordOf (prefixStream w c) w.length = w := by
  simpa using wordOf_prefixStream (w := w) (c := c) (n := w.length)

theorem wordOf_prefixStream_append (w c : Word) (n : Nat) :
    wordOf (prefixStream w c) (w.length + n) =
      w ++ wordOf (periodicStream c) n := by
  apply List.ext_getElem
  · simp [wordOf]
  · intro i hi hright
    have hleft : i < w.length + n := by simpa [wordOf] using hi
    simp only [wordOf, List.getElem_ofFn]
    rw [List.getElem_append]
    split
    · next hlt =>
        rw [prefixStream_eq_prefix hlt]
        simp only [List.getElem?_eq_getElem hlt]
        rfl
    · next hge =>
        have hidx : i - w.length < n := by omega
        rw [prefixStream_eq_tail (by omega)]
        simp only [List.getElem_ofFn]

theorem safeRun_prefixStream_tail (I : Instance k) {w c : Word} {q : Fin k}
    (hw : SafeRun I I.initial w q) (hc : c ≠ [])
    (hcycle : SafeRun I q c q) (n : Nat) :
    ∃ r, SafeRun I I.initial
      (wordOf (prefixStream w c) (w.length + n)) r := by
  rcases safeRun_periodic_prefix I hc hcycle n with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [wordOf_prefixStream_append]
  exact safeRun_append I hw hr

theorem safeRun_prefixStream (I : Instance k) {w c : Word} {q : Fin k}
    (hw : SafeRun I I.initial w q) (hc : c ≠ [])
    (hcycle : SafeRun I q c q) :
    ∀ n, ∃ r, SafeRun I I.initial
      (wordOf (prefixStream w c) n) r := by
  intro n
  by_cases hn : n ≤ w.length
  · rcases hw.2 n (by omega) with ⟨r, hr, hs⟩
    refine ⟨r, ?_⟩
    rw [wordOf_prefixStream (c := c) hn]
    exact safeRun_prefix I hw hn hr
  · have hlen : w.length ≤ n := by omega
    have hsplit : n = w.length + (n - w.length) := by omega
    rw [hsplit]
    exact safeRun_prefixStream_tail I hw hc hcycle (n - w.length)

/-- The finite endpoint reached by the concrete prefix/cycle stream. -/
def prefixControl (I : Instance k) (w c : Word) (t : Nat) : Fin k :=
  (runFrom I I.initial (wordOf (prefixStream w c) t)).getD I.initial

theorem prefixControl_run (I : Instance k) {w c : Word} {t : Nat}
    (hrun : ∃ r, SafeRun I I.initial
      (wordOf (prefixStream w c) t) r) :
    runFrom I I.initial (wordOf (prefixStream w c) t) =
      some (prefixControl I w c t) := by
  rcases hrun with ⟨r, hr⟩
  unfold prefixControl
  rw [hr.1]
  rfl

theorem prefixStream_trace (I : Instance k) {w c : Word} {q : Fin k}
    (hw : SafeRun I I.initial w q) (hc : c ≠ [])
    (hcycle : SafeRun I q c q) :
    Trace I (prefixStream w c) (prefixControl I w c) := by
  have hall := safeRun_prefixStream I hw hc hcycle
  refine ⟨?_, ?_⟩
  · have hzero := prefixControl_run I (hall 0)
    simp [prefixControl, wordOf, runFrom]
  · intro t
    have ht := prefixControl_run I (hall t)
    have ht1 := prefixControl_run I (hall (t + 1))
    rw [wordOf_succ] at ht1
    rw [runFrom_append, ht] at ht1
    simpa [runFrom] using ht1

theorem prefixStream_safe (I : Instance k) {w c : Word} {q : Fin k}
    (hw : SafeRun I I.initial w q) (hc : c ≠ [])
    (hcycle : SafeRun I q c q) :
    ∀ t, safeState I (prefixControl I w c t) = true := by
  intro t
  rcases safeRun_prefixStream I hw hc hcycle t with ⟨r, hr⟩
  rcases hr.2 t (by simp) with ⟨s, hs, hsafe⟩
  have hrun := prefixControl_run I ⟨r, hr⟩
  have hs' : runFrom I I.initial
      (wordOf (prefixStream w c) t) = some s := by
    have ht : (wordOf (prefixStream w c) t).take t =
        wordOf (prefixStream w c) t := by
      apply List.take_of_length_le
      simp
    rw [ht] at hs
    exact hs
  have heq : s = prefixControl I w c t := by
    apply Option.some.inj
    rw [← hrun, ← hs']
  simpa [heq] using hsafe

theorem prefixControl_at_length (I : Instance k) {w c : Word} {q : Fin k}
    (hw : SafeRun I I.initial w q) :
    prefixControl I w c w.length = q := by
  have hrun : runFrom I I.initial
      (wordOf (prefixStream w c) w.length) = some q := by
    rw [wordOf_prefixStream_length]
    exact hw.1
  unfold prefixControl
  rw [hrun]
  rfl

theorem infWitness_of_prefix_good (I : Instance k)
    (hA : Absorbing I) {w c : Word} {q : Fin k}
    (hw : SafeRun I I.initial w q) (hcycle : SafeRun I q c q)
    (hc : c ≠ []) (hfinal : I.final.get q = true)
    (hgood : PrefixGood I w c) : InfWitness I := by
  let s : Nat → Bool := prefixStream w c
  let qs : Nat → Fin k := prefixControl I w c
  have htrace : Trace I s qs := by
    simpa [s, qs] using prefixStream_trace I hw hc hcycle
  have hsafe : ∀ i, safeState I (qs i) = true := by
    simpa [qs] using prefixStream_safe I hw hc hcycle
  have hboundary : qs w.length = q := by
    simpa [qs] using prefixControl_at_length I hw
  have hfinal' : I.final.get (qs w.length) = true := by
    simpa [hboundary] using hfinal
  have hper : ∀ t, w.length ≤ t → s (t + c.length) = s t := by
    simpa [s] using prefixStream_periodic_tail (w := w) (c := c) hc
  have hcpos : 0 < c.length := by
    cases c with
    | nil => exact False.elim (hc rfl)
    | cons a c => simp
  have hno : ∀ i j, i < j → j ≤ w.length →
      PeriodicTail.SameSuffix s i j →
      (I.flags.get (qs i)).get (qs j) = false := by
    intro i j hij hj heq
    have hiState : stateAt I w i = some (qs i) := by
      have hst := trace_stateAt I htrace (Nat.le_trans (Nat.le_of_lt hij) hj)
      simpa [s, qs, wordOf_prefixStream] using hst
    have hjState : stateAt I w j = some (qs j) := by
      have hst := trace_stateAt I htrace hj
      simpa [s, qs, wordOf_prefixStream] using hst
    have hg := hgood i j hij hj heq
    rw [hiState, hjState] at hg
    simpa [unflaggedCheck] using hg
  exact infWitness_of_absorbing_periodic_trace I hA htrace hcpos hper hsafe
    hfinal' hno

theorem witness_safeRun (I : Instance k) {w : Word} {q : Fin k}
    (hw : Witness I w) (hq : stateAt I w w.length = some q) :
    SafeRun I I.initial w q := by
  refine ⟨?_, witness_safeCut I hw⟩
  simpa [stateAt] using hq

theorem prefixGood_of_witness (I : Instance k) {w : Word}
    (hw : Witness I w) (c : Word) : PrefixGood I w c := by
  intro i j hij hj hsame
  have hi : i ≤ j := Nat.le_of_lt hij
  have hword := wordOf_prefixStream_length w c
  have hagStream : ∀ t, t < w.length - j →
      prefixStream w c (j + t) = prefixStream w c (i + t) := by
    intro t ht
    exact (hsame t).symm
  have hagWord : Agrees (wordOf (prefixStream w c) w.length) i j :=
    (InfiniteWitness.agrees_wordOf_iff (prefixStream w c) hi hj).mpr (by
      intro t ht
      exact hagStream t (by omega))
  rw [hword] at hagWord
  exact hw.2.2 j hj i hi hagWord

theorem infWitness_of_witness_cycle (I : Instance k)
    (hA : Absorbing I) {w c : Word} {q : Fin k}
    (hw : Witness I w) (hq : stateAt I w w.length = some q)
    (hcycle : SafeRun I q c q) (hc : c ≠ [])
    (hfinal : I.final.get q = true) : InfWitness I := by
  exact infWitness_of_prefix_good I hA (witness_safeRun I hw hq) hcycle hc
    hfinal (prefixGood_of_witness I hw c)

end PeriodicRun
end Subtail
