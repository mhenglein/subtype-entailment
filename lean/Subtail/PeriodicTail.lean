import Subtail.Basic

/-!
# Periodic tails

Small, stream-level lemmas for the periodic continuation branch.  These
lemmas do not mention automata or primitive periods: they only transport
eventual agreement along two positive shifts.
-/

namespace Subtail
namespace PeriodicTail

variable {α : Type}

def SameSuffix (s : Nat → α) (i j : Nat) : Prop :=
  ∀ t, s (i + t) = s (j + t)

def MatchesFrom (s r : Nat → α) (i : Nat) : Prop :=
  ∀ t, i ≤ t → s t = r t

def Periodic (r : Nat → α) (d : Nat) : Prop :=
  ∀ t, r (t + d) = r t

theorem sameSuffix_step {s : Nat → α} {i j : Nat}
    (hij : i < j) (h : SameSuffix s i j) {t : Nat} (hti : i ≤ t) :
    s (t + (j - i)) = s t := by
  have h0 := h (t - i)
  have hleft : i + (t - i) = t := by omega
  have hright : j + (t - i) = t + (j - i) := by omega
  rw [hleft, hright] at h0
  exact h0.symm

theorem sameSuffix_mul {s : Nat → α} {i j : Nat}
    (hij : i < j) (h : SameSuffix s i j) {t : Nat} (hti : i ≤ t) :
    ∀ n, s (t + (j - i) * n) = s t := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := sameSuffix_step hij h (t := t + (j - i) * n) (by omega)
      have hstep' : s (t + (j - i) * (n + 1)) =
          s (t + (j - i) * n) := by
        simpa [Nat.mul_succ, Nat.add_assoc] using hstep
      exact hstep'.trans ih

theorem periodic_mul {r : Nat → α} {d : Nat}
    (h : Periodic r d) :
    ∀ t n, r (t + d * n) = r t := by
  intro t n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := h (t + d * n)
      have hstep' : r (t + d * (n + 1)) = r (t + d * n) := by
        simpa [Nat.mul_succ, Nat.add_assoc] using hstep
      exact hstep'.trans ih

/-- Eventual agreement with a positive periodic stream propagates back to
the first suffix equality.  No relation between i,j and N is required. -/
theorem eventually_sameSuffix_iff
    {s r : Nat → α} {d N i j : Nat}
    (hd : 0 < d) (hr : Periodic r d) (hm : MatchesFrom s r N)
    (hij : i < j) :
    SameSuffix s i j ↔ MatchesFrom s r i ∧ SameSuffix r i j := by
  constructor
  · intro hs
    have hsFrom : MatchesFrom s r i := by
      intro t hti
      have hg : 0 < j - i := by omega
      have hshift : N ≤ t + (j - i) * (d * N) := by
        have hNprod : N ≤ (j - i) * (d * N) := by
          calc
            N ≤ d * N := Nat.le_mul_of_pos_left N hd
            _ ≤ (j - i) * (d * N) := Nat.le_mul_of_pos_left (d * N) hg
        omega
      have hsMul := sameSuffix_mul hij hs hti (d * N)
      have hrMul := periodic_mul hr t ((j - i) * N)
      have htail := hm (t + (j - i) * (d * N)) hshift
      have hcomm : (j - i) * (d * N) = d * ((j - i) * N) := by
        ac_rfl
      calc
        s t = s (t + (j - i) * (d * N)) := hsMul.symm
        _ = r (t + (j - i) * (d * N)) := htail
        _ = r (t + d * ((j - i) * N)) := by rw [hcomm]
        _ = r t := hrMul
    refine ⟨hsFrom, ?_⟩
    intro t
    calc
      r (i + t) = s (i + t) := (hsFrom (i + t) (by omega)).symm
      _ = s (j + t) := hs t
      _ = r (j + t) := hsFrom (j + t) (by omega)
  · rintro ⟨hm', hr'⟩ t
    calc
      s (i + t) = r (i + t) := hm' (i + t) (by omega)
      _ = r (j + t) := hr' t
      _ = s (j + t) := (hm' (j + t) (by omega)).symm

/-- A suffix equality on the finite window before the periodic tail extends to
all offsets.  The window endpoint is strict so that the first reduction lands
at an offset covered by the premise. -/
theorem sameSuffix_of_eventually_periodic
    {s : Nat → α} {d N i j : Nat}
    (hd : 0 < d)
    (hper : ∀ t, N ≤ t → s (t + d) = s t)
    (hwindow : ∀ t, t < N + d → s (i + t) = s (j + t)) :
    SameSuffix s i j := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
      by_cases hlt : t < N + d
      · exact hwindow t hlt
      · have htd : N ≤ t - d := by omega
        have hprev : t - d < t := by omega
        have hleft0 := hper (i + (t - d)) (by omega)
        have hright0 := hper (j + (t - d)) (by omega)
        have hleft : s (i + t) = s (i + (t - d)) := by
          have hidx : i + (t - d) + d = i + t := by omega
          rw [← hidx]
          exact hleft0
        have hright : s (j + t) = s (j + (t - d)) := by
          have hidx : j + (t - d) + d = j + t := by omega
          rw [← hidx]
          exact hright0
        exact hleft.trans ((ih (t - d) hprev).trans hright.symm)

/-- Matching a globally periodic stream makes the source periodic after the
matching point. -/
theorem periodic_from_matches
    {s r : Nat → α} {d N : Nat}
    (hr : Periodic r d) (hm : MatchesFrom s r N) :
    ∀ t, N ≤ t → s (t + d) = s t := by
  intro t ht
  calc
    s (t + d) = r (t + d) := hm (t + d) (by omega)
    _ = r t := hr t
    _ = s t := (hm t ht).symm

/-- Finite extraction for a periodic tail, stated with the direct finite
window and without primitive-period assumptions. -/
theorem sameSuffix_of_periodic_tail_window
    {s r : Nat → α} {d N i j : Nat}
    (hd : 0 < d) (hr : Periodic r d) (hm : MatchesFrom s r N)
    (hwindow : ∀ t, t < N + d → s (i + t) = s (j + t)) :
    SameSuffix s i j := by
  exact sameSuffix_of_eventually_periodic hd (periodic_from_matches hr hm) hwindow

end PeriodicTail
end Subtail
