import Subtail.ExpressionNormalization
import Subtail.CanonicalReachability

/-!
# Finite-tree bounds for finite seeded stack closure

This module isolates the semantic part of the finite-tree candidate.  A
reverse-pop language is called hot when it has no uniform word-length bound.
For a finite seed list, the full stack closure is length-bounded exactly when
no reachable control is hot.  The result is independent of how hot controls
are computed; it uses the existing minimum-stack factorisation theorem.
-/

namespace Subtail
namespace FiniteTreeReduction

open TreeSemantics ExpressionNormalization CanonicalModel CanonicalReachability
  StackSummary StackReachability

/-! ## Exact semantic contracts -/

/-- A tree has finite height when all product addresses have a common bound. -/
def FiniteTree (X : Tree) : Prop :=
  ∃ N, ∀ w, X.nodes w → w.length < N

/-- The reverse-pop language into `m` has a uniform word-length bound. -/
def BoundedReversePop (M : System n) (m : Fin n) : Prop :=
  ∃ N, ∀ q w, Pop (reverse M) q w m → w.length < N

/-- A control is hot when its reverse-pop language is unbounded. -/
def Hot (M : System n) (m : Fin n) : Prop :=
  ¬ BoundedReversePop M m

/-- Reachability from one finite list of stack configurations. -/
def Reachable (M : System n) (seeds : List (Fin n × Word))
    (q : Fin n) (w : Word) : Prop :=
  ∃ p u, (p,u) ∈ seeds ∧ Reaches M (p,u) (q,w)

/-- The seeded closure has a common bound on all stack words. -/
def ClosureBounded (M : System n) (seeds : List (Fin n × Word)) : Prop :=
  ∃ N, ∀ q w, Reachable M seeds q w → w.length < N

/-- A hot control is reached by the seeded closure at some stack suffix. -/
def ReachesControl (M : System n) (seeds : List (Fin n × Word)) (m : Fin n) : Prop :=
  ∃ p u z, (p,u) ∈ seeds ∧ Reaches M (p,u) (m,z)

/-- A hot control is reached by the seeded closure at some stack suffix. -/
def ReachesHot (M : System n) (seeds : List (Fin n × Word)) (m : Fin n) : Prop :=
  ReachesControl M seeds m ∧ Hot M m

/-- A global bound on every reverse-pop language of a finite system. -/
def UniformReversePopBound (M : System n) : Prop :=
  ∃ N, ∀ m q w, Pop (reverse M) q w m → w.length < N

/-- Entailment restricted to valuations whose component trees are finite. -/
def FiniteEntails (C : List (Constraint n)) (a b : Fin n) : Prop :=
  ∀ rho, (∀ q, FiniteTree (rho q)) → Models C rho →
    Below (rho a) (rho b)

/-- Entailment restricted to finite component trees before normalization. -/
def FiniteExprEntails (G : Input n) (s t : Expr n) : Prop :=
  ∀ rho, (∀ q, FiniteTree (rho q)) → ExprModels G rho →
    Below (eval rho s) (eval rho t)

/-- A finite-tree model of a normalized constraint list. -/
def FiniteSatisfiable (C : List (Constraint n)) : Prop :=
  ∃ rho, Models C rho ∧ ∀ q, FiniteTree (rho q)

theorem finiteTree_bottom : FiniteTree bottom := by
  refine ⟨0, ?_⟩
  intro w hw
  exact False.elim hw

theorem finiteTree_product {X Y : Tree}
    (hX : FiniteTree X) (hY : FiniteTree Y) :
    FiniteTree (product X Y) := by
  obtain ⟨NX, hX⟩ := hX
  obtain ⟨NY, hY⟩ := hY
  refine ⟨max NX NY + 1, ?_⟩
  intro w hw
  cases w with
  | nil => simp
  | cons b w =>
      cases b with
      | false =>
          have hw' : X.nodes w := by simpa only [product] using hw
          have hlen := hX w hw'
          simp only [List.length_cons]
          omega
      | true =>
          have hw' : Y.nodes w := by simpa only [product] using hw
          have hlen := hY w hw'
          simp only [List.length_cons]
          omega

theorem finiteTree_eval (rho : Valuation n)
    (hf : ∀ q, FiniteTree (rho q)) (e : Expr n) :
    FiniteTree (eval rho e) := by
  induction e with
  | var x => exact hf x
  | bot => exact finiteTree_bottom
  | prod l r ihl ihr => exact finiteTree_product ihl ihr

theorem finiteTree_extend (R : Naming n) (rho : Valuation n)
    (hf : ∀ q, FiniteTree (rho q)) (i : Fin R.total) :
    FiniteTree (R.extend rho i) := by
  by_cases hi : i.val < n
  · simp [Naming.extend, hi]
    exact hf ⟨i.val, hi⟩
  · by_cases hb : i.val < n + R.botUsed.toNat
    · simp [Naming.extend, hi, hb]
      exact finiteTree_bottom
    · simp only [Naming.extend, dif_neg hi, dif_neg hb]
      exact finiteTree_eval rho hf _

/-! ## Finite list bounds -/

theorem seed_length_bounded (seeds : List (Fin n × Word)) :
    ∃ K, ∀ p u, (p,u) ∈ seeds → u.length < K := by
  induction seeds with
  | nil =>
      refine ⟨0, ?_⟩
      simp
  | cons seed seeds ih =>
      obtain ⟨K, hK⟩ := ih
      refine ⟨max (seed.2.length + 1) K, ?_⟩
      intro p u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (hK _ _ hu) (Nat.le_max_right _ _)

theorem fin_bound {P : Fin n → Nat → Prop}
    (mono : ∀ m {a b}, a ≤ b → P m a → P m b)
    (h : ∀ m, ∃ N, P m N) :
    ∃ N, ∀ m, P m N := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      intro m
      exact Fin.elim0 m
  | succ n ih =>
      obtain ⟨N0, h0⟩ := h 0
      have monot : ∀ (m : Fin n) {a b}, a ≤ b → P m.succ a → P m.succ b := by
        intro m a b hab ha
        exact mono m.succ hab ha
      have ht : ∀ m : Fin n, ∃ N, P m.succ N := by
        intro m
        exact h m.succ
      obtain ⟨Nt, ht⟩ := ih monot ht
      refine ⟨max N0 Nt, ?_⟩
      intro m
      refine Fin.cases ?_ ?_ m
      · exact mono 0 (Nat.le_max_left _ _) h0
      · intro m
        exact mono m.succ (Nat.le_max_right _ _) (ht m)

theorem reverse_pop_reaches_suffix {M : System n} {q m : Fin n}
    {w z : Word} (h : Pop (reverse M) q w m) :
    Reaches M (m,z) (q,w ++ z) := by
  have hr := reaches_reverse (pop_sound h z)
  simpa only [reverse_reverse] using hr

def repeatWord (w : Word) : Nat → Word
  | 0 => []
  | k + 1 => w ++ repeatWord w k

theorem repeatWord_length (w : Word) (k : Nat) :
    (repeatWord w k).length = k * w.length := by
  induction k with
  | zero => simp [repeatWord]
  | succ k ih =>
      simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

theorem repeat_reaches_of_cycle {M : System n} {m : Fin n} {w : Word}
    (hcycle : Reaches M (m,[]) (m,w)) (k : Nat) :
    Reaches M (m,[]) (m,repeatWord w k) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
      have hs := reaches_suffix hcycle (repeatWord w k)
      have hs' : Reaches M (m,repeatWord w k)
          (m,repeatWord w (k+1)) := by
        simpa [repeatWord] using hs
      exact reaches_trans ih hs'

/-! ## Two finite-tree transfer endpoints -/

theorem forced_reverse_pop_loop_noFiniteModel
    (C : List (Constraint n)) (m : Fin n)
    (hf : Forced C m)
    (hloop : ∃ w, w ≠ [] ∧ Pop (reverse (systemOf C)) m w m) :
    ¬ FiniteSatisfiable C := by
  rintro ⟨rho, hm, hfinite⟩
  obtain ⟨w, hwne, hw⟩ := hloop
  have hcycle : Reaches (systemOf C) (m,[]) (m,w) := by
    simpa using (reverse_pop_reaches_suffix hw (z := []))
  obtain ⟨N, hN⟩ := hfinite m
  have hderived : ∀ k, Derived C (forcedSeeds C) m (repeatWord w k) := by
    intro k
    exact reaches_preserves_derived (repeat_reaches_of_cycle hcycle k)
      (Derived.seed ⟨hf, rfl⟩)
  have hnode : ∀ k, (rho m).nodes (repeatWord w k) := by
    intro k
    exact derived_sound hm (forcedSeeds_in_model hm) (hderived k)
  have hlenw : 0 < w.length := by
    cases w with
    | nil => simp at hwne
    | cons a w => simp
  have hbig := hN (repeatWord w (N + 1)) (hnode (N + 1))
  rw [repeatWord_length] at hbig
  have hstrict0 : N < N + w.length := Nat.lt_add_of_pos_right hlenw
  have hNmul : N ≤ N * w.length := Nat.le_mul_of_pos_right N hlenw
  have hstrict : N < N * w.length + w.length :=
    Nat.lt_of_lt_of_le hstrict0 (Nat.add_le_add_right hNmul _)
  have hstrict' : N < (N + 1) * w.length := by
    simpa [Nat.add_mul] using hstrict
  omega

/-! ## Hot-control characterization -/

theorem closureBounded_iff_noHot (M : System n) (seeds : List (Fin n × Word)) :
    ClosureBounded M seeds ↔ ∀ m, ¬ ReachesHot M seeds m := by
  constructor
  · rintro ⟨N, hN⟩ m hhot
    obtain ⟨⟨p, u, z, hseed, hreach⟩, hm⟩ := hhot
    apply hm
    refine ⟨N, ?_⟩
    intro q w hpop
    have hreach' := reaches_trans hreach (reverse_pop_reaches_suffix hpop)
    have hb := hN q (w ++ z) ⟨p, u, hseed, hreach'⟩
    have hw : w.length ≤ (w ++ z).length := by simp
    exact Nat.lt_of_le_of_lt hw hb
  · intro hsafe
    classical
    have each : ∀ m, ∃ N, ReachesControl M seeds m →
        ∀ q w, Pop (reverse M) q w m → w.length < N := by
      intro m
      by_cases hr : ReachesControl M seeds m
      · have hnotHot : ¬ Hot M m := by
          intro hm
          exact hsafe m ⟨hr, hm⟩
        have hb : BoundedReversePop M m := by
          by_cases hnb : BoundedReversePop M m
          · exact hnb
          · exact False.elim (hnotHot hnb)
        obtain ⟨N, hN⟩ := hb
        exact ⟨N, fun _ => hN⟩
      · refine ⟨0, ?_⟩
        intro hreach
        exact False.elim (hr hreach)
    obtain ⟨N, hN⟩ := fin_bound (P := fun m k =>
      ReachesControl M seeds m →
        ∀ q w, Pop (reverse M) q w m → w.length < k)
      (by
        intro m a b hab ha hrc q w hp
        exact Nat.lt_of_lt_of_le (ha hrc q w hp) hab)
      each
    obtain ⟨K, hK⟩ := seed_length_bounded seeds
    refine ⟨N + K, ?_⟩
    intro q w hreach
    obtain ⟨p, u, hseed, hpath⟩ := hreach
    obtain ⟨x, y, z, m, hux, hwz, hp, hq⟩ := reaches_normal hpath
    change u = x ++ z at hux
    change w = y ++ z at hwz
    change Pop M p x m at hp
    change Pop (reverse M) q y m at hq
    have hpm : Reaches M (p,u) (m,z) := by
      simpa [hux] using pop_sound hp z
    have hrc : ReachesControl M seeds m := ⟨p, u, z, hseed, hpm⟩
    have hy : y.length < N := hN m hrc q y hq
    have hu : u.length < K := hK p u hseed
    have hzle : z.length ≤ u.length := by
      rw [hux]
      simp
    have hz : z.length < K := Nat.lt_of_le_of_lt hzle hu
    rw [hwz]
    simp only [List.length_append]
    omega

/-! ## Canonical-closure readback -/

/-- A normalized derivation closure has one common finite-height bound. -/
def DerivedBounded (C : List (Constraint n)) (S : Seeds n) : Prop :=
  ∃ N, ∀ q w, Derived C S q w → w.length < N

theorem derivedBounded_iff_closureBounded
    (C : List (Constraint n)) (seeds : List (Fin n × Word)) :
    DerivedBounded C (seedPred seeds) ↔
      ClosureBounded (systemOf C) seeds := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro q w hreach
    obtain ⟨p, u, hseed, hpath⟩ := hreach
    exact hN q w ((derived_iff_reaches C (seedPred seeds) q w).mpr
      ⟨p, u, hseed, hpath⟩)
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro q w hderived
    obtain ⟨p, u, hseed, hpath⟩ :=
      (derived_iff_reaches C (seedPred seeds) q w).mp hderived
    exact hN q w ⟨p, u, hseed, hpath⟩

theorem derivedBounded_iff_noHot
    (C : List (Constraint n)) (seeds : List (Fin n × Word)) :
    DerivedBounded C (seedPred seeds) ↔
      ∀ m, ¬ ReachesHot (systemOf C) seeds m := by
  rw [derivedBounded_iff_closureBounded]
  exact closureBounded_iff_noHot (systemOf C) seeds

theorem pathDerivedBounded_iff_noHot
    (C : List (Constraint n)) (a : Fin n) (pi : Word) :
    DerivedBounded C (pathSeeds C a pi) ↔
      ∀ m, ¬ ReachesHot (systemOf C) (pathList C a pi) m := by
  rw [← pathList_pred C a pi]
  exact derivedBounded_iff_noHot C (pathList C a pi)

theorem closureFinite_iff_derivedBounded
    (C : List (Constraint n)) (S : Seeds n)
    (hc : SeedsClosed S) (hr : HasRoots C S) :
    (∀ q, FiniteTree (closureValuation C S hc hr q)) ↔
      DerivedBounded C S := by
  constructor
  · intro hfinite
    classical
    have each : ∀ q, ∃ N, ∀ w, Derived C S q w → w.length < N := by
      intro q
      obtain ⟨N, hN⟩ := hfinite q
      exact ⟨N, hN⟩
    obtain ⟨N, hN⟩ := fin_bound
      (P := fun q k => ∀ w, Derived C S q w → w.length < k)
      (by
        intro q a b hab ha w hw
        exact Nat.lt_of_lt_of_le (ha w hw) hab)
      each
    exact ⟨N, hN⟩
  · rintro ⟨N, hN⟩ q
    refine ⟨N, ?_⟩
    intro w hw
    exact hN q w hw

theorem canonicalFinite_iff_noHot
    (C : List (Constraint n)) (a : Fin n) (pi : Word) :
    (∀ q, FiniteTree (canonical C a pi q)) ↔
      ∀ m, ¬ ReachesHot (systemOf C) (pathList C a pi) m := by
  simp only [canonical]
  rw [closureFinite_iff_derivedBounded C (pathSeeds C a pi)
    (pathSeeds_closed C a pi) (pathSeeds_roots C a pi)]
  exact pathDerivedBounded_iff_noHot C a pi

theorem finiteEntails_iff_entails_of_uniform_reverse_pop
    (C : List (Constraint n)) (a b : Fin n)
    (hbound : UniformReversePopBound (systemOf C)) :
    FiniteEntails C a b ↔ Entails C a b := by
  constructor
  · intro hfinite
    classical
    by_cases hent : Entails C a b
    · exact hent
    · obtain ⟨pi, hs, hb⟩ := (not_entails_iff_canonical C a b).mp hent
      have hsafe : ∀ m, ¬ ReachesHot (systemOf C) (pathList C a pi) m := by
        intro m hhot
        obtain ⟨_, hm⟩ := hhot
        apply hm
        obtain ⟨N, hN⟩ := hbound
        exact ⟨N, fun q w hp => hN m q w hp⟩
      have hfiniteCanonical := (canonicalFinite_iff_noHot C a pi).mpr hsafe
      have hmodel := closure_models (pathSeeds_closed C a pi)
        (pathSeeds_roots C a pi) hs
      have hbelow := hfinite (canonical C a pi) hfiniteCanonical hmodel
      exact False.elim (hb (hbelow pi (canonical_contains C a pi)))
  · intro hent rho _ hm
    exact hent rho hm

theorem normalize_finite_entails_iff (G : Input n) (s t : Expr n) :
    FiniteExprEntails G s t ↔
      FiniteEntails (normalized G s t)
        ((naming G s t).ref s) ((naming G s t).ref t) := by
  have hs := naming_support G s t s (by simp [forest])
  have ht := naming_support G s t t (by simp [forest])
  constructor
  · intro h eta hfinite hm
    have hd := normalized_definitions G s t eta hm
    rw [representative_correct _ _ hd _ hs,
      representative_correct _ _ hd _ ht]
    exact h _ (fun x => hfinite ((naming G s t).old x))
      (restrict_models G s t eta hm)
  · intro h rho hfinite hm
    have hh := h ((naming G s t).extend rho)
      (fun i => finiteTree_extend (naming G s t) rho hfinite i)
      (extend_models G s t rho hm)
    rw [extend_ref _ _ _ hs, extend_ref _ _ _ ht] at hh
    exact hh

end FiniteTreeReduction
end Subtail
