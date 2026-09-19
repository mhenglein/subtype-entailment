import Subtail.PeriodicRotation
import Subtail.PeriodicRun
import Subtail.PeriodicGood
import Subtail.InfiniteWitness
import Subtail.RankQueryEnumeration

/- The reverse periodic monitor used by C029. -/
namespace Subtail
namespace PeriodicMonitor
open AbsorbingTerminal
open RankQueryEnumeration
open InfiniteWitness
open PeriodicRun
open PeriodicGood
open PeriodicRotation
variable {k : Nat}

def ray (c : Word) (z : Fin c.length) (t : Nat) : Bool :=
  PeriodicRun.periodicStream c (z.val + t)

def RayAll (w c : Word) (z : Fin c.length) : Prop :=
  ∀ t, PeriodicRun.prefixStream w c t = ray c z t

def MismatchTail (w c : Word) : Prop :=
  ∃ z : Fin c.length, ∃ m N : Nat,
    m < N ∧ N ≤ w.length ∧
      PeriodicTail.MatchesFrom (PeriodicRun.prefixStream w c) (ray c z) N ∧
      PeriodicRun.prefixStream w c m ≠ ray c z m

@[simp] theorem prefixStream_cons_zero (a : Bool) (w c : Word) :
    PeriodicRun.prefixStream (a :: w) c 0 = a := by
  simp [PeriodicRun.prefixStream]

theorem prefixStream_cons_succ (a : Bool) (w c : Word) (t : Nat) :
    PeriodicRun.prefixStream (a :: w) c (t + 1) =
      PeriodicRun.prefixStream w c t := by
  by_cases ht : t < w.length
  · simp [PeriodicRun.prefixStream, ht]
  · have hlen : w.length ≤ t := by omega
    have htail : (a :: w).length ≤ t + 1 := by
      simp only [List.length_cons]
      omega
    rw [PeriodicRun.prefixStream_eq_tail htail,
      PeriodicRun.prefixStream_eq_tail hlen]
    congr 1
    simp only [List.length_cons]
    omega

abbrev Bucket (k : Nat) := Vector Bool k
structure State (k : Nat) (c : Word) where
  current : Fin k
  phase : Fin c.length
  matching : Bool
  buckets : Vector (Bucket k) c.length
  deriving DecidableEq, Repr
def zeroBucket (k : Nat) : Bucket k := Vector.ofFn (fun _ : Fin k => false)
def singletonBucket (q : Fin k) : Bucket k := (zeroBucket k).set q.val true q.isLt
def emptyBuckets (k d : Nat) : Vector (Bucket k) d :=
  Vector.ofFn (fun _ : Fin d => zeroBucket k)
def bucketHas (b : Bucket k) (q : Fin k) : Bool := b.get q
def addBucket (b : Bucket k) (q : Fin k) : Bucket k := b.set q.val true

theorem bucket_get_set_eq (b : Bucket k) (q : Fin k) :
    (b.set q.val true q.isLt).get q = true := by
  change (b.set q.val true q.isLt)[q.val] = true
  rw [Vector.getElem_set q.isLt q.isLt]
  simp

theorem bucket_get_set_ne (b : Bucket k) (q r : Fin k)
    (h : q.val ≠ r.val) :
    (b.set q.val true q.isLt).get r = b.get r := by
  change (b.set q.val true q.isLt)[r.val] = b[r.val]
  rw [Vector.getElem_set q.isLt r.isLt]
  simp [h]

theorem bucketHas_add (b : Bucket k) (q r : Fin k)
    (h : bucketHas b r = true) : bucketHas (addBucket b q) r = true := by
  by_cases hqr : q = r
  · subst r
    exact bucket_get_set_eq b q
  · have hqr' : q.val ≠ r.val := by
      intro hval
      apply hqr
      exact Fin.ext hval
    simpa [bucketHas, addBucket] using
      (bucket_get_set_ne b q r hqr').trans h

theorem bucketHas_singleton (q r : Fin k) :
    bucketHas (singletonBucket q) r = true ↔ q = r := by
  by_cases hqr : q = r
  · subst r
    exact ⟨fun _ => rfl, fun _ => bucket_get_set_eq (zeroBucket k) q⟩
  · have hqr' : q.val ≠ r.val := by
      intro hval
      apply hqr
      exact Fin.ext hval
    constructor
    · intro h
      change ((zeroBucket k).set q.val true q.isLt).get r = true at h
      rw [bucket_get_set_ne (zeroBucket k) q r hqr'] at h
      have hz : (zeroBucket k).get r = false := by
        unfold zeroBucket
        change (Vector.ofFn (fun _ : Fin k => false))[r.val] = false
        rw [Vector.getElem_ofFn r.isLt]
      rw [hz] at h
      simp at h
    · intro h
      exact False.elim (hqr h)
def bucketVectors (k d : Nat) : List (Vector (Bucket k) d) :=
  (exactLists (masks k) d).filterMap (vectorFromList d)
theorem mem_bucketVectors (b : Vector (Bucket k) d) :
    b ∈ bucketVectors k d := by
  apply List.mem_filterMap.mpr
  refine ⟨b.toList, ?_, vectorFromList_toList b⟩
  apply (mem_exactLists (masks k) d b.toList).mpr
  constructor
  · simp [Vector.toList]
  · intro x hx
    exact mem_masks x
def allStates (k : Nat) (c : Word) : List (State k c) :=
  (List.finRange k).flatMap (fun q =>
    (List.finRange c.length).flatMap (fun z =>
      bools.flatMap (fun matching =>
        (bucketVectors k c.length).map (fun bs =>
          { current := q, phase := z, matching := matching, buckets := bs }))))
theorem mem_allStates (s : State k c) : s ∈ allStates k c := by
  cases s with
  | mk q z matching buckets =>
    simp only [allStates, List.mem_flatMap, List.mem_map]
    refine ⟨q, List.mem_finRange _, z, List.mem_finRange _, matching,
      mem_bools matching, buckets, mem_bucketVectors buckets, rfl⟩
def phaseAt (c : Word) (x t : Fin c.length) : Fin c.length :=
  ⟨(x.val + t.val) % c.length, by
    have hx : x.val < c.length := x.isLt
    have h : 0 < c.length := by omega
    exact Nat.mod_lt _ h⟩
def phasePred (c : Word) (z : Fin c.length) : Fin c.length :=
  ⟨(z.val + c.length - 1) % c.length, by
    have hz : z.val < c.length := z.isLt
    have h : 0 < c.length := by omega
    exact Nat.mod_lt _ h⟩

def phaseShift (c : Word) (z : Fin c.length) (n : Nat) : Fin c.length :=
  ⟨(z.val + n) % c.length, by
    have hz : z.val < c.length := z.isLt
    have h : 0 < c.length := by omega
    exact Nat.mod_lt _ h⟩

@[simp] theorem phaseShift_zero (c : Word) (z : Fin c.length) :
    phaseShift c z 0 = z := by
  apply Fin.ext
  simp [phaseShift, Nat.mod_eq_of_lt z.isLt]

theorem phaseShift_pred_succ {c : Word} (z : Fin c.length) (n : Nat) :
    phaseShift c (phasePred c z) (n + 1) = phaseShift c z n := by
  apply Fin.ext
  have hpred :
      (((z.val + c.length - 1) % c.length) + 1) % c.length = z.val := by
    have hzlt := z.isLt
    have hd : 0 < c.length := by omega
    by_cases hz : z.val = 0
    · have hsub : c.length - 1 < c.length := by omega
      have heq : c.length - 1 + 1 = c.length := by omega
      simp [hz, Nat.mod_eq_of_lt hsub, heq]
    · have hpos : 0 < z.val := by omega
      have heq : z.val + c.length - 1 = (z.val - 1) + c.length := by omega
      have hsub : z.val - 1 < c.length := by omega
      have heq' : z.val - 1 + 1 = z.val := by omega
      simp [heq, Nat.mod_eq_of_lt hsub, heq', Nat.mod_eq_of_lt z.isLt]
  simp only [phaseShift, phasePred]
  have hidx :
      (z.val + c.length - 1) % c.length + (n + 1) =
        ((z.val + c.length - 1) % c.length + 1) + n := by omega
  rw [hidx]
  calc
    _ = ((((z.val + c.length - 1) % c.length) + 1) % c.length +
        n % c.length) % c.length := Nat.add_mod _ _ _
    _ = (z.val + n % c.length) % c.length := by rw [hpred]
    _ = (z.val + n) % c.length := by
      simpa only [Nat.mod_eq_of_lt z.isLt] using (Nat.add_mod z.val n c.length).symm

theorem ray_phasePred_shift {c : Word} (hc : c ≠ [])
    (z : Fin c.length) (t : Nat) :
    ray c (phasePred c z) (t + 1) = ray c z t := by
  have hzlt := z.isLt
  have hd : 0 < c.length := by
    cases c with
    | nil => exact False.elim (hc rfl)
    | cons b c => simp
  have hpred :
      (((z.val + c.length - 1) % c.length) + 1) % c.length = z.val := by
    by_cases hz : z.val = 0
    · have hsub : c.length - 1 < c.length := by omega
      have heq : c.length - 1 + 1 = c.length := by omega
      simp [hz, Nat.mod_eq_of_lt hsub, heq]
    · have hpos : 0 < z.val := by omega
      have heq : z.val + c.length - 1 = (z.val - 1) + c.length := by omega
      have hsub : z.val - 1 < c.length := by omega
      have heq' : z.val - 1 + 1 = z.val := by omega
      simp [heq, Nat.mod_eq_of_lt hsub, heq',
        Nat.mod_eq_of_lt z.isLt]
  unfold ray PeriodicRun.periodicStream phasePred
  have hidx :
      ((z.val + c.length - 1) % c.length) + (t + 1) =
        (((z.val + c.length - 1) % c.length) + 1) + t := by omega
  rw [hidx]
  have hm :
      ((((z.val + c.length - 1) % c.length) + 1) + t) % c.length =
        (z.val + t) % c.length := by
    calc
      _ = ((((z.val + c.length - 1) % c.length) + 1) % c.length +
        t % c.length) % c.length := Nat.add_mod _ _ _
      _ = (z.val + t % c.length) % c.length := by rw [hpred]
      _ = (z.val + t) % c.length := by
        simpa only [Nat.mod_eq_of_lt z.isLt] using
          (Nat.add_mod z.val t c.length).symm
  rw [hm]

theorem get_phaseAt (c : Word) (x t : Fin c.length) :
    c.get (phaseAt c x t) = periodicStream c (x.val+t.val) := by
  unfold periodicStream
  have hlt : (x.val+t.val)%c.length < c.length := (phaseAt c x t).isLt
  rw [List.getElem?_eq_getElem hlt]
  rfl

def phaseEqual (c : Word) (x y : Fin c.length) : Bool :=
  (List.finRange c.length).all (fun t =>
    c.get (phaseAt c x t) == c.get (phaseAt c y t))

theorem phaseEqual_iff_ray (c : Word) (x y : Fin c.length) :
    phaseEqual c x y = true ↔ ∀ t, ray c x t = ray c y t := by
  have hd : 0 < c.length := by have hx := x.isLt; omega
  have hne : c ≠ [] := by intro h; simp [h] at hd
  change phaseEqual c x y = true ↔
    ∀ t, periodicStream c (x.val+t) = periodicStream c (y.val+t)
  rw [← periodic_rotation_iff c hne x.val y.val]
  simp only [phaseEqual, List.all_eq_true]
  constructor
  · intro h t ht
    have h' := h ⟨t,ht⟩ (List.mem_finRange _)
    simpa only [beq_iff_eq, get_phaseAt] using h'
  · intro h t ht
    simp only [beq_iff_eq, get_phaseAt]
    exact h t.val t.isLt

theorem ray_phaseShift (c : Word) (z : Fin c.length) (j t : Nat) :
    ray c (phaseShift c z j) t = ray c z (j+t) := by
  simp only [ray, periodicStream, phaseShift, ← Nat.add_assoc]
  simp only [Nat.add_mod, Nat.mod_mod]

theorem phaseEqual_shift_iff_sameSuffix (c : Word) (z : Fin c.length) (j : Nat) :
    phaseEqual c z (phaseShift c z j) = true ↔ PeriodicTail.SameSuffix (ray c z) 0 j := by
  rw [phaseEqual_iff_ray]
  simp only [ray_phaseShift, PeriodicTail.SameSuffix, Nat.zero_add]

theorem phaseEqual_of_matching_sameSuffix (w c : Word) (hc : 0 < c.length)
    (j : Nat) (hj : 0 < j) (hm : Matches w c hc)
    (hs : PeriodicTail.SameSuffix (prefixStream w c) 0 j) :
    phaseEqual c (alignedPhase c hc w)
      (phaseShift c (alignedPhase c hc w) j) = true := by
  have href := (prefix_sameSuffix_iff w c hc hj).mp hs
  have hray : PeriodicTail.SameSuffix
      (ray c (alignedPhase c hc w)) 0 j := by
    intro t
    simpa [reference, ray] using href.2 t
  exact (phaseEqual_shift_iff_sameSuffix c (alignedPhase c hc w) j).mpr hray

theorem reference_zero_eq (a : Bool) (w c : Word) (hc : 0 < c.length) :
    reference (a :: w) c hc 0 =
      c.get (alignedPhase c hc (a :: w)) := by
  unfold reference periodicStream
  rw [Nat.add_zero, Nat.mod_eq_of_lt (alignedPhase c hc (a :: w)).isLt]
  rw [List.getElem?_eq_getElem (alignedPhase c hc (a :: w)).isLt]
  rfl

theorem no_sameSuffix_of_mismatch {s r : Nat → Bool} {d N m i j : Nat}
    (hd : 0 < d) (hr : PeriodicTail.Periodic r d)
    (hm : PeriodicTail.MatchesFrom s r N) (hmi : i ≤ m)
    (hmis : s m ≠ r m) (hij : i < j)
    (hsame : PeriodicTail.SameSuffix s i j) : False := by
  have hfrom :=
    (PeriodicTail.eventually_sameSuffix_iff hd hr hm hij).mp hsame
  exact hmis (hfrom.1 m hmi)
def flaggedIn (I : Instance k) (p : Fin k) (b : Bucket k) : Bool :=
  (List.finRange k).any (fun r =>
    bucketHas b r && (I.flags.get p).get r)
def hasConflict (I : Instance k) (c : Word) (s : State k c)
    (newPhase : Fin c.length) (p : Fin k) : Bool :=
  (List.finRange c.length).any (fun z =>
    phaseEqual c newPhase z && flaggedIn I p (s.buckets.get z))

def bucketContainsAll (I : Instance k) (c : Word) (s : State k c)
    (p : Fin k) (w : Word) : Prop :=
  ∀ i, i ≤ w.length → ∀ r,
    runFrom I p (w.take i) = some r →
      bucketHas (s.buckets.get (phaseShift c s.phase i)) r = true

def ScanInvariant (I : Instance k) (c : Word) (hc : 0 < c.length)
    (s : State k c) (p q : Fin k) (w : Word) : Prop :=
  s.current = p ∧
  SafeRun I p w q ∧
  GoodFrom I p w c ∧
  ((s.matching = true ∧
      s.phase = alignedPhase c hc w ∧
      Matches w c hc ∧
      bucketContainsAll I c s p w) ∨
    (s.matching = false ∧ ¬ Matches w c hc))
def falseState (s : State k c) (p : Fin k) : State k c :=
  { current := p, phase := ⟨0, by have hz := s.phase.isLt; omega⟩, matching := false,
    buckets := emptyBuckets k c.length }
def seedState (q : Fin k) (c : Word) (h : 0 < c.length) : State k c :=
  { current := q, phase := ⟨0, h⟩, matching := true,
    buckets := (emptyBuckets k c.length).set 0 (singletonBucket q) h }

theorem scanInvariant_seed (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) (hq : safeState I q = true) :
    ScanInvariant I c hc (seedState q c hc) q q [] := by
  refine ⟨rfl, ?_, goodFrom_nil I q c, ?_⟩
  · constructor
    · simp [runFrom]
    · intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst i
      exact (safeCut_zero_iff I q []).mpr hq
  · left
    refine ⟨rfl, ?_, matches_nil c hc, ?_⟩
    · rfl
    · intro i hi r hr
      have hi0 : i = 0 := by simp at hi; omega
      subst i
      have hrq : r = q := by
        apply Option.some.inj
        simpa [runFrom] using hr.symm
      subst r
      rw [phaseShift_zero]
      change bucketHas ((emptyBuckets k c.length).set 0 (singletonBucket q) hc |>.get
        ⟨0, hc⟩) q = true
      simp only [bucketHas]
      change (((emptyBuckets k c.length).set 0 (singletonBucket q) hc)[0]).get q = true
      rw [Vector.getElem_set hc hc]
      exact bucket_get_set_eq (zeroBucket k) q
def matchingState (s : State k c) (p : Fin k) (z : Fin c.length) : State k c :=
  { current := p, phase := z, matching := true,
    buckets := s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt }

theorem alignedPhase_cons_phasePred (c : Word) (hc : 0 < c.length)
    (a : Bool) (w : Word) :
    phasePred c (alignedPhase c hc w) = alignedPhase c hc (a :: w) := by
  apply Fin.ext
  rfl

theorem hasConflict_false_flagged (I : Instance k) (c : Word)
    (s : State k c) (z : Fin c.length) (p : Fin k)
    (h : hasConflict I c s z p = false) (z' : Fin c.length)
    (hz : phaseEqual c z z' = true) :
    flaggedIn I p (s.buckets.get z') = false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  have hb' : flaggedIn I p (s.buckets.get z') = true := by
    exact hb
  have hnot := (List.any_eq_false.mp h) z' (List.mem_finRange _)
  apply hnot
  simp only [Bool.and_eq_true]
  exact ⟨hz, hb'⟩

theorem flagged_false_unflagged (I : Instance k) (p r : Fin k)
    (b : Bucket k) (hb : bucketHas b r = true)
    (hf : flaggedIn I p b = false) :
    unflaggedCheck I (some p) (some r) = true := by
  have hflag : (I.flags.get p).get r = false := by
    apply Bool.eq_false_iff.mpr
    intro hflag'
    have hnot := (List.any_eq_false.mp hf) r (List.mem_finRange _)
    apply hnot
    simp only [Bool.and_eq_true]
    exact ⟨hb, hflag'⟩
  simp [unflaggedCheck, hflag]

theorem matchingState_bucket_has (s : State k c) (p : Fin k)
    (z x : Fin c.length) (r : Fin k)
    (hold : bucketHas (s.buckets.get x) r = true) :
    bucketHas ((matchingState s p z).buckets.get x) r = true := by
  change bucketHas ((s.buckets.set z.val
    (addBucket (s.buckets.get z) p) z.isLt).get x) r = true
  by_cases hx : x = z
  · subst x
    rw [show (s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt).get z =
        addBucket (s.buckets.get z) p by
      change (s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt)[z.val] =
        (addBucket (s.buckets.get z) p)
      rw [Vector.getElem_set z.isLt z.isLt]
      simp]
    exact bucketHas_add (s.buckets.get z) p r hold
  · have hidx : z.val ≠ x.val := by
      intro hval
      apply hx
      exact Fin.ext hval.symm
    change bucketHas ((s.buckets.set z.val
      (addBucket (s.buckets.get z) p) z.isLt).get x) r = true
    rw [show (s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt).get x =
        s.buckets.get x by
      change (s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt)[x.val] =
        s.buckets[x.val]
      rw [Vector.getElem_set z.isLt x.isLt]
      simp [hidx]]
    exact hold

theorem matchingState_has_p (s : State k c) (p : Fin k) (z : Fin c.length) :
    bucketHas ((matchingState s p z).buckets.get z) p = true := by
  change bucketHas ((s.buckets.set z.val
    (addBucket (s.buckets.get z) p) z.isLt).get z) p = true
  rw [show (s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt).get z =
      addBucket (s.buckets.get z) p by
    change (s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt)[z.val] =
      (addBucket (s.buckets.get z) p)
    rw [Vector.getElem_set z.isLt z.isLt]
    simp]
  exact bucket_get_set_eq (s.buckets.get z) p

theorem bucketContainsAll_matching (I : Instance k) (c : Word)
    (s : State k c) (p : Fin k) (a : Bool) (w : Word)
    (he : step I p a = some s.current)
    (hcont : bucketContainsAll I c s s.current w) :
    bucketContainsAll I c (matchingState s p (phasePred c s.phase)) p (a :: w) := by
  intro i hi r hr
  cases i with
  | zero =>
    have hrp : r = p := by
      apply Option.some.inj
      simpa [runFrom] using hr.symm
    subst r
    rw [phaseShift_zero]
    exact matchingState_has_p s p (phasePred c s.phase)
  | succ i =>
    have hi' : i ≤ w.length := by
      simp only [List.length_cons] at hi
      omega
    have hr' : runFrom I s.current (w.take i) = some r := by
      simpa only [run_take_cons I he] using hr
    have hb := hcont i hi' r hr'
    have hshift : phaseShift c (phasePred c s.phase) (i + 1) =
        phaseShift c s.phase i := phaseShift_pred_succ (z := s.phase) i
    change bucketHas ((matchingState s p (phasePred c s.phase)).buckets.get
      (phaseShift c (phasePred c s.phase) (i + 1))) r = true
    rw [hshift]
    exact matchingState_bucket_has s p (phasePred c s.phase)
      (phaseShift c s.phase i) r hb

theorem new_cut_unflagged_of_matching (I : Instance k) (c : Word)
    (hc : 0 < c.length) (s : State k c) (p q : Fin k) (a : Bool)
    (w : Word) (hmw : Matches w c hc)
    (hphase : s.phase = alignedPhase c hc w)
    (hsafe : SafeRun I s.current w q)
    (hcont : bucketContainsAll I c s s.current w)
    (hconf : hasConflict I c s (phasePred c s.phase) p = false)
    (hletter : a = reference (a :: w) c hc 0) :
    ∀ j, j ≤ w.length →
      PeriodicTail.SameSuffix (prefixStream (a :: w) c) 0 (j+1) →
      unflaggedCheck I (some p) (runFrom I s.current (w.take j)) = true := by
  intro j hj hsame
  have hMnew : Matches (a :: w) c hc := by
    apply (matches_cons_iff w c hc a).mpr
    exact ⟨hletter, hmw⟩
  have hzAligned : phasePred c s.phase = alignedPhase c hc (a :: w) := by
    rw [hphase]
    exact alignedPhase_cons_phasePred c hc a w
  have hphaseeqNew := phaseEqual_of_matching_sameSuffix
    (a :: w) c hc (j+1) (by omega) hMnew hsame
  have hphaseeq : phaseEqual c (phasePred c s.phase)
      (phaseShift c (phasePred c s.phase) (j+1)) = true := by
    simpa [hzAligned] using hphaseeqNew
  have hshift : phaseShift c (phasePred c s.phase) (j+1) =
      phaseShift c s.phase j := by
    exact phaseShift_pred_succ (z := s.phase) j
  have hphaseeqOld : phaseEqual c (phasePred c s.phase)
      (phaseShift c s.phase j) = true := by
    rw [← hshift]
    exact hphaseeq
  obtain ⟨r, hr, _⟩ := hsafe.2 j hj
  have hb := hcont j hj r hr
  have hflag := hasConflict_false_flagged I c s (phasePred c s.phase) p
    hconf (phaseShift c s.phase j) hphaseeqOld
  rw [hr]
  exact flagged_false_unflagged I p r
    (s.buckets.get (phaseShift c s.phase j)) hb hflag

theorem new_cut_good_of_not_matches (I : Instance k) (c : Word)
    (hc : 0 < c.length) (p r : Fin k) (a : Bool) (w : Word)
    (hnm : ¬ Matches (a :: w) c hc) :
    ∀ j, j ≤ w.length →
      PeriodicTail.SameSuffix (prefixStream (a :: w) c) 0 (j+1) →
      unflaggedCheck I (some p) (runFrom I r (w.take j)) = true := by
  intro j hj hs
  have hm := matches_of_sameSuffix (a :: w) c hc (by omega) hs
  exact False.elim (hnm hm)

def seed (q : Fin k) (c : Word) : Option (State k c) :=
  if h : 0 < c.length then
    some (seedState q c h)
  else none
def prepend (I : Instance k) (c : Word) (s : State k c)
    (p : Fin k) (a : Bool) : Option (State k c) :=
  if safeState I p = true then
    if step I p a = some s.current then
      if s.matching then
        let z := phasePred c s.phase
        if a == c.get z then
          if hasConflict I c s z p then none
          else some (matchingState s p z)
        else some (falseState s p)
      else some (falseState s p)
    else none
  else none
def successors (I : Instance k) (c : Word) (s : State k c) : List (State k c) :=
  (List.finRange k).flatMap (fun p =>
    [false, true].filterMap (fun a => prepend I c s p a))
def accepts (I : Instance k) (s : State k c) : Bool := decide (s.current = I.initial)

/-- Run the reverse monitor on one supplied finite prefix.  This is an
    independent executable oracle for native differential tests; it performs
    no prefix-length truncation beyond the supplied word. -/
def monitorWord (I : Instance k) (w c : Word) : Bool :=
  match runFrom I I.initial w with
  | none => false
  | some q =>
      if safeState I q = true then
        match seed q c with
        | none => false
        | some start =>
            let finish := (List.range w.length).reverse.foldl
              (fun acc i =>
                acc.bind (fun s =>
                  (stateAt I w i).bind (fun p =>
                    (w[i]?).bind (fun a => prepend I c s p a))))
              (some start)
            finish.map (accepts I) |>.getD false
      else false

/- A labelled reverse path remembers the letters used while scanning from the
   cycle endpoint back to the initial control.  Its word is therefore built by
   consing each newly discovered predecessor letter. -/
inductive LPath (I : Instance k) (c : Word) (x : State k c) :
    State k c → Word → Prop
  | refl : LPath I c x x []
  | step {y z : State k c} {w : Word} {p : Fin k} {a : Bool} :
      LPath I c x y w → prepend I c y p a = some z →
        LPath I c x z (a :: w)

inductive Path (I : Instance k) (c : Word) (x : State k c) :
    State k c → Prop
  | refl : Path I c x x
  | step {y z : State k c} :
      Path I c x y → z ∈ successors I c y → Path I c x z
theorem mem_successors {I : Instance k} {c : Word} {s t : State k c} :
    t ∈ successors I c s ↔
      ∃ p : Fin k, ∃ a : Bool, prepend I c s p a = some t := by
  constructor
  · intro h
    simp only [successors, List.mem_flatMap] at h
    obtain ⟨p, hp, h⟩ := h
    simp only [List.mem_filterMap] at h
    obtain ⟨a, ha, ht⟩ := h
    exact ⟨p, a, ht⟩
  · rintro ⟨p, a, h⟩
    apply List.mem_flatMap.mpr
    refine ⟨p, List.mem_finRange _, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨a, by simp, h⟩

theorem lpath_to_path {I : Instance k} {c : Word} {x y : State k c} {w : Word}
    (h : LPath I c x y w) : Path I c x y := by
  induction h with
  | refl => exact Path.refl
  | step hpath hstep ih =>
      exact Path.step ih ((mem_successors).2 ⟨_, _, hstep⟩)

theorem path_to_lpath {I : Instance k} {c : Word} {x y : State k c}
    (h : Path I c x y) : ∃ w, LPath I c x y w := by
  induction h with
  | refl => exact ⟨[], LPath.refl⟩
  | @step y z hpath hsucc ih =>
      rcases ih with ⟨w, hw⟩
      rcases (mem_successors).1 hsucc with ⟨p, a, hstep⟩
      exact ⟨a :: w, LPath.step hw hstep⟩
theorem prepend_some_safe {I : Instance k} {c : Word} {s t : State k c}
    {p : Fin k} {a : Bool} (h : prepend I c s p a = some t) :
    safeState I p = true ∧ step I p a = some s.current := by
  unfold prepend at h
  by_cases hp : safeState I p = true
  · by_cases he : step I p a = some s.current
    · simp [hp, he] at h
      exact ⟨hp, he⟩
    · simp [hp, he] at h
  · simp [hp] at h
theorem prepend_some_current {I : Instance k} {c : Word} {s t : State k c}
    {p : Fin k} {a : Bool} (h : prepend I c s p a = some t) :
    t.current = p := by
  have hs := prepend_some_safe h
  unfold prepend at h
  rw [if_pos hs.1, if_pos hs.2] at h
  by_cases hm : s.matching = true
  · rw [if_pos hm] at h
    let z := phasePred c s.phase
    by_cases ha : a == c.get z
    · rw [if_pos ha] at h
      by_cases hc : hasConflict I c s z p = true
      · rw [if_pos hc] at h
        simp at h
      · rw [if_neg hc] at h
        have hh := congrArg State.current (Option.some.inj h)
        simpa [matchingState] using hh.symm
    · rw [if_neg ha] at h
      have hh := congrArg State.current (Option.some.inj h)
      simpa [falseState] using hh.symm
  · rw [if_neg hm] at h
    have hh := congrArg State.current (Option.some.inj h)
    simpa [falseState] using hh.symm
theorem seed_some (q : Fin k) (c : Word) (h : 0 < c.length) :
    seed q c = some (seedState q c h) := by
  simp [seed, h]
theorem seed_none_of_empty {q : Fin k} : seed q ([] : Word) = none := by
  simp [seed]
theorem accepts_iff {I : Instance k} {s : State k c} :
    accepts I s = true ↔ s.current = I.initial := by
  simp [accepts]
theorem scanInvariant_step (I : Instance k) (c : Word) (hc : 0 < c.length)
    (s : State k c) (p q : Fin k) (a : Bool) (w : Word) (t : State k c)
    (hinv : ScanInvariant I c hc s s.current q w)
    (hpre : prepend I c s p a = some t) :
    ScanInvariant I c hc t p q (a :: w) := by
  rcases hinv with ⟨hcur, hsafe, hgood, hmode⟩
  have hstep := prepend_some_safe hpre
  have htcur := prepend_some_current hpre
  have hsafeNew : SafeRun I p (a :: w) q := by
    apply (safeRun_cons_iff I p q a w).mpr
    exact ⟨hstep.1, s.current, hstep.2, hsafe⟩
  have hpre' := hpre
  unfold prepend at hpre'
  rw [if_pos hstep.1, if_pos hstep.2] at hpre'
  by_cases hm : s.matching = true
  · rw [if_pos hm] at hpre'
    dsimp at hpre'
    rcases hmode with ⟨hmold, hphase, hmw, hcont⟩ | ⟨hmold, hnot⟩
    · split at hpre' <;> rename_i hletterCond
      · split at hpre' <;> rename_i hconf
        · simp at hpre'
        · have ht : t = matchingState s p (phasePred c s.phase) :=
            (Option.some.inj hpre').symm
          subst t
          have hzAligned : phasePred c s.phase =
              alignedPhase c hc (a :: w) := by
            rw [hphase]
            exact alignedPhase_cons_phasePred c hc a w
          have hcondGet : (a == c.get (phasePred c s.phase)) = true := by
            change (a == c[(phasePred c s.phase).val]) = true
            exact hletterCond
          have haeq : a = c.get (phasePred c s.phase) :=
            beq_iff_eq.mp hcondGet
          have hletter : a = reference (a :: w) c hc 0 := by
            rw [reference_zero_eq, ← hzAligned]
            exact haeq
          have hmwNew : Matches (a :: w) c hc :=
            (matches_cons_iff w c hc a).mpr ⟨hletter, hmw⟩
          have hgoodNew := (goodFrom_cons_iff I hstep.2 w c).mpr
            ⟨hgood, new_cut_unflagged_of_matching I c hc s p q a w hmw
              hphase hsafe hcont (Bool.eq_false_iff.mpr hconf) hletter⟩
          have hcontNew := bucketContainsAll_matching I c s p a w
            hstep.2 hcont
          refine ⟨rfl, hsafeNew, hgoodNew, ?_⟩
          left
          exact ⟨rfl, hzAligned, hmwNew, hcontNew⟩
      · have haneq : a ≠ c.get (phasePred c s.phase) := by
          intro heq
          apply hletterCond
          change (a == c.get (phasePred c s.phase)) = true
          exact beq_iff_eq.mpr heq
        have ht : t = falseState s p := (Option.some.inj hpre').symm
        subst t
        have hzAligned : phasePred c s.phase =
            alignedPhase c hc (a :: w) := by
          rw [hphase]
          exact alignedPhase_cons_phasePred c hc a w
        have hane : a ≠ reference (a :: w) c hc 0 := by
          intro heq
          apply haneq
          rw [reference_zero_eq] at heq
          rw [← hzAligned] at heq
          exact heq
        have hnotNew : ¬ Matches (a :: w) c hc := by
          intro hnew
          exact hane ((matches_cons_iff w c hc a).mp hnew).1
        have hgoodNew := (goodFrom_cons_iff I hstep.2 w c).mpr
          ⟨hgood, new_cut_good_of_not_matches I c hc p s.current a w hnotNew⟩
        refine ⟨rfl, hsafeNew, hgoodNew, ?_⟩
        exact Or.inr ⟨rfl, hnotNew⟩
    · have hfalse : (true : Bool) = false := hm.symm.trans hmold
      cases hfalse
  · rw [if_neg hm] at hpre'
    rcases hmode with ⟨hmold, hphase, hmw, hcont⟩ | ⟨hmold, hnot⟩
    · exact False.elim (hm hmold)
    · have ht : t = falseState s p := (Option.some.inj hpre').symm
      subst t
      have hnotNew : ¬ Matches (a :: w) c hc := by
        intro hnew
        exact hnot ((matches_cons_iff w c hc a).mp hnew).2
      have hgoodNew := (goodFrom_cons_iff I hstep.2 w c).mpr
        ⟨hgood, new_cut_good_of_not_matches I c hc p s.current a w hnotNew⟩
      refine ⟨rfl, hsafeNew, hgoodNew, ?_⟩
      exact Or.inr ⟨rfl, hnotNew⟩

theorem lpath_scanInvariant (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) (hq : safeState I q = true) {t : State k c} {w : Word}
    (hpath : LPath I c (seedState q c hc) t w) :
    ScanInvariant I c hc t t.current q w := by
  induction hpath with
  | refl =>
      exact scanInvariant_seed I c hc q hq
  | @step y z w p a hpath hpre ih =>
      have hz := prepend_some_current hpre
      simpa [hz] using (scanInvariant_step (I := I) (c := c) (hc := hc)
        (s := y) (p := p) (q := q) (a := a) (w := w) (t := z) ih hpre
        )

theorem accepted_path_sound (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) (start : State k c)
    (hseed : seed q c = some start) (hq : safeState I q = true) :
    (∃ finish, Path I c start finish ∧ accepts I finish = true) →
      ∃ w, SafeRun I I.initial w q ∧ PrefixGood I w c := by
  rintro ⟨finish, hpath, haccept⟩
  rcases path_to_lpath hpath with ⟨w, hw⟩
  have hstart : start = seedState q c hc := by
    apply Option.some.inj
    exact hseed.symm.trans (seed_some q c hc)
  subst start
  have hinv := lpath_scanInvariant I c hc q hq hw
  have hacc : finish.current = I.initial := (accepts_iff).mp haccept
  have hsafe : SafeRun I I.initial w q := by
    simpa [hacc] using hinv.2.1
  have hgoodInit : GoodFrom I I.initial w c := by
    simpa [hacc] using hinv.2.2.1
  exact ⟨w, hsafe, (goodFrom_initial I w c).mp hgoodInit⟩

end PeriodicMonitor
end Subtail
