import Subtail.PeriodicRun
import Subtail.InfiniteWitness
import Subtail.RankQueryEnumeration

/- The reverse periodic monitor used by C029. -/
namespace Subtail
namespace PeriodicMonitor
open AbsorbingTerminal
open RankQueryEnumeration
open InfiniteWitness
variable {k : Nat}

def ray (c : Word) (z : Fin c.length) (t : Nat) : Bool :=
  PeriodicRun.periodicStream c (z.val + t)

def GoodFrom (I : Instance k) (p : Fin k) (w c : Word) : Prop :=
  ∀ i j, i < j → j ≤ w.length →
    PeriodicTail.SameSuffix (PeriodicRun.prefixStream w c) i j →
      unflaggedCheck I (runFrom I p (w.take i)) (runFrom I p (w.take j)) = true

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

theorem no_sameSuffix_of_mismatch {s r : Nat → Bool} {d N m i j : Nat}
    (hd : 0 < d) (hr : PeriodicTail.Periodic r d)
    (hm : PeriodicTail.MatchesFrom s r N) (hmi : i ≤ m)
    (hmis : s m ≠ r m) (hij : i < j)
    (hsame : PeriodicTail.SameSuffix s i j) : False := by
  have hfrom :=
    (PeriodicTail.eventually_sameSuffix_iff hd hr hm hij).mp hsame
  exact hmis (hfrom.1 m hmi)
def phaseEqual (c : Word) (x y : Fin c.length) : Bool :=
  (List.finRange c.length).all (fun t =>
    c.get (phaseAt c x t) == c.get (phaseAt c y t))
def flaggedIn (I : Instance k) (p : Fin k) (b : Bucket k) : Bool :=
  (List.finRange k).any (fun r =>
    bucketHas b r && (I.flags.get p).get r)
def hasConflict (I : Instance k) (c : Word) (s : State k c)
    (newPhase : Fin c.length) (p : Fin k) : Bool :=
  (List.finRange c.length).any (fun z =>
    phaseEqual c newPhase z && flaggedIn I p (s.buckets.get z))
def falseState (s : State k c) (p : Fin k) : State k c :=
  { current := p, phase := ⟨0, by have hz := s.phase.isLt; omega⟩, matching := false,
    buckets := emptyBuckets k c.length }
def seedState (q : Fin k) (c : Word) (h : 0 < c.length) : State k c :=
  { current := q, phase := ⟨0, h⟩, matching := true,
    buckets := (emptyBuckets k c.length).set 0 (singletonBucket q) h }
def matchingState (s : State k c) (p : Fin k) (z : Fin c.length) : State k c :=
  { current := p, phase := z, matching := true,
    buckets := s.buckets.set z.val (addBucket (s.buckets.get z) p) z.isLt }
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
end PeriodicMonitor
end Subtail
