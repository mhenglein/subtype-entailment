import Subtail.PeriodicMonitor
import Subtail.PeriodicGood

/-! Every safe, good periodic prefix is represented by an accepted reverse path.
The completeness carrier excludes spurious bucket members; the companion
soundness invariant ensures that no genuine member is missing. -/
namespace Subtail.PeriodicMonitorComplete
open AbsorbingTerminal PeriodicRun PeriodicRotation PeriodicGood PeriodicMonitor
variable {k : Nat}

theorem vector_get_set (v : Vector α n) (i j : Fin n) (a : α) :
    (v.set i.val a).get j = if i = j then a else v.get j := by
  change (v.set i.val a)[j.val] = if i = j then a else v[j.val]
  rw [Vector.getElem_set i.isLt j.isLt]
  by_cases h : i = j
  · subst j; simp
  · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
    simp [h, hv]

theorem bucket_add_iff (b : Bucket k) (p r : Fin k) :
    bucketHas (addBucket b p) r = true ↔ p = r ∨ bucketHas b r = true := by
  unfold bucketHas addBucket
  rw [vector_get_set]
  by_cases h : p = r <;> simp [h]

theorem matching_member_iff (s : State k c) (p r : Fin k) (z x : Fin c.length) :
    bucketHas ((matchingState s p z).buckets.get x) r = true ↔
      (z = x ∧ p = r) ∨ bucketHas (s.buckets.get x) r = true := by
  change bucketHas ((s.buckets.set z.val (addBucket (s.buckets.get z) p)).get x) r = true ↔ _
  rw [vector_get_set]
  by_cases h : z = x
  · subst x; simp only [ite_true, bucket_add_iff, true_and]
  · simp [h]

/-- Each stored member comes from an actual cut at precisely that phase. -/
def BucketSound (I : Instance k) (c : Word) (s : State k c)
    (p : Fin k) (w : Word) : Prop :=
  ∀ z r, bucketHas (s.buckets.get z) r = true →
    ∃ i, i ≤ w.length ∧ phaseShift c s.phase i = z ∧
      runFrom I p (w.take i) = some r

/-- Only matching states inspect buckets; completeness needs no carrier for
reset buckets in a nonmatching state. Forward soundness checks that branch. -/
def BackInvariant (I : Instance k) (c : Word) (hc : 0 < c.length)
    (s : State k c) (p : Fin k) (w : Word) : Prop :=
  s.current = p ∧ (s.matching = true →
    s.phase = alignedPhase c hc w ∧ Matches w c hc ∧ BucketSound I c s p w)

theorem seed_bucket_sound (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) : BucketSound I c (seedState q c hc) q [] := by
  intro z r hr
  change bucketHas ((emptyBuckets k c.length).set 0 (singletonBucket q) hc |>.get z) r = true at hr
  have hset := vector_get_set (emptyBuckets k c.length) (⟨0,hc⟩ : Fin c.length) z (singletonBucket q)
  rw [hset] at hr
  by_cases hz : (⟨0,hc⟩ : Fin c.length) = z
  · rw [if_pos hz] at hr
    have hr' : q = r := by
      unfold bucketHas singletonBucket at hr
      rw [vector_get_set] at hr
      by_cases hq : q = r
      · exact hq
      · simp [hq, zeroBucket, Vector.get] at hr
    subst r
    refine ⟨0, by simp, ?_, rfl⟩
    simpa only [phaseShift_zero, seedState] using hz
  · rw [if_neg hz] at hr
    simp [bucketHas, emptyBuckets, zeroBucket, Vector.get] at hr

theorem seed_back (I : Instance k) (c : Word) (hc : 0 < c.length) (q : Fin k) :
    BackInvariant I c hc (seedState q c hc) q [] := by
  exact ⟨rfl, fun _ => ⟨rfl, matches_nil c hc, seed_bucket_sound I c hc q⟩⟩

theorem false_back (I : Instance k) (c : Word) (hc : 0 < c.length)
    (s : State k c) (p : Fin k) (w : Word) :
    BackInvariant I c hc (falseState s p) p w := by
  exact ⟨rfl, by simp [falseState]⟩

theorem matching_bucket_sound (I : Instance k) (c : Word) (s : State k c)
    (p : Fin k) (a : Bool) (w : Word)
    (he : step I p a = some s.current) (hb : BucketSound I c s s.current w) :
    BucketSound I c (matchingState s p (phasePred c s.phase)) p (a::w) := by
  intro z r hr
  rcases (matching_member_iff s p r (phasePred c s.phase) z).mp hr with hnew | hold
  · obtain ⟨hz,hp⟩ := hnew
    subst r
    refine ⟨0, by simp, ?_, rfl⟩
    simpa only [phaseShift_zero, matchingState] using hz
  · obtain ⟨i,hi,hz,hr⟩ := hb z r hold
    refine ⟨i+1, by simp; omega, ?_, ?_⟩
    · change phaseShift c (phasePred c s.phase) (i+1) = z
      exact (phaseShift_pred_succ s.phase i).trans hz
    · rw [run_take_cons I he]
      exact hr


theorem aligned_predecessor (c : Word) (hc : 0 < c.length) (a : Bool) (w : Word) :
    phasePred c (alignedPhase c hc w) = alignedPhase c hc (a::w) := by rfl

theorem reference_head (w c : Word) (hc : 0 < c.length) :
    reference w c hc 0 = c.get (alignedPhase c hc w) := by
  unfold reference periodicStream
  rw [Nat.add_zero, Nat.mod_eq_of_lt (alignedPhase c hc w).isLt]
  rw [List.getElem?_eq_getElem (alignedPhase c hc w).isLt]
  rfl

/-- Goodness rules out exactly the conflicts tested by a matching prepend.
The bucket member supplies a real target cut, so no extra hypothesis on
unreachable states or flags is introduced. -/
theorem good_no_conflict (I : Instance k) (c : Word) (hc : 0 < c.length)
    (s : State k c) (p : Fin k) (a : Bool) (w : Word)
    (he : step I p a = some s.current)
    (hphase : s.phase = alignedPhase c hc w)
    (hmatch : Matches (a::w) c hc)
    (hb : BucketSound I c s s.current w)
    (hg : PeriodicGood.GoodFrom I p (a::w) c) :
    hasConflict I c s (phasePred c s.phase) p = false := by
  apply Bool.eq_false_iff.mpr
  intro hconf
  obtain ⟨z, hz, hpair⟩ := List.any_eq_true.mp hconf
  obtain ⟨heq,hf⟩ := Bool.and_eq_true_iff.mp hpair
  obtain ⟨r, hr, hpair⟩ := List.any_eq_true.mp hf
  obtain ⟨hmem,hflag⟩ := Bool.and_eq_true_iff.mp hpair
  obtain ⟨j,hj,hz,hrun⟩ := hb z r hmem
  have hnewphase : phasePred c s.phase = alignedPhase c hc (a::w) := by
    rw [hphase, aligned_predecessor]
  have hrot : phaseEqual c (phasePred c s.phase)
      (phaseShift c (phasePred c s.phase) (j+1)) = true := by
    rw [phaseShift_pred_succ, hz]
    exact heq
  have hray := (PeriodicMonitor.phaseEqual_shift_iff_sameSuffix c
    (phasePred c s.phase) (j+1)).mp hrot
  have href : PeriodicTail.SameSuffix (reference (a::w) c hc) 0 (j+1) := by
    rw [hnewphase] at hray
    exact hray
  have hsame : PeriodicTail.SameSuffix (prefixStream (a::w) c) 0 (j+1) :=
    (prefix_sameSuffix_iff (a::w) c hc (by omega)).mpr ⟨hmatch,href⟩
  have hun := ((goodFrom_cons_iff I he w c).mp hg).2 j hj hsame
  simp [hrun, unflaggedCheck, hflag] at hun

/-- Construct a labelled path for every safe good word, with exact enough
bucket provenance to keep all subsequent prepends possible. -/
theorem good_has_lpath (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) (w : Word) (p : Fin k)
    (hw : SafeRun I p w q) (hg : PeriodicGood.GoodFrom I p w c) :
    ∃ s, LPath I c (seedState q c hc) s w ∧ BackInvariant I c hc s p w := by
  induction w generalizing p with
  | nil =>
    have hp : p = q := by simpa [runFrom] using hw.1
    subst p
    exact ⟨seedState q c hc, LPath.refl, seed_back I c hc q⟩
  | cons a w ih =>
    obtain ⟨hp,r,he,htail⟩ := (safeRun_cons_iff I p q a w).mp hw
    obtain ⟨hgTail,hgNew⟩ := (goodFrom_cons_iff I he w c).mp hg
    obtain ⟨s,hs,hback⟩ := ih r htail hgTail
    have he' : step I p a = some s.current := by rw [hback.1]; exact he
    by_cases hm : s.matching = true
    · obtain ⟨hphase,hmatch,hb⟩ := hback.2 hm
      have hb' : BucketSound I c s s.current w := by rw [hback.1]; exact hb
      have hz : phasePred c s.phase = alignedPhase c hc (a::w) := by
        rw [hphase, aligned_predecessor]
      by_cases ha : a = c.get (phasePred c s.phase)
      · have hmatch' : Matches (a::w) c hc := by
          apply (matches_cons_iff w c hc a).mpr
          refine ⟨?_,hmatch⟩
          rw [reference_head, ← hz]
          exact ha
        have hconf := good_no_conflict I c hc s p a w he' hphase hmatch' hb' hg
        refine ⟨matchingState s p (phasePred c s.phase), LPath.step (p := p) hs ?_, ?_⟩
        · unfold prepend
          rw [if_pos hp, if_pos he', if_pos hm]
          have haB : (a == c.get (phasePred c s.phase)) = true := beq_iff_eq.mpr ha
          rw [if_pos haB, if_neg (by simp [hconf])]
        · refine ⟨rfl, fun _ => ⟨hz, hmatch', ?_⟩⟩
          exact matching_bucket_sound I c s p a w he' hb'
      · refine ⟨falseState s p, LPath.step (p := p) hs ?_, false_back I c hc s p (a::w)⟩
        unfold prepend
        rw [if_pos hp, if_pos he', if_pos hm]
        have haB : ¬ (a == c.get (phasePred c s.phase)) = true := by
          simpa only [beq_iff_eq] using ha
        rw [if_neg haB]
    · refine ⟨falseState s p, LPath.step (p := p) hs ?_, false_back I c hc s p (a::w)⟩
      unfold prepend
      rw [if_pos hp, if_pos he', if_neg hm]

/-- The reverse monitor does not miss any safe prefix with the required
ordered infinite-suffix comparisons. -/
theorem good_has_accepted_path (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) (w : Word) (hw : SafeRun I I.initial w q)
    (hg : PrefixGood I w c) :
    ∃ s, Path I c (seedState q c hc) s ∧ accepts I s = true := by
  obtain ⟨s,hs,hb⟩ := good_has_lpath I c hc q w I.initial hw hg
  exact ⟨s, lpath_to_path hs, accepts_iff.mpr hb.1⟩


/-- Exact accepted-prefix language, with seed safety kept explicit. -/
theorem accepted_path_iff (I : Instance k) (c : Word) (hc : 0 < c.length)
    (q : Fin k) (start : State k c)
    (hseed : seed q c = some start) (hq : safeState I q = true) :
    (∃ finish, Path I c start finish ∧ accepts I finish = true) ↔
      ∃ w, SafeRun I I.initial w q ∧ PrefixGood I w c := by
  constructor
  · exact accepted_path_sound I c hc q start hseed hq
  · rintro ⟨w,hw,hg⟩
    have hstart : start = seedState q c hc := by
      apply Option.some.inj
      exact hseed.symm.trans (seed_some q c hc)
    subst start
    exact good_has_accepted_path I c hc q w hw hg

end Subtail.PeriodicMonitorComplete
