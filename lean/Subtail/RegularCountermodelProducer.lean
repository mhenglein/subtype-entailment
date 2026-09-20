import Subtail.RegularLanguageGraph
import Subtail.CanonicalReachability
import Subtail.StackSummaryFast
import Subtail.EntailmentDecision

/-!
Issue 68: constructive finite-seed language compilation and regular graph
production. The public model uses the C084 Graph, original variable roots,
and one unchanged separating word. No finite-tree conclusion is made.

SOURCE DRAFT: this module has not been elaborated in the authoring container.
Its intended all-input theorem is not a report of successful kernel checking.
-/
namespace Subtail.RegularCountermodelProducer

open TreeSemantics CanonicalModel CanonicalReachability
open StackSummary StackReachability ExpressionNormalization RegularTreeCertificate

variable {n : Nat}

/-! Reuse the checked finite saturation rather than enumerate all balanced tables. -/

def popTest (M : System n) : Fin n -> Word -> Fin n -> Bool
  | p, [], q => StackSummaryFast.balancedCheck M p q
  | p, a :: w, q => (List.finRange n).any fun r => (List.finRange n).any fun s =>
      StackSummaryFast.balancedCheck M p r && M.pop a r s && popTest M s w q

@[simp] theorem popTest_correct (M : System n) (p : Fin n) (w : Word) (q : Fin n) :
    popTest M p w q = true <-> Pop M p w q := by
  induction w generalizing p with
  | nil => exact StackSummaryFast.balancedCheck_correct M p q
  | cons a w ih => simp [popTest, Pop, List.any_eq_true, ih, and_assoc]

/-! ## Finite seed suffixes and exact attachment tests -/

abbrev Raw (n : Nat) := Sum (Fin n) Word

def suffixes (seeds : List (Config n)) : List Word :=
  seeds.flatMap fun c => (List.range (c.2.length + 1)).map fun i => c.2.drop i

def rawStates (seeds : List (Config n)) : List (Raw n) :=
  (List.finRange n).map Sum.inl ++ (suffixes seeds).map Sum.inr

@[simp] theorem mem_suffixes (seeds : List (Config n)) (z : Word) :
    z ∈ suffixes seeds <->
      ∃ c, c ∈ seeds ∧ ∃ i, i <= c.2.length ∧ z = c.2.drop i := by
  simp [suffixes, List.mem_flatMap, List.mem_map, Nat.lt_succ_iff, eq_comm]

@[simp] theorem control_mem (seeds : List (Config n)) (q : Fin n) :
    (Sum.inl q : Raw n) ∈ rawStates seeds := by
  simp [rawStates]

@[simp] theorem suffix_mem (seeds : List (Config n)) (z : Word) :
    (Sum.inr z : Raw n) ∈ rawStates seeds <-> z ∈ suffixes seeds := by
  simp [rawStates]

theorem suffix_tail (seeds : List (Config n)) (a : Bool) (z : Word)
    (h : a :: z ∈ suffixes seeds) : z ∈ suffixes seeds := by
  obtain ⟨c, hc, i, hi, he⟩ := (mem_suffixes seeds (a :: z)).mp h
  have hn : ¬ c.2.drop i = [] := by rw [<- he]; simp
  have hlt : i < c.2.length := by
    have hnot : ¬ c.2.length <= i := by
      intro hh
      apply hn
      exact List.drop_eq_nil_iff.mpr hh
    omega
  apply (mem_suffixes seeds z).mpr
  refine ⟨c, hc, i + 1, by omega, ?_⟩
  calc
    z = (a :: z).drop 1 := rfl
    _ = (c.2.drop i).drop 1 := by rw [he]
    _ = c.2.drop (i + 1) := by simp [List.drop_drop, Nat.add_comm]

def Attachment (M : System n) (seeds : List (Config n)) (r : Fin n) (z : Word) : Prop :=
  ∃ c, c ∈ seeds ∧ ∃ i, i <= c.2.length ∧
    Pop M c.1 (c.2.take i) r ∧ z = c.2.drop i

def attachmentCheck (M : System n) (seeds : List (Config n)) (r : Fin n) (z : Word) : Bool :=
  seeds.any fun c => (List.range (c.2.length + 1)).any fun i =>
    popTest M c.1 (c.2.take i) r && decide (z = c.2.drop i)

@[simp] theorem attachmentCheck_correct (M : System n) (seeds : List (Config n))
    (r : Fin n) (z : Word) :
    attachmentCheck M seeds r z = true <-> Attachment M seeds r z := by
  simp [attachmentCheck, Attachment, List.any_eq_true, Nat.lt_succ_iff, and_assoc]

theorem attachment_suffix {M : System n} {seeds : List (Config n)} {r z}
    (h : Attachment M seeds r z) : z ∈ suffixes seeds := by
  obtain ⟨c, hc, i, hi, _, he⟩ := h
  exact (mem_suffixes seeds z).mpr ⟨c, hc, i, hi, he⟩

def joinCheck (M : System n) (seeds : List (Config n)) (q : Fin n) (z : Word) : Bool :=
  (List.finRange n).any fun r =>
    StackSummaryFast.balancedCheck (reverse M) q r && attachmentCheck M seeds r z

@[simp] theorem joinCheck_correct (M : System n) (seeds : List (Config n))
    (q : Fin n) (z : Word) :
    joinCheck M seeds q z = true <->
      ∃ r, Balanced (reverse M) q r ∧ Attachment M seeds r z := by
  simp [joinCheck, List.any_eq_true]

/-! ## An epsilon-free NFA, with separate coverage and reconstruction -/

def rawNext (M : System n) (seeds : List (Config n)) : Raw n -> Bool -> Raw n -> Bool
  | .inl q, a, .inl s => (List.finRange n).any fun r =>
      StackSummaryFast.balancedCheck (reverse M) q r && (reverse M).pop a r s
  | .inl q, a, .inr z => joinCheck M seeds q (a :: z)
  | .inr u, a, .inr z => decide (u = a :: z)
  | .inr _, _, .inl _ => false

def rawFinal (M : System n) (seeds : List (Config n)) : Raw n -> Bool
  | .inl q => joinCheck M seeds q []
  | .inr z => decide (z = [])

def Language (M : System n) (seeds : List (Config n)) : Raw n -> Word -> Prop
  | .inl q, w => ∃ y z r, w = y ++ z ∧
      Pop (reverse M) q y r ∧ Attachment M seeds r z
  | .inr z, w => w = z

/-- Coverage: every propagation run supplies a reverse-pop/suffix factorization. -/
theorem language_coverage (M : System n) (seeds : List (Config n))
    (q : Fin n) (w : Word)
    (h : ∃ c, c ∈ seeds ∧ Reaches M c (q, w)) :
    Language M seeds (.inl q) w := by
  obtain ⟨c, hc, hr⟩ := h
  obtain ⟨x, y, z, r, hx, hy, hp, hq⟩ := reaches_normal hr
  refine ⟨y, z, r, hy, hq, c, hc, x.length, ?_, ?_, ?_⟩
  · simp [hx]
  · simpa [hx] using hp
  · simp [hx]

/-- Reconstruction: an accepted factorization comes from one actual seed/run. -/
theorem language_reconstruction (M : System n) (seeds : List (Config n))
    (q : Fin n) (w : Word) (h : Language M seeds (.inl q) w) :
    ∃ c, c ∈ seeds ∧ Reaches M c (q, w) := by
  obtain ⟨y, z, r, hw, hq, c, hc, i, hi, hp, hz⟩ := h
  subst z
  refine ⟨c, hc, normal_sound ⟨c.2.take i, y, c.2.drop i, r, ?_, hw, hp, hq⟩⟩
  exact (List.take_append_drop i c.2).symm

theorem language_iff_reaches (M : System n) (seeds : List (Config n))
    (q : Fin n) (w : Word) :
    Language M seeds (.inl q) w <->
      ∃ c, c ∈ seeds ∧ Reaches M c (q, w) :=
  ⟨language_reconstruction M seeds q w, language_coverage M seeds q w⟩

theorem rawFinal_correct (M : System n) (seeds : List (Config n)) (p : Raw n) :
    rawFinal M seeds p = true <-> Language M seeds p [] := by
  cases p with
  | inr z => simp [rawFinal, Language, eq_comm]
  | inl q =>
      rw [rawFinal, joinCheck_correct]
      constructor
      · rintro ⟨r, hb, ha⟩
        exact ⟨[], [], r, rfl, hb, ha⟩
      · rintro ⟨y, z, r, he, hp, ha⟩
        have hyz : y = [] ∧ z = [] := List.append_eq_nil_iff.mp he.symm
        rcases hyz with ⟨rfl, rfl⟩
        exact ⟨r, hp, ha⟩

/-- This derivative identity is the NFA correctness invariant. -/
theorem rawNext_correct (M : System n) (seeds : List (Config n))
    (p : Raw n) (hp : p ∈ rawStates seeds) (a : Bool) (w : Word) :
    Language M seeds p (a :: w) <->
      ∃ q, q ∈ rawStates seeds ∧ rawNext M seeds p a q = true ∧
        Language M seeds q w := by
  cases p with
  | inr z =>
      constructor
      · intro he
        change a :: w = z at he
        subst z
        refine ⟨.inr w, ?_, by simp [rawNext], rfl⟩
        exact (suffix_mem seeds w).mpr
          (suffix_tail seeds a w ((suffix_mem seeds (a :: w)).mp hp))
      · rintro ⟨q, _, ht, hl⟩
        cases q with
        | inl q => simp [rawNext] at ht
        | inr u =>
            have he : z = a :: u := by simpa [rawNext] using ht
            change w = u at hl
            change a :: w = z
            rw [he, hl]
  | inl q =>
      constructor
      · rintro ⟨y, z, r, he, hpop, ha⟩
        cases y with
        | nil =>
            have hz : a :: w = z := by simpa using he
            subst z
            refine ⟨.inr w, ?_, ?_, rfl⟩
            · exact (suffix_mem seeds w).mpr
                (suffix_tail seeds a w (attachment_suffix ha))
            · exact (joinCheck_correct M seeds q (a :: w)).mpr ⟨r, hpop, ha⟩
        | cons b ys =>
            have he' : a :: w = b :: (ys ++ z) := he
            have hab : a = b := (List.cons.inj he').1
            have hw : w = ys ++ z := (List.cons.inj he').2
            subst b
            obtain ⟨u, t, hb, ht, hrest⟩ := hpop
            refine ⟨.inl t, control_mem seeds t, ?_, ys, z, r, hw, hrest, ha⟩
            apply List.any_eq_true.mpr
            refine ⟨u, by simp, ?_⟩
            exact Bool.and_eq_true.mpr
              ⟨(StackSummaryFast.balancedCheck_correct _ _ _).mpr hb, ht⟩
      · rintro ⟨p, _, ht, hl⟩
        cases p with
        | inl s =>
            have hs : ∃ r, Balanced (reverse M) q r ∧ (reverse M).pop a r s = true := by
              simpa [rawNext, List.any_eq_true] using ht
            obtain ⟨r, hb, hstep⟩ := hs
            obtain ⟨y, z, t, hw, hpop, ha⟩ := hl
            exact ⟨a :: y, z, t, by simp [hw], ⟨r, s, hb, hstep, hpop⟩, ha⟩
        | inr z =>
            have hw : w = z := hl
            subst w
            obtain ⟨r, hb, ha⟩ := (joinCheck_correct M seeds q (a :: z)).mp ht
            exact ⟨[], a :: z, r, rfl, hb, ha⟩

def nfa (M : System n) (seeds : List (Config n)) : RegularLanguageGraph.NFA (Raw n) where
  carrier := rawStates seeds
  next := rawNext M seeds
  final := rawFinal M seeds

theorem nfa_recognizes (C : List (Constraint n)) (seeds : List (Config n))
    (q : Fin n) (w : Word) :
    RegularLanguageGraph.accepts
      (RegularLanguageGraph.determinize (nfa (systemOf C) seeds))
      (RegularLanguageGraph.initial (nfa (systemOf C) seeds) (.inl q)) w = true <->
    Derived C (seedPred seeds) q w := by
  rw [RegularLanguageGraph.accepts_initial_iff
    (nfa (systemOf C) seeds) (Language (systemOf C) seeds)
    (fun p _ => rawFinal_correct (systemOf C) seeds p)
    (rawNext_correct (systemOf C) seeds) (.inl q) (control_mem seeds q)]
  rw [language_iff_reaches, derived_iff_reaches]
  constructor
  · rintro ⟨c, hc, hr⟩
    exact ⟨c.1, c.2, hc, hr⟩
  · rintro ⟨p, u, hs, hr⟩
    exact ⟨(p, u), hs, hr⟩

/-! ## Constructed graphs, not supplied candidate graphs -/

def canonicalSize (C : List (Constraint n)) (a : Fin n) (w : Word) : Nat :=
  (RegularLanguageGraph.subsetsOf (nfa (systemOf C) (pathList C a w))).length

def canonicalGraph (C : List (Constraint n)) (a : Fin n) (w : Word) :
    Graph (canonicalSize C a w) :=
  RegularLanguageGraph.toGraph
    (RegularLanguageGraph.determinize (nfa (systemOf C) (pathList C a w)))

def canonicalRoot (C : List (Constraint n)) (a : Fin n) (w : Word) (q : Fin n) :
    Fin (canonicalSize C a w) :=
  RegularLanguageGraph.initial (nfa (systemOf C) (pathList C a w)) (.inl q)

/-- Exact at all variables and all words, with no satisfiability assumption. -/
theorem canonicalGraph_exact (C : List (Constraint n)) (a : Fin n) (w : Word)
    (q : Fin n) (u : Word) :
    graphNodes (canonicalGraph C a w) (canonicalRoot C a w q) u = true <->
      Derived C (pathSeeds C a w) q u := by
  let D := RegularLanguageGraph.determinize (nfa (systemOf C) (pathList C a w))
  let root := canonicalRoot C a w q
  have hr : ∀ u, RegularLanguageGraph.accepts D root u = true <->
      Derived C (pathSeeds C a w) q u := by
    intro u
    dsimp only [D, root, canonicalRoot]
    simpa only [pathList_pred] using nfa_recognizes C (pathList C a w) q u
  have hc : PrefixClosed (fun u => RegularLanguageGraph.accepts D root u = true) := by
    intro x y hxy
    exact (hr x).mpr
      (derived_closed (pathSeeds_closed C a w) (pathSeeds_roots C a w) q x y
        ((hr (x ++ y)).mp hxy))
  exact (RegularLanguageGraph.graphNodes_iff D root hc u).trans (hr u)

theorem canonicalGraph_tree (C : List (Constraint n)) (a : Fin n) (w : Word)
    (q : Fin n) :
    treeOf (canonicalGraph C a w) (canonicalRoot C a w q) = canonical C a w q := by
  apply tree_eq_of_nodes
  intro u
  exact canonicalGraph_exact C a w q u

structure Model (n : Nat) where
  size : Nat
  graph : Graph size
  roots : Fin n -> Fin size
  word : Word

def Model.valuation (m : Model n) : Valuation n :=
  fun q => treeOf m.graph (m.roots q)

def normalizedModel (C : List (Constraint n)) (a : Fin n) (w : Word) : Model n where
  size := canonicalSize C a w
  graph := canonicalGraph C a w
  roots := canonicalRoot C a w
  word := w

theorem normalizedModel_valuation (C : List (Constraint n)) (a : Fin n) (w : Word) :
    (normalizedModel C a w).valuation = canonical C a w := by
  funext q
  exact canonicalGraph_tree C a w q

theorem normalizedModel_correct (C : List (Constraint n)) (a b : Fin n) (w : Word)
    (h : separationCheck C a b w = true) :
    Models C (normalizedModel C a w).valuation ∧
      ((normalizedModel C a w).valuation a).nodes w ∧
      ¬ ((normalizedModel C a w).valuation b).nodes w := by
  rw [normalizedModel_valuation]
  obtain ⟨hs, hb⟩ := (separationCheck_correct C a b w).mp h
  exact ⟨closure_models (pathSeeds_closed C a w) (pathSeeds_roots C a w) hs,
    canonical_contains C a w, hb⟩

def inputTest (G : Input n) (s t : Expr n) (w : Word) : Bool :=
  separationCheck (normalized G s t) ((naming G s t).ref s) ((naming G s t).ref t) w

def modelForWord (G : Input n) (s t : Expr n) (w : Word) : Model n :=
  let R := naming G s t
  let m := normalizedModel (normalized G s t) (R.ref s) w
  { size := m.size, graph := m.graph, roots := fun q => m.roots (R.old q), word := w }

/-- Original-input soundness, at the very same word passed to the constructor. -/
theorem modelForWord_correct (G : Input n) (s t : Expr n) (w : Word)
    (h : inputTest G s t w = true) :
    ExprModels G (modelForWord G s t w).valuation ∧
      (eval (modelForWord G s t w).valuation s).nodes w ∧
      ¬ (eval (modelForWord G s t w).valuation t).nodes w := by
  let R := naming G s t
  let eta := (normalizedModel (normalized G s t) (R.ref s) w).valuation
  have hm := normalizedModel_correct (normalized G s t) (R.ref s) (R.ref t) w h
  have hd := normalized_definitions G s t eta hm.1
  have hs := naming_support G s t s (by simp [forest])
  have ht := naming_support G s t t (by simp [forest])
  change ExprModels G (R.restrict eta) ∧
    (eval (R.restrict eta) s).nodes w ∧ ¬ (eval (R.restrict eta) t).nodes w
  refine ⟨restrict_models G s t eta hm.1, ?_, ?_⟩
  · have hleft : (eta (R.ref s)).nodes w := hm.2.1
    rw [representative_correct R eta hd s hs] at hleft
    exact hleft
  · have hright : ¬ (eta (R.ref t)).nodes w := hm.2.2
    rw [representative_correct R eta hd t ht] at hright
    exact hright

theorem exists_input_word (G : Input n) (s t : Expr n) (h : ¬ ExprEntails G s t) :
    ∃ w, inputTest G s t w = true := by
  apply (not_entails_iff_exists_check (normalized G s t)
    ((naming G s t).ref s) ((naming G s t).ref t)).mp
  intro he
  exact h ((normalize_entails_iff G s t).mpr he)

/-! ## Fair search with a proof of termination, not a finite word cutoff -/

def wordsOfLength : Nat -> List Word
  | 0 => [[]]
  | d + 1 => (wordsOfLength d).map (fun w => false :: w) ++
      (wordsOfLength d).map (fun w => true :: w)

theorem word_enumerated (w : Word) : w ∈ wordsOfLength w.length := by
  induction w with
  | nil => simp [wordsOfLength]
  | cons a w ih =>
      cases a <;> simp [wordsOfLength, ih]

def Jump (p : Nat -> Bool) (j i : Nat) : Prop := j = i + 1 ∧ p i = false

theorem accessible_before_hit (p : Nat -> Bool) (i d : Nat) (h : p (i + d) = true) :
    Acc (Jump p) i := by
  induction d generalizing i with
  | zero =>
      refine Acc.intro i ?_
      intro j hj
      have hi : p i = true := by simpa using h
      simp [Jump, hi] at hj
  | succ d ih =>
      refine Acc.intro i ?_
      intro j hj
      rcases hj with ⟨rfl, _⟩
      apply ih (i + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The accessibility proof is erased; the executable code only tests successive p i. -/
def seekAcc (p : Nat -> Bool) (i : Nat) (acc : Acc (Jump p) i) :
    {j : Nat // p j = true} :=
  if hi : p i = true then ⟨i, hi⟩
  else seekAcc p (i + 1) (acc.inv ⟨rfl, by cases hp : p i <;> simp_all⟩)
termination_by Subtype.mk i acc
decreasing_by
  change Jump p (i + 1) i
  exact ⟨rfl, by cases hp : p i <;> simp_all⟩

def seek (p : Nat -> Bool) (h : ∃ d, p d = true) : {j : Nat // p j = true} :=
  seekAcc p 0 (by
    obtain ⟨d, hd⟩ := h
    apply accessible_before_hit p 0 d
    simpa using hd)

def pickWord (f : Word -> Bool) (xs : List Word) (h : xs.any f = true) :
    {w : Word // f w = true} :=
  match xs with
  | [] => False.elim (by simp at h)
  | x :: xs =>
      if hx : f x = true then ⟨x, hx⟩
      else pickWord f xs (by cases hf : f x <;> simp_all)
termination_by structural xs

def findWord (G : Input n) (s t : Expr n) (h : ¬ ExprEntails G s t) :
    {w : Word // inputTest G s t w = true} :=
  let p := fun d => (wordsOfLength d).any (inputTest G s t)
  let d := seek p (by
    obtain ⟨w, hw⟩ := exists_input_word G s t h
    exact ⟨w.length, List.any_eq_true.mpr ⟨w, word_enumerated w, hw⟩⟩)
  pickWord (inputTest G s t) (wordsOfLength d.val) d.property

def produceNegative (G : Input n) (s t : Expr n) (h : ¬ ExprEntails G s t) : Model n :=
  modelForWord G s t (findWord G s t h).val

theorem produceNegative_correct (G : Input n) (s t : Expr n)
    (h : ¬ ExprEntails G s t) :
    ExprModels G (produceNegative G s t h).valuation ∧
      (eval (produceNegative G s t h).valuation s).nodes (produceNegative G s t h).word ∧
      ¬ (eval (produceNegative G s t h).valuation t).nodes (produceNegative G s t h).word := by
  exact modelForWord_correct G s t (findWord G s t h).val (findWord G s t h).property

/-- C081 handles positive inputs; fair constructive extraction handles negative ones. -/
def produce (G : Input n) (s t : Expr n) : Option (Model n) :=
  if hd : EntailmentDecision.entailsCheck G s t = true then none
  else some (produceNegative G s t (fun he =>
    hd ((EntailmentDecision.entailsCheck_correct G s t).mpr he)))

theorem produce_none_iff (G : Input n) (s t : Expr n) :
    produce G s t = none <-> ExprEntails G s t := by
  by_cases hd : EntailmentDecision.entailsCheck G s t = true
  · simp [produce, hd, (EntailmentDecision.entailsCheck_correct G s t).mp hd]
  · have hn : ¬ ExprEntails G s t := fun h =>
        hd ((EntailmentDecision.entailsCheck_correct G s t).mpr h)
    simp [produce, hd, hn]

theorem produce_sound (G : Input n) (s t : Expr n) (m : Model n)
    (h : produce G s t = some m) :
    ExprModels G m.valuation ∧ (eval m.valuation s).nodes m.word ∧
      ¬ (eval m.valuation t).nodes m.word := by
  by_cases hd : EntailmentDecision.entailsCheck G s t = true
  · simp [produce, hd] at h
  · have hn : ¬ ExprEntails G s t := fun he =>
        hd ((EntailmentDecision.entailsCheck_correct G s t).mpr he)
    have hm : produceNegative G s t hn = m := by simpa [produce, hd] using h
    rw [<- hm]
    exact produceNegative_correct G s t hn

theorem produce_complete (G : Input n) (s t : Expr n)
    (h : ¬ ExprEntails G s t) : ∃ m, produce G s t = some m := by
  have hd : ¬ EntailmentDecision.entailsCheck G s t = true := fun he =>
    h ((EntailmentDecision.entailsCheck_correct G s t).mp he)
  refine ⟨produceNegative G s t h, ?_⟩
  simp [produce, hd]

end Subtail.RegularCountermodelProducer
