import Subtail.StackSummary

/-!
Exact normal form and finite decision of push/pop/epsilon reachability.
No stack-height, derivation-length or word-length cutoff is used.
-/
namespace Subtail
namespace StackReachability
open StackSummary

abbrev Config (n : Nat) := Fin n × Word

inductive Step (M : System n) : Config n -> Config n -> Prop where
  | eps {p q w} : M.eps p q = true -> Step M (p,w) (q,w)
  | push {a p q w} : M.push a p q = true -> Step M (p,w) (q,a::w)
  | pop {a p q w} : M.pop a p q = true -> Step M (p,a::w) (q,w)

inductive Reaches (M : System n) : Config n -> Config n -> Prop where
  | refl {c} : Reaches M c c
  | tail {c d e} : Reaches M c d -> Step M d e -> Reaches M c e

theorem reaches_one {M : System n} {c d} (h : Step M c d) : Reaches M c d :=
  .tail .refl h

theorem reaches_trans {M : System n} {c d e}
    (h : Reaches M c d) (g : Reaches M d e) : Reaches M c e := by
  induction g with
  | refl => exact h
  | tail _ hs ih => exact .tail ih hs

theorem step_suffix {M : System n} {c d} (h : Step M c d) (z : Word) :
    Step M (c.1,c.2 ++ z) (d.1,d.2 ++ z) := by
  cases h with
  | eps h => exact .eps h
  | push h => exact .push h
  | pop h => exact .pop h

theorem reaches_suffix {M : System n} {c d} (h : Reaches M c d) (z : Word) :
    Reaches M (c.1,c.2 ++ z) (d.1,d.2 ++ z) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact .tail ih (step_suffix hs z)

theorem step_reverse {M : System n} {c d} (h : Step M c d) :
    Step (reverse M) d c := by
  cases h with
  | eps h => exact .eps h
  | push h => exact .pop h
  | pop h => exact .push h

theorem reaches_reverse {M : System n} {c d} (h : Reaches M c d) :
    Reaches (reverse M) d c := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact reaches_trans (reaches_one (step_reverse hs)) ih

theorem balanced_sound {M : System n} {p q} (h : Balanced M p q) :
    ∀ z, Reaches M (p,z) (q,z) := by
  induction h with
  | refl p => intro z; exact .refl
  | eps h => intro z; exact reaches_one (.eps h)
  | trans _ _ ih1 ih2 => intro z; exact reaches_trans (ih1 z) (ih2 z)
  | @wrap a p q r s hp _ hq ih =>
    intro z
    exact reaches_trans (reaches_one (.push hp))
      (reaches_trans (ih (a::z)) (reaches_one (.pop hq)))

/-- Regular consuming paths with balanced excursions between pops. -/
def Pop (M : System n) : Fin n -> Word -> Fin n -> Prop
  | p, [], q => Balanced M p q
  | p, a::w, q => ∃ r s, Balanced M p r ∧ M.pop a r s = true ∧ Pop M s w q

theorem pop_pre {M : System n} {p r q w}
    (h : Balanced M p r) (g : Pop M r w q) : Pop M p w q := by
  induction w generalizing p r with
  | nil => exact .trans h g
  | cons a w ih =>
    obtain ⟨s,t,hs,hp,hrest⟩ := g
    exact ⟨s,t,.trans h hs,hp,hrest⟩

theorem pop_post {M : System n} {p r q w}
    (g : Pop M p w r) (h : Balanced M r q) : Pop M p w q := by
  induction w generalizing p with
  | nil => exact .trans g h
  | cons a w ih =>
    obtain ⟨s,t,hs,hp,hrest⟩ := g
    exact ⟨s,t,hs,hp,ih hrest⟩

theorem pop_append {M : System n} {p r q u v}
    (h : Pop M p u r) (g : Pop M r v q) : Pop M p (u ++ v) q := by
  induction u generalizing p with
  | nil => exact pop_pre h g
  | cons a u ih =>
    obtain ⟨s,t,hs,hp,hrest⟩ := h
    exact ⟨s,t,hs,hp,ih hrest⟩

theorem pop_sound {M : System n} {p q w} (h : Pop M p w q) (z : Word) :
    Reaches M (p,w ++ z) (q,z) := by
  induction w generalizing p with
  | nil => exact balanced_sound h z
  | cons a w ih =>
    obtain ⟨r,s,hb,hp,hr⟩ := h
    exact reaches_trans (balanced_sound hb (a :: (w ++ z)))
      (reaches_trans (reaches_one (.pop hp)) (ih hr))

/-- Pop to a shared untouched tail, then reverse a Pop run of the reversed system. -/
def Normal (M : System n) (p : Fin n) (u : Word) (q : Fin n) (v : Word) : Prop :=
  ∃ x y z m, u = x ++ z ∧ v = y ++ z ∧
    Pop M p x m ∧ Pop (reverse M) q y m

theorem normal_sound {M : System n} {p u q v} (h : Normal M p u q v) :
    Reaches M (p,u) (q,v) := by
  obtain ⟨x,y,z,m,rfl,rfl,hp,hq⟩ := h
  have hr := reaches_reverse (pop_sound hq z)
  simp only [reverse_reverse] at hr
  exact reaches_trans (pop_sound hp z) hr

theorem normal_refl (M : System n) (p : Fin n) (w : Word) : Normal M p w p w :=
  ⟨[],[],w,p,rfl,rfl,Balanced.refl p,Balanced.refl p⟩

theorem normal_eps {M : System n} {p u q v r}
    (h : Normal M p u q v) (he : M.eps q r = true) : Normal M p u r v := by
  obtain ⟨x,y,z,m,hx,hy,hp,hq⟩ := h
  exact ⟨x,y,z,m,hx,hy,hp,pop_pre (Balanced.eps he) hq⟩

theorem normal_push {M : System n} {p u q v r a}
    (h : Normal M p u q v) (he : M.push a q r = true) : Normal M p u r (a::v) := by
  obtain ⟨x,y,z,m,hx,hy,hp,hq⟩ := h
  refine ⟨x,a::y,z,m,hx,?_,hp,?_⟩
  · simp [hy]
  · exact ⟨r,q,Balanced.refl r,he,hq⟩

/-- The only nontrivial normalization case: a pop either cancels a summarized
push or consumes one symbol of the formerly untouched common tail. -/
theorem normal_pop {M : System n} {p u q v r a}
    (h : Normal M p u q (a::v)) (he : M.pop a q r = true) : Normal M p u r v := by
  obtain ⟨x,y,z,m,hx,hy,hp,hq⟩ := h
  cases y with
  | nil =>
    simp only [List.nil_append] at hy
    subst z
    have hbal : Balanced M m q := (balanced_reverse_iff M q m).mp hq
    have hone : Pop M m [a] r := ⟨q,r,hbal,he,Balanced.refl r⟩
    refine ⟨x ++ [a],[],v,r,?_,rfl,pop_append hp hone,Balanced.refl r⟩
    simpa [List.append_assoc] using hx
  | cons b ys =>
    simp only [List.cons_append] at hy
    have hab := (List.cons.inj hy).1
    have hv := (List.cons.inj hy).2
    subst b
    obtain ⟨r0,s0,hbal,hpush,hrest⟩ := hq
    have hbr : Balanced M s0 r :=
      Balanced.wrap hpush ((balanced_reverse_iff M q r0).mp hbal) he
    exact ⟨x,ys,z,m,hx,hv,hp,pop_pre (balanced_reverse hbr) hrest⟩

theorem normal_step {M : System n} {p u} {c d : Config n}
    (h : Normal M p u c.1 c.2) (hs : Step M c d) : Normal M p u d.1 d.2 := by
  cases hs with
  | eps he => exact normal_eps h he
  | push he => exact normal_push h he
  | pop he => exact normal_pop h he

theorem reaches_normal {M : System n} {c d} (h : Reaches M c d) :
    Normal M c.1 c.2 d.1 d.2 := by
  induction h with
  | refl => exact normal_refl _ _ _
  | tail _ hs ih => exact normal_step ih hs

theorem reaches_iff_normal (M : System n) (p : Fin n) (u : Word) (q : Fin n) (v : Word) :
    Reaches M (p,u) (q,v) ↔ Normal M p u q v :=
  ⟨reaches_normal,normal_sound⟩

theorem pop_iff_reaches_empty (M : System n) (p : Fin n) (w : Word) (q : Fin n) :
    Pop M p w q ↔ Reaches M (p,w) (q,[]) := by
  constructor
  · intro h; simpa using pop_sound h []
  · intro h
    obtain ⟨x,y,z,m,hx,hy,hp,hq⟩ := reaches_normal h
    have hyz : y = [] ∧ z = [] := by
      cases y with
      | nil => exact ⟨rfl,by simpa using hy.symm⟩
      | cons a ys => simp at hy
    rcases hyz with ⟨rfl,rfl⟩
    simp only [List.append_nil] at hx
    subst x
    exact pop_post hp ((balanced_reverse_iff M q m).mp hq)

def popCheck (M : System n) : Fin n -> Word -> Fin n -> Bool
  | p, [], q => balancedCheck M p q
  | p, a::w, q => (List.finRange n).any fun r => (List.finRange n).any fun s =>
      balancedCheck M p r && M.pop a r s && popCheck M s w q

@[simp] theorem popCheck_correct (M : System n) (p : Fin n) (w : Word) (q : Fin n) :
    popCheck M p w q = true ↔ Pop M p w q := by
  induction w generalizing p with
  | nil => exact balancedCheck_correct M p q
  | cons a w ih => simp [popCheck,Pop,List.any_eq_true,ih,and_assoc]

def CutNormal (M : System n) (p : Fin n) (u : Word) (q : Fin n) (v : Word) : Prop :=
  ∃ i, i <= u.length ∧ ∃ j, j <= v.length ∧ ∃ m,
    u.drop i = v.drop j ∧ Pop M p (u.take i) m ∧ Pop (reverse M) q (v.take j) m

theorem normal_iff_cut (M : System n) (p : Fin n) (u : Word) (q : Fin n) (v : Word) :
    Normal M p u q v ↔ CutNormal M p u q v := by
  constructor
  · rintro ⟨x,y,z,m,rfl,rfl,hp,hq⟩
    refine ⟨x.length,by simp,y.length,by simp,m,?_,?_,?_⟩
    · simp
    · simpa using hp
    · simpa using hq
  · rintro ⟨i,hi,j,hj,m,he,hp,hq⟩
    refine ⟨u.take i,v.take j,u.drop i,m,?_,?_,hp,hq⟩
    · exact (List.take_append_drop i u).symm
    · rw [he]; exact (List.take_append_drop j v).symm

def reachesCheck (M : System n) (p : Fin n) (u : Word) (q : Fin n) (v : Word) : Bool :=
  (List.range (u.length+1)).any fun i =>
    (List.range (v.length+1)).any fun j => (List.finRange n).any fun m =>
      (u.drop i == v.drop j) && popCheck M p (u.take i) m &&
        popCheck (reverse M) q (v.take j) m

@[simp] theorem reachesCheck_correct (M : System n) (p : Fin n) (u : Word) (q : Fin n) (v : Word) :
    reachesCheck M p u q v = true ↔ Reaches M (p,u) (q,v) := by
  rw [reaches_iff_normal, normal_iff_cut]
  simp [reachesCheck,CutNormal,List.any_eq_true,Nat.lt_succ_iff,and_assoc]

/-- Existence of ANY consumed word is a finite graph language-nonemptiness test. -/
def controlEdge (M : System n) (p q : Fin n) : Bool :=
  balancedCheck M p q || M.pop false p q || M.pop true p q

theorem exists_pop_iff_path (M : System n) (p q) :
    (∃ w, Pop M p w q) ↔ Path (controlEdge M) p q := by
  constructor
  · rintro ⟨w,hw⟩
    induction w generalizing p with
    | nil => exact .step .refl (by simp [controlEdge, (balancedCheck_correct M p q).mpr hw])
    | cons a w ih =>
      obtain ⟨r,s,hb,hpop,hrest⟩ := hw
      have h1 : Path (controlEdge M) p r :=
        .step .refl (by simp [controlEdge,(balancedCheck_correct M p r).mpr hb])
      have h2 : Path (controlEdge M) r s := by
        apply Path.step Path.refl
        cases a <;> simp [controlEdge,hpop]
      exact path_trans h1 (path_trans h2 (ih s hrest))
  · intro h
    induction h with
    | refl => exact ⟨[],Balanced.refl p⟩
    | @step q r _ he ih =>
      obtain ⟨w,hw⟩ := ih
      have hh : Balanced M q r ∨ M.pop false q r = true ∨ M.pop true q r = true := by
        simpa [controlEdge,or_assoc] using he
      rcases hh with hb | hp | hp
      · exact ⟨w,pop_post hw hb⟩
      · exact ⟨w ++ [false],pop_append hw ⟨q,r,Balanced.refl q,hp,Balanced.refl r⟩⟩
      · exact ⟨w ++ [true],pop_append hw ⟨q,r,Balanced.refl q,hp,Balanced.refl r⟩⟩

def controlReachCheck (M : System n) (p : Fin n) (u : Word) (q : Fin n) : Bool :=
  (List.range (u.length+1)).any fun i => (List.finRange n).any fun m =>
    popCheck M p (u.take i) m && pathCheck (controlEdge (reverse M)) q m

@[simp] theorem controlReachCheck_correct (M : System n) (p : Fin n) (u : Word) (q : Fin n) :
    controlReachCheck M p u q = true ↔ ∃ v, Reaches M (p,u) (q,v) := by
  have hc : controlReachCheck M p u q = true ↔
      ∃ i, i <= u.length ∧ ∃ m, Pop M p (u.take i) m ∧ ∃ y, Pop (reverse M) q y m := by
    simp [controlReachCheck,List.any_eq_true,Nat.lt_succ_iff,
      <- exists_pop_iff_path,and_assoc]
  rw [hc]
  constructor
  · rintro ⟨i,hi,m,hp,y,hq⟩
    refine ⟨y ++ u.drop i,normal_sound ⟨u.take i,y,u.drop i,m,?_,rfl,hp,hq⟩⟩
    exact (List.take_append_drop i u).symm
  · rintro ⟨v,hv⟩
    obtain ⟨x,y,z,m,hx,hy,hp,hq⟩ := reaches_normal hv
    change u = x ++ z at hx
    subst u
    exact ⟨x.length,by simp,m,by simpa using hp,y,hq⟩

end StackReachability
end Subtail
