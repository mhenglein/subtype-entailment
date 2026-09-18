import Subtail.RankQueryReconstructionFamily

/-!
# Literal first-return reconstruction from a common generator trace

The generator reads the OLD prefix graph. Its finite controls are actual reverse
states of the input automaton. Every successful trace is reconstructed as one
safe labelled reference, using the previously proved literal parent recurrence.
No diagram-correctness or closure theorem is assumed.
-/
namespace Subtail
namespace RankQueryReconstruction
open RankQuery RankMilestones TerminalRank

/-- Add one physical reversed letter and its actual new cut state. -/
def appendReference (P : Reference k) (a : Bool) (q : Fin k) : Reference k where
  word := P.word ++ [a]
  label := fun j => if j ≤ P.word.length then P.label j else q

theorem appendReference_length (P : Reference k) (a : Bool) (q : Fin k) :
    (appendReference P a q).word.length = P.word.length+1 := by
  simp [appendReference]

theorem appendReference_take (P : Reference k) (a : Bool) (q : Fin k)
    {j : Nat} (hj : j ≤ P.word.length) :
    (appendReference P a q).word.take j = P.word.take j := by
  simp [appendReference,List.take_append,Nat.sub_eq_zero_of_le hj]

theorem appendReference_old_label (P : Reference k) (a : Bool) (q : Fin k)
    {j : Nat} (hj : j ≤ P.word.length) :
    (appendReference P a q).label j = P.label j := by
  simp [appendReference,hj]

theorem appendReference_new_label (P : Reference k) (a : Bool) (q : Fin k) :
    (appendReference P a q).label (P.word.length+1) = q := by
  simp [appendReference]

theorem any_same {alpha : Type} (xs : List alpha) (f g : alpha -> Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons,h x (List.mem_cons_self)]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Equality only of the prefix and its cut labels suffices for its mask. -/
theorem mask_same_prefix (I : Instance k) (P Q : Reference k) (j : Nat)
    (hw : P.word.take j = Q.word.take j)
    (hl : ∀ h, h ≤ j -> P.label h = Q.label h) (q : Fin k) :
    (RankQuery.mask I P j).get q = (RankQuery.mask I Q j).get q := by
  rw [RankQueryFirstReturn.mask_get_eq,RankQueryFirstReturn.mask_get_eq]
  unfold FirstReturnGraph.mask
  rw [hw]
  apply any_same
  intro h hh
  have hb := (mem_borderLengths.mp hh).1
  have hj : h ≤ j := by simp only [List.length_take] at hb; omega
  rw [hl h hj]

/-- The parent of an appended prefix is computed by the old reference's K edge. -/
theorem appendReference_parent (P B : Reference k) (a : Bool) (q : Fin k)
    (hp : 0 < P.word.length) (hb : B.word = P.word.take B.word.length)
    {h : Nat} (hh : failureParent P.word = h) (hsmall : h < B.word.length) :
    failureParent (appendReference P a q).word = RankQuery.advance B.word h a := by
  let w := (appendReference P a q).word
  have htake : w.take P.word.length = P.word := by simp [w,appendReference]
  have hfull : w.take (P.word.length+1) = w := by simp [w,appendReference]
  have hn : FirstReturnGraph.Next w P.word.length a := by
    unfold FirstReturnGraph.Next
    rw [htake,hfull]
    rfl
  have he := FirstReturnGraph.parent_next hp hn
  rw [htake,hfull,hh] at he
  have hb' : B.word = w.take B.word.length := by
    rw [appendReference_take P a q (by
      have hlen := congrArg List.length hb
      simp only [List.length_take] at hlen
      omega)]
    exact hb
  rw [← FirstReturnGraph.advance_prefix hsmall a,← hb'] at he
  exact he.trans (RankQueryFirstReturn.advance_eq (by omega) a).symm

/-- Proof data carried while building one extension, with its actual old cursor.
The no-earlier-return condition is syntactic border absence, not an oracle. -/
structure ExtensionFrame (I : Instance k) (B P : Reference k) (h : Nat) (q : Fin k) : Prop where
  safe : SafeReference I P
  length : B.word.length ≤ P.word.length
  word : B.word = P.word.take B.word.length
  labels : ∀ j, j ≤ B.word.length -> P.label j = B.label j
  parent : failureParent P.word = h
  last : P.label P.word.length = q
  earlier : ∀ j, B.word.length < j -> j < P.word.length ->
    B.word.length ∉ borderLengths (P.word.take j)

theorem initial_frame (I : Instance k) (B : Reference k) (hb : SafeReference I B) :
    ExtensionFrame I B B (failureParent B.word) (B.label B.word.length) := by
  refine ⟨hb,Nat.le_refl _,by simp,fun _ _ => rfl,rfl,rfl,?_⟩
  intro j hj hlt
  omega

/-- Local reverse-step guards are sufficient for every new border comparison. -/
theorem frame_append (I : Instance k) (B P : Reference k) {h : Nat} {q p : Fin k}
    (H : ExtensionFrame I B P h q) (hsmall : h < B.word.length) (a : Bool)
    (hs : step I p a = some q) (hbad : I.bad.get p = false)
    (hdiag : (I.flags.get p).get p = false)
    (hmask : (RankQuery.mask I B (RankQuery.advance B.word h a)).get p = false) :
    ExtensionFrame I B (appendReference P a p) (RankQuery.advance B.word h a) p := by
  let Q := appendReference P a p
  let t := RankQuery.advance B.word h a
  have hlen : Q.word.length = P.word.length+1 := appendReference_length P a p
  have ht : t ≤ B.word.length := RankQuery.advance_le _ _ _
  have hparent : failureParent Q.word = t :=
    appendReference_parent P B a p H.safe.nonempty H.word H.parent hsmall
  have hpre : ∀ j, j ≤ P.word.length ->
      (RankQuery.mask I Q j).get (P.label j) = (RankQuery.mask I P j).get (P.label j) := by
    intro j hj
    apply mask_same_prefix
    · exact appendReference_take P a p hj
    · intro r hr; exact appendReference_old_label P a p (by omega)
  have hprefix : Q.word.take t = B.word.take t := by
    rw [appendReference_take P a p (by omega),H.word]
    simp only [List.take_take,Nat.min_eq_left ht]
  have hnewmask : (RankQuery.mask I Q Q.word.length).get p = false := by
    rw [RankQueryFirstReturn.mask_get_eq]
    rw [FirstReturnGraph.mask_decomposition (Nat.le_refl _) (by omega)]
    have hl : Q.label Q.word.length = p := by
      rw [hlen]; exact appendReference_new_label P a p
    rw [hl,hdiag]
    simp only [Bool.false_or,List.take_length,hparent]
    have heq : (RankQuery.mask I Q t).get p = (RankQuery.mask I B t).get p := by
      apply mask_same_prefix I Q B t hprefix
      intro j hj
      rw [appendReference_old_label P a p (by omega)]
      exact H.labels j (by omega)
    rw [← RankQueryFirstReturn.mask_get_eq,heq]
    exact hmask
  have hsafe : SafeReference I Q := by
    refine ⟨by omega,?_,?_,?_,?_⟩
    · rw [appendReference_old_label P a p (by omega)]
      exact H.safe.accepting
    · intro j hj
      have hjle : j ≤ P.word.length := by omega
      by_cases hjlt : j < P.word.length
      · have hj1 : j+1 ≤ P.word.length := by omega
        rw [appendReference_old_label P a p hj1,appendReference_old_label P a p hjle]
        have ha : Q.word[j] = P.word[j] := by simp [Q,appendReference,List.getElem_append,hjlt]
        rw [ha]
        exact H.safe.run j hjlt
      · have he : j = P.word.length := by omega
        subst j
        rw [appendReference_new_label P a p,appendReference_old_label P a p (Nat.le_refl _),H.last]
        simpa [Q,appendReference] using hs
    · intro j hj
      by_cases hjo : j ≤ P.word.length
      · rw [appendReference_old_label P a p hjo]
        exact H.safe.safe j hjo
      · have he : j = P.word.length+1 := by omega
        subst j
        rw [appendReference_new_label P a p]
        exact hbad
    · intro j hj
      by_cases hjo : j ≤ P.word.length
      · rw [appendReference_old_label P a p hjo,hpre j hjo]
        exact H.safe.border j hjo
      · have he : j = Q.word.length := by omega
        subst j
        have hl : Q.label Q.word.length = p := by rw [hlen]; exact appendReference_new_label P a p
        rw [hl]
        exact hnewmask
  refine ⟨hsafe,by omega,?_,?_,hparent,?_,?_⟩
  · rw [appendReference_take P a p H.length]
    exact H.word
  · intro j hj
    rw [appendReference_old_label P a p (by omega)]
    exact H.labels j hj
  · rw [hlen]; exact appendReference_new_label P a p
  · intro j hj hlt hb
    have hjle : j ≤ P.word.length := by omega
    rw [appendReference_take P a p hjle] at hb
    by_cases hjlt : j < P.word.length
    · exact H.earlier j hj hjlt hb
    · have he : j = P.word.length := by omega
      subst j
      simp only [List.take_length] at hb
      have hh := (failureParent_spec P.word H.safe.nonempty).2.2 B.word.length hb hj
      rw [H.parent] at hh
      omega

theorem frame_at_end (I : Instance k) (B P : Reference k) (hb : SafeReference I B)
    {q : Fin k} (H : ExtensionFrame I B P B.word.length q) : FirstReturnExt I B P := by
  have hp := (failureParent_spec P.word H.safe.nonempty).2.1
  rw [H.parent] at hp
  refine ⟨H.safe,?_,H.labels,?_,Nat.le_refl _,?_,?_⟩
  · rw [H.word]
    exact ⟨P.word.drop B.word.length, List.take_append_drop _ _⟩
  · exact hp
  · simpa only [List.take_length,H.parent] using
      (failureParent_spec P.word H.safe.nonempty).1
  · exact H.earlier

/-- A finite return generator: predecessor controls on K-labelled old-graph steps.
A full cursor hit cannot have an outgoing generator step. -/
def returnGenerator (I : Instance k) (q : Fin k) : Observer k where
  size := k
  initial := [q]
  final := List.finRange k
  allows := fun p c => !I.bad.get p && !(I.flags.get p).get p && !c.mask.get p
  move := fun p c l _ => match l with
    | .K a => if c.isEnd then [] else
        (List.finRange k).filter fun r => step I r a == some p
    | _ => []

theorem return_generator_move (I : Instance k) (q p r : Fin k)
    (c d : Colour k) (a : Bool) :
    r ∈ (returnGenerator I q).move p c (.K a) d ↔
      c.isEnd = false ∧ step I r a = some p := by
  cases hc : c.isEnd <;> simp [returnGenerator,hc]

theorem return_generator_allowed (I : Instance k) (q p : Fin k) (c : Colour k) :
    (returnGenerator I q).allows p c = true ↔
      I.bad.get p = false ∧ (I.flags.get p).get p = false ∧ c.mask.get p = false := by
  simp [returnGenerator,Bool.and_eq_true,and_assoc]

def emittedBit : Label -> Bool
  | .K a => a
  | _ => false

def rebuildReference {I : Instance k} {B : Reference k} {q : Fin k}
    (P : Reference k) : List (Label × Node (prefixGraph I B) (returnGenerator I q)) -> Reference k
  | [] => P
  | (l,y)::ts => rebuildReference (appendReference P (emittedBit l) y.2) ts

/-- Readback of actual generator moves, with every semantic guard displayed. -/
theorem return_move (I : Instance k) (B : Reference k) (q : Fin k)
    {x y : Node (prefixGraph I B) (returnGenerator I q)} {l : Label}
    (hs : TaggedStep (prefixGraph I B) (returnGenerator I q) x l y) :
    ∃ a, l = .K a ∧ x.1.val < B.word.length ∧
      RankQuery.advance B.word x.1.val a = y.1.val ∧
      step I y.2 a = some x.2 ∧ I.bad.get y.2 = false ∧
      (I.flags.get y.2).get y.2 = false ∧
      (RankQuery.mask I B y.1.val).get y.2 = false := by
  have hm := hs.2.1
  have hy := hs.2.2
  cases l with
  | F => simp [returnGenerator] at hm
  | S => simp [returnGenerator] at hm
  | K a =>
    have hbound : x.1.val ≤ B.word.length := by have := x.1.isLt; change x.1.val < B.word.length+1 at this; omega
    have hm' := (return_generator_move I q x.2 y.2 _ _ a).mp hm
    have hnot := hm'.1
    have hx : x.1.val < B.word.length := by
      change decide (x.1.val = B.word.length) = false at hnot
      have hn : x.1.val ≠ B.word.length := of_decide_eq_false hnot
      omega
    have hstep := hm'.2
    have hclear : I.bad.get y.2 = false ∧ (I.flags.get y.2).get y.2 = false ∧
        (RankQuery.mask I B y.1.val).get y.2 = false :=
      (return_generator_allowed I q y.2 _).mp hy
    have hedge : RankQuery.advance B.word x.1.val a = y.1.val :=
      congrArg Fin.val (Option.some.inj hs.1)
    exact ⟨a,rfl,hx,hedge,hstep,hclear⟩

/-- Induction follows one trace and constructs all its physical reference positions. -/
theorem trace_rebuild_frame (I : Instance k) (B : Reference k) (q : Fin k)
    {x y : Node (prefixGraph I B) (returnGenerator I q)} {ts}
    (hr : TraceRun (prefixGraph I B) (returnGenerator I q) x ts y) :
    ∀ P, ExtensionFrame I B P x.1.val x.2 ->
      ExtensionFrame I B (rebuildReference P ts) y.1.val y.2 := by
  induction hr with
  | nil hx => intro P h; exact h
  | cons hx hs ht ih =>
    intro P H
    obtain ⟨a,hl,hsmall,hedge,hstep,hbad,hdiag,hmask⟩ := return_move I B q hs
    subst hl
    apply ih
    simpa only [emittedBit,hedge] using frame_append I B P H hsmall a hstep hbad hdiag
      (by simpa only [hedge] using hmask)

/-- Terminal accepted generator traces build literal safe first returns. -/
theorem trace_rebuild_first_return (I : Instance k) (B : Reference k)
    (hb : SafeReference I B)
    (start finish : Fin (prefixGraph I B).size)
    (hstart : start.val = failureParent B.word) (hfinish : finish.val = B.word.length)
    {p : Fin k} {ts}
    (hr : TraceRun (prefixGraph I B) (returnGenerator I (B.label B.word.length))
      (start,B.label B.word.length) ts (finish,p)) :
    FirstReturnExt I B (rebuildReference B ts) := by
  apply frame_at_end I B _ hb
  have hinit := initial_frame I B hb
  rw [← hstart] at hinit
  have hout := trace_rebuild_frame I B (B.label B.word.length) hr B hinit
  simpa only [hfinish] using hout

end RankQueryReconstruction
end Subtail
