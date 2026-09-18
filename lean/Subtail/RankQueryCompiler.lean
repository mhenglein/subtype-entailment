import Subtail.RankQueryFirstReturn

/-!
# An executable diagram compiler for the promotion preimage (stage 4c, issue #29)

This module defines, in Lean, the syntactic compilation of ONE bounded portal
diagram into ONE clause of the query grammar, mirroring
`experiments/rank_preimage.py` (`compile_diagram`) and the observer kinds of
`experiments/rank_preimage_core.py` (`core`, `slice`, `edge`, `interval`).
The compiler has no graph, word or reference argument: it only reads the finite
diagram data and the finite instance.

Nothing about the Closure Lemma is proved in this file yet.  The compiler is
executable so that it can be compared with the Python implementation and used
as the concrete `pre` of `RankQuery.ClosureFor`; the reverse-direction theorem
("a base model of a compiled clause yields one safe first-return extension")
is the target of issue #29 and is stated separately as it is proved.
No `sorry`, no custom axiom.
-/
namespace Subtail
namespace RankQueryCompiler
open TerminalRank RankMilestones RankQuery

variable {k : Nat}

/-! ## Finite colour maps -/

/-- Flag column of an original state `q`: the set of `p` with `(p, q)` a flag. -/
def column (I : Instance k) (q : Fin k) : Vector Bool k :=
  Vector.ofFn fun p => (I.flags.get p).get q

def orMask (a b : Vector Bool k) : Vector Bool k :=
  Vector.ofFn fun p => a.get p || b.get p

/-- The colour of a fresh vertex generated at an old origin of colour `c`, with
actual reverse state `q` and next bit `nxt` (`none` = END). -/
def freshMap (I : Instance k) (q : Fin k) (nxt : Option Bool) (c : Colour k) : Colour k :=
  ⟨q, orMask c.mask (column I q), nxt, false, nxt.isNone⟩

/-- Recolouring of the old endpoint after the first emission `a`: it is no longer
`End` and its next bit becomes `a`; every other colour is unchanged. -/
def coreMap (a : Bool) (c : Colour k) : Colour k :=
  if c.isEnd then ⟨c.state, c.mask, some a, c.root, false⟩ else c

/-! ## Derived observers -/

/-- The same automaton with one initial and one final control. -/
def sliceObs (o : Observer k) (lc rc : Fin o.size) : Observer k :=
  { o with initial := [lc], final := [rc] }

/-- Relativize an observer to the recoloured old graph and suppress the old
`K_a` edge leaving the endpoint. -/
def coreObs (o : Observer k) (a : Bool) : Observer k where
  size := o.size
  initial := o.initial
  final := o.final
  allows := fun q c => o.allows q (coreMap a c)
  move := fun q c l d =>
    if c.isEnd ∧ l = .K a then [] else o.move q (coreMap a c) l (coreMap a d)

/-- A portal check: observer `o` moves from control `src` to control `dst` along
`label`, reading the two mapped colours; both controls allow their colours. -/
structure Portal (k : Nat) where
  observer : Observer k
  src : Fin observer.size
  dst : Fin observer.size
  label : Label
  left : Colour k → Colour k
  right : Colour k → Colour k

def portalTest (P : Portal k) (c : Colour k) : Bool :=
  P.observer.allows P.src (P.left c) && P.observer.allows P.dst (P.right c) &&
    (P.observer.move P.src (P.left c) P.label (P.right c)).contains P.dst

def portalMove (P : Portal k) (c d : Colour k) : Bool :=
  (P.observer.move P.src (P.left c) P.label (P.right d)).contains P.dst

/-- One directed edge with label `l`, colour tests at both ends and an optional
semantic guard on the two actual endpoint colours. -/
def semOK : Option (Portal k) → Colour k → Colour k → Bool
  | none, _, _ => true
  | some P, c, d => portalMove P c d

def edgeObs (l : Label) (left right : Colour k → Bool) (sem : Option (Portal k)) : Observer k where
  size := 2
  initial := [⟨0, by omega⟩]
  final := [⟨1, by omega⟩]
  allows := fun q c => if q.val = 0 then left c else right c
  move := fun q c l' d =>
    if (q.val == 0) && (l' == l) && semOK sem c d then [⟨1, by omega⟩] else []

/-! ## The shared-interval product observer -/

def prodList : List Nat → Nat
  | [] => 1
  | s :: ss => s * prodList ss

/-- Mixed-radix digits of `v` for the given sizes, most significant first
(the order of `rank_preimage_core.radix_encode`). -/
def digits : List Nat → Nat → List Nat
  | [], _ => []
  | s :: ss, v => (v / prodList ss) % s :: digits ss (v % prodList ss)

/-- The next-bit index convention `0, 1, END ↦ 0, 1, 2`. -/
def nextOfIdx : Nat → Option (Option Bool)
  | 0 => some (some false)
  | 1 => some (some true)
  | 2 => some none
  | _ => none

def idxOfNext : Option Bool → Nat
  | some false => 0
  | some true => 1
  | none => 2

def stateOf (k : Nat) (q : Nat) : Option (Fin k) :=
  (List.finRange k).find? fun p => p.val = q

/-- An active observation of an interval: observer, entering control, leaving control. -/
abbrev Active (k : Nat) := Observer k × Nat × Nat

def intervalSizes (k : Nat) (active : List (Active k)) : List Nat :=
  k :: 3 :: 2 :: active.map fun a => a.1.size

def intervalSize (k : Nat) (active : List (Active k)) : Nat :=
  prodList (intervalSizes k active)

/-- Decoded interval control `(state, next, seen, controls)`. -/
structure IControl (k : Nat) where
  state : Fin k
  next : Option Bool
  seen : Nat
  controls : List Nat

def decodeI (active : List (Active k)) (v : Nat) : Option (IControl k) :=
  match digits (intervalSizes k active) v with
  | q :: n :: s :: ts => do
      let q ← stateOf k q
      let nxt ← nextOfIdx n
      pure ⟨q, nxt, s, ts⟩
  | _ => none

/-- Does control `t` (as a number) of observer `o` allow colour `c`? -/
def allowsNat (o : Observer k) (t : Nat) (c : Colour k) : Bool :=
  (List.finRange o.size).any fun t' => t'.val = t && o.allows t' c

/-- Is `t'` reachable from `t` in `o` by an `S` or `K_b` move between the two colours? -/
def moveNat (o : Observer k) (t : Nat) (b : Bool) (c d : Colour k) (t' : Nat) : Bool :=
  (List.finRange o.size).any fun s => s.val = t &&
    ((o.move s c .S d ++ o.move s c (.K b) d).any fun r => r.val = t')

def zipAll {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && zipAll f as bs
  | _, _ => false

/-- The colour predicate of an interval control at an old origin `c`. -/
def intervalAllows (I : Instance k) (active : List (Active k)) (x : IControl k) (c : Colour k) : Bool :=
  !I.bad.get x.state && !(I.flags.get x.state).get x.state && !c.mask.get x.state &&
    (x.next.isNone == c.isEnd) &&
    zipAll (fun (a : Active k) t => allowsNat a.1 t (freshMap I x.state x.next c)) active x.controls

/-- One generator step of the interval product: emit the guessed bit along the
base `K_b` edge `c → d`, choose the previous actual state and the next guess, and
let every active observer move by `S` or `K_b` between the SAME two fresh colours. -/
def intervalStep (I : Instance k) (active : List (Active k)) (x y : IControl k)
    (c : Colour k) (l : Label) (d : Colour k) : Bool :=
  match x.next with
  | none => false
  | some b =>
    l = .K b && !c.isEnd && y.seen = 1 &&
      step I y.state b == some x.state && !I.bad.get y.state &&
      !(I.flags.get y.state).get y.state && !d.mask.get y.state &&
      (y.next.isNone == d.isEnd) &&
      (let fc := freshMap I x.state (some b) c
       let gc := freshMap I y.state y.next d
       zipAll (fun (a : Active k) (tt : Nat × Nat) =>
           moveNat a.1 tt.1 b fc gc tt.2 && allowsNat a.1 tt.2 gc)
         active (x.controls.zip y.controls) && x.controls.length = y.controls.length)

def intervalObs (I : Instance k) (active : List (Active k))
    (ql : Fin k) (nl : Option Bool) (qr : Fin k) (nr : Option Bool) : Observer k where
  size := intervalSize k active
  initial := (List.finRange (intervalSize k active)).filter fun v =>
    match decodeI active v.val with
    | some x => x.state = ql && x.next == nl && x.seen = 0 &&
        x.controls = active.map fun a => a.2.1
    | none => false
  final := (List.finRange (intervalSize k active)).filter fun v =>
    match decodeI active v.val with
    | some x => x.state = qr && x.next == nr && x.seen = 1 &&
        x.controls = active.map fun a => a.2.2
    | none => false
  allows := fun v c =>
    match decodeI active v.val with
    | some x => intervalAllows I active x c
    | none => false
  move := fun v c l d =>
    match decodeI active v.val with
    | some x => (List.finRange (intervalSize k active)).filter fun v' =>
        match decodeI active v'.val with
        | some y => intervalStep I active x y c l d
        | none => false
    | none => []

/-! ## Diagrams -/

/-- Where a query variable lives: at a core (old) variable or at a fresh mark group. -/
inductive Loc where
  | core (x : Nat)
  | fresh (g : Nat)
  deriving DecidableEq, Repr

inductive PieceKind where
  | core
  | forward
  | enter
  | exit
  | wrap
  deriving DecidableEq, Repr

/-- One piece of a path diagram.  `source`/`target` are core-variable indices or
mark-group indices according to the kind; `lc`/`rc` are the observer controls at
its two ends; `label` is used by `enter`, `exit` and `wrap`. -/
structure Piece where
  kind : PieceKind
  source : Nat
  target : Nat
  lc : Nat
  rc : Nat
  label : Label := .F
  deriving Repr

def pieceSourceLoc (P : Piece) : Loc :=
  match P.kind with
  | .core => .core P.source
  | .enter => .core P.source
  | _ => .fresh P.source

def pieceTargetLoc (P : Piece) : Loc :=
  match P.kind with
  | .core => .core P.target
  | .exit => .core P.target
  | _ => .fresh P.target

/-- A bounded portal diagram for a clause: ordered mark groups `0 .. groups-1`
(group `0` is the first fresh vertex, group `groups-1` the new endpoint), core
variables, the location of every clause variable, the actual reverse state and
next bit at each group, the first emitted bit, the guessed colour of the old
endpoint, one piece list per atom, and the shared seam controls of forward
pieces at internal groups `(atom, piece, group, control)`. -/
structure Diagram (k : Nat) where
  groups : Nat
  coreVars : Nat
  loc : List Loc
  states : List (Fin k)
  nextBits : List (Option Bool)
  firstBit : Bool
  oldEnd : Colour k
  pieces : List (List Piece)
  seams : List (Nat × Nat × Nat × Nat)
  deriving Repr

/-! ## Compilation -/

abbrev Var (D : Diagram k) := Fin (2 + D.groups + D.coreVars)

def endVar (D : Diagram k) : Var D := ⟨0, by omega⟩
def initVar (D : Diagram k) : Var D := ⟨1, by omega⟩

def zVar (D : Diagram k) (g : Nat) : Option (Var D) :=
  if h : g < D.groups then some ⟨2 + g, by omega⟩ else none

def coreVar (D : Diagram k) (x : Nat) : Option (Var D) :=
  if h : x < D.coreVars then some ⟨2 + D.groups + x, by omega⟩ else none

def locVar (D : Diagram k) : Loc → Option (Var D)
  | .core x => coreVar D x
  | .fresh g => zVar D g

def seamControl (D : Diagram k) (ai pi g : Nat) : Option Nat :=
  (D.seams.find? fun s => s.1 = ai ∧ s.2.1 = pi ∧ s.2.2.1 = g).map fun s => s.2.2.2

def finOf (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

/-- The finite output of compiling the pieces of one atom. -/
structure Emitted (D : Diagram k) where
  tests : List (Var D × (Colour k → Bool)) := []
  equal : List (Var D × Var D) := []
  atoms : List (Atom k (2 + D.groups + D.coreVars)) := []
  active : List (Nat × Active k) := []

def appendEmitted (e f : Emitted D) : Emitted D :=
  ⟨e.tests ++ f.tests, e.equal ++ f.equal, e.atoms ++ f.atoms, e.active ++ f.active⟩

/-- Compile one piece of atom `ai` (piece index `pi`) with observer `o`. -/
def compilePiece (I : Instance k) (D : Diagram k) (ai pi : Nat) (o : Observer k)
    (P : Piece) : Option (Emitted D) := do
  let a := D.firstBit
  let n := D.groups
  let lc ← finOf o.size P.lc
  let rc ← finOf o.size P.rc
  let fm : Nat → Option (Colour k → Colour k) := fun g => do
    let q ← D.states[g]?
    let b ← D.nextBits[g]?
    pure (freshMap I q b)
  match P.kind with
  | .core => do
      let u ← coreVar D P.source
      let v ← coreVar D P.target
      pure { atoms := [⟨coreObs (sliceObs o lc rc) a, u, v⟩] }
  | .forward => do
      let i := P.source
      let j := P.target
      guard (i ≤ j ∧ j < n)
      if i = j then do
        guard (P.lc = P.rc)
        let z ← zVar D i
        let f ← fm i
        pure { tests := [(z, fun c => o.allows lc (f c))] }
      else do
        let inner ← (List.range (j - i - 1)).mapM fun t => seamControl D ai pi (i + 1 + t)
        let cs := P.lc :: inner ++ [P.rc]
        guard (cs.all fun x => x < o.size)
        let acts ← (List.range (j - i)).mapM fun t => do
          let l ← cs[t]?
          let r ← cs[t + 1]?
          pure (i + t, (o, l, r))
        pure { active := acts }
  | .enter => do
      guard (P.target = 0 ∧ (P.label = .S ∨ P.label = .K a))
      let u ← coreVar D P.source
      let z0 ← zVar D 0
      let f0 ← fm 0
      let leftColour := coreMap a D.oldEnd
      pure { tests := [(z0, portalTest ⟨o, lc, rc, P.label, fun _ => leftColour, f0⟩)],
             equal := [(u, endVar D)] }
  | .wrap => do
      guard (P.source = n - 1 ∧ P.target = 0 ∧ P.label = .K a)
      let z0 ← zVar D 0
      let f0 ← fm 0
      let flast ← fm (n - 1)
      let leftColour := flast D.oldEnd
      pure { tests := [(z0, portalTest ⟨o, lc, rc, .K a, fun _ => leftColour, f0⟩)] }
  | .exit => do
      let i := P.source
      let zi ← zVar D i
      let fi ← fm i
      let v ← coreVar D P.target
      match P.label with
      | .F =>
          pure { tests := [(zi, portalTest ⟨o, lc, rc, .F, fi, coreMap a⟩)],
                 equal := [(v, zi)] }
      | .K b => do
          let avoid ← if i = n - 1 then pure (some a) else D.nextBits[i]?
          guard (some b ≠ avoid)
          pure { atoms := [⟨edgeObs (.K b) (fun c => o.allows lc (fi c))
                    (fun c => o.allows rc (coreMap a c))
                    (some ⟨o, lc, rc, .K b, fi, coreMap a⟩), zi, v⟩] }
      | .S => none

/-- Compile the pieces of atom `ai`: endpoints, acceptance and seams are checked. -/
def compileAtom (I : Instance k) (c : Clause k) (D : Diagram k) (ai : Nat)
    (atm : Atom k c.vars) (ps : List Piece) : Option (Emitted D) := do
  let o := atm.observer
  let first ← ps.head?
  let last ← ps.getLast?
  let srcLoc ← D.loc[atm.source.val]?
  let tgtLoc ← D.loc[atm.target.val]?
  guard (pieceSourceLoc first = srcLoc ∧ pieceTargetLoc last = tgtLoc)
  guard ((o.initial.any fun q => q.val = first.lc) ∧ (o.final.any fun q => q.val = last.rc))
  guard ((ps.zip ps.tail).all fun (l, r) => pieceTargetLoc l = pieceSourceLoc r ∧ l.rc = r.lc)
  let parts ← (List.range ps.length).mapM fun pi => do
    let P ← ps[pi]?
    compilePiece I D ai pi o P
  pure (parts.foldl appendEmitted {})

/-- The compiled clause of one diagram, or `none` when the diagram is malformed.
This is `rank_preimage.compile_diagram`, with variables `END = 0`, `INITIAL = 1`,
origins `z_g = 2 + g` and core variables `2 + groups + x`. -/
def compileDiagram (I : Instance k) (c : Clause k) (D : Diagram k) : Option (Clause k) := do
  let n := D.groups
  let a := D.firstBit
  guard (0 < n ∧ D.states.length = n ∧ D.nextBits.length = n ∧ D.loc.length = c.vars ∧
    D.pieces.length = c.atoms.length)
  guard (D.nextBits.getLast? = some none ∧ (D.nextBits.take (n - 1)).all Option.isSome)
  guard (D.oldEnd.isEnd ∧ !D.oldEnd.root ∧ D.oldEnd.next = none)
  let p0 ← D.states[0]?
  guard (step I p0 a = some D.oldEnd.state ∧ !I.bad.get p0 ∧ !(I.flags.get p0).get p0)
  let z0 ← zVar D 0
  let zlast ← zVar D (n - 1)
  let notEnd ← (List.range (n - 1)).mapM fun j => (zVar D j).map fun z =>
    (z, fun (col : Colour k) => !col.isEnd)
  let baseTests : List (Var D × (Colour k → Bool)) :=
    (endVar D, fun col => decide (col = D.oldEnd)) :: notEnd
  let baseAtoms : List (Atom k (2 + n + D.coreVars)) :=
    [⟨oneEdge .F, endVar D, initVar D⟩,
     ⟨edgeObs (.K a) (fun _ => true)
        (fun col => !col.mask.get p0 && (col.isEnd == decide (n = 1))) none, initVar D, z0⟩]
  let fm : Nat → Option (Colour k → Colour k) := fun g => do
    let q ← D.states[g]?
    let b ← D.nextBits[g]?
    pure (freshMap I q b)
  -- unary tests of the clause, pulled back through the colour maps
  let qTests ← c.tests.mapM fun (v, t) => do
    let l ← D.loc[v.val]?
    match l with
    | .core x => do
        let cv ← coreVar D x
        pure (cv, fun col => t (coreMap a col))
    | .fresh g => do
        let zv ← zVar D g
        let f ← fm g
        pure (zv, fun col => t (f col))
  -- equalities and disequalities
  let qEqual ← c.equal.mapM fun (v, w) => do
    let lv ← D.loc[v.val]?
    let lw ← D.loc[w.val]?
    match lv, lw with
    | .core x, .core y => do
        let cx ← coreVar D x
        let cy ← coreVar D y
        pure (some (cx, cy))
    | .fresh g, .fresh h => do
        guard (g = h)
        pure none
    | _, _ => none
  let qUnequal ← c.unequal.mapM fun (v, w) => do
    let lv ← D.loc[v.val]?
    let lw ← D.loc[w.val]?
    match lv, lw with
    | .core x, .core y => do
        let cx ← coreVar D x
        let cy ← coreVar D y
        pure (some (cx, cy))
    | .fresh g, .fresh h => do
        guard (g ≠ h)
        pure none
    | _, _ => pure none
  -- path diagrams
  let emitted ← (List.range c.atoms.length).mapM fun ai => do
    let atm ← c.atoms[ai]?
    let ps ← D.pieces[ai]?
    compileAtom I c D ai atm ps
  let e := emitted.foldl appendEmitted {}
  -- one product observer per physical interval
  let intervals ← (List.range (n - 1)).mapM fun g => do
    let items := (e.active.filter fun x => x.1 = g).map fun x => x.2
    let ql ← D.states[g]?
    let nl ← D.nextBits[g]?
    let qr ← D.states[g + 1]?
    let nr ← D.nextBits[g + 1]?
    let zg ← zVar D g
    let zg' ← zVar D (g + 1)
    pure (⟨intervalObs I items ql nl qr nr, zg, zg'⟩ : Atom k (2 + n + D.coreVars))
  pure { vars := 2 + n + D.coreVars
         tests := baseTests ++ qTests ++ e.tests
         equal := (zlast, endVar D) :: qEqual.filterMap id ++ e.equal
         unequal := qUnequal.filterMap id
         atoms := baseAtoms ++ e.atoms ++ intervals }

/-- The clause-level preimage over a supplied finite list of diagrams. -/
def preimageOver (I : Instance k) (c : Clause k) (Ds : List (Diagram k)) : Query k :=
  Ds.filterMap (compileDiagram I c)

end RankQueryCompiler
end Subtail
