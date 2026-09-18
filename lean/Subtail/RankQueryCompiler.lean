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

/-! ## Compilation

The compiler is split into a Boolean validity check (`validDiagram`, the guards
of `compile_diagram`) and a TOTAL construction (`compileValid`) that never fails
and uses harmless fallbacks where the check would have rejected the diagram.
`compileDiagram` returns the construction exactly when the check passes.  This
shape lets proofs read facts about the compiled clause off plain list
membership, with the validity facts as separate Boolean hypotheses. -/

abbrev Var (D : Diagram k) := Fin (2 + D.groups + D.coreVars)

def endVar (D : Diagram k) : Var D := ⟨0, by omega⟩
def initVar (D : Diagram k) : Var D := ⟨1, by omega⟩

/-- Origin variable of mark group `g` (falls back to `END` out of range). -/
def zVar (D : Diagram k) (g : Nat) : Var D :=
  if h : g < D.groups then ⟨2 + g, by omega⟩ else endVar D

/-- Core variable `x` (falls back to `END` out of range). -/
def coreVar (D : Diagram k) (x : Nat) : Var D :=
  if h : x < D.coreVars then ⟨2 + D.groups + x, by omega⟩ else endVar D

def locVar (D : Diagram k) : Loc → Var D
  | .core x => coreVar D x
  | .fresh g => zVar D g

/-- Actual reverse state at mark group `g` (fallback: the old endpoint's state). -/
def markState (D : Diagram k) (g : Nat) : Fin k := D.states.getD g D.oldEnd.state

/-- Next bit at mark group `g` (fallback: END). -/
def nextOf (D : Diagram k) (g : Nat) : Option Bool := D.nextBits.getD g none

def locOf (D : Diagram k) (v : Nat) : Loc := D.loc.getD v (.core 0)

def piecesOf (D : Diagram k) (ai : Nat) : List Piece := D.pieces.getD ai []

def seamControl (D : Diagram k) (ai pi g : Nat) : Nat :=
  ((D.seams.find? fun s => s.1 = ai ∧ s.2.1 = pi ∧ s.2.2.1 = g).map fun s => s.2.2.2).getD 0

/-- The fresh colour map of mark group `g`. -/
def fm (I : Instance k) (D : Diagram k) (g : Nat) : Colour k → Colour k :=
  freshMap I (markState D g) (nextOf D g)

def finOf (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

/-- The finite output of compiling pieces. -/
structure Emitted (D : Diagram k) where
  tests : List (Var D × (Colour k → Bool)) := []
  equal : List (Var D × Var D) := []
  atoms : List (Atom k (2 + D.groups + D.coreVars)) := []
  active : List (Nat × Active k) := []

def appendEmitted (e f : Emitted D) : Emitted D :=
  ⟨e.tests ++ f.tests, e.equal ++ f.equal, e.atoms ++ f.atoms, e.active ++ f.active⟩

def emptyEmitted : Emitted D := {}

/-- The seam-control sequence of a forward piece from group `i` to group `j`. -/
def forwardControls (D : Diagram k) (ai pi i j : Nat) (P : Piece) : List Nat :=
  P.lc :: (List.range (j - i - 1)).map (fun t => seamControl D ai pi (i + 1 + t)) ++ [P.rc]

/-- Active observations contributed by a forward piece from group `i` to group `j`. -/
def forwardActive (D : Diagram k) (ai pi i j : Nat) (o : Observer k) (P : Piece) :
    List (Nat × Active k) :=
  let cs := forwardControls D ai pi i j P
  (List.range (j - i)).map fun t => (i + t, (o, cs.getD t 0, cs.getD (t + 1) 0))

/-- Total compilation of one piece; malformed pieces contribute nothing. -/
def compilePiece (I : Instance k) (D : Diagram k) (ai pi : Nat) (o : Observer k)
    (P : Piece) : Emitted D :=
  let a := D.firstBit
  let n := D.groups
  match finOf o.size P.lc, finOf o.size P.rc with
  | some lc, some rc =>
    match P.kind with
    | .core => { atoms := [⟨coreObs (sliceObs o lc rc) a, coreVar D P.source, coreVar D P.target⟩] }
    | .forward =>
      if P.source = P.target then
        { tests := [(zVar D P.source, fun c => o.allows lc (fm I D P.source c))] }
      else { active := forwardActive D ai pi P.source P.target o P }
    | .enter =>
      { tests := [(zVar D 0, portalTest ⟨o, lc, rc, P.label, fun _ => coreMap a D.oldEnd, fm I D 0⟩)],
        equal := [(coreVar D P.source, endVar D)] }
    | .wrap =>
      { tests := [(zVar D 0, portalTest ⟨o, lc, rc, .K a, fun _ => fm I D (n - 1) D.oldEnd, fm I D 0⟩)] }
    | .exit =>
      match P.label with
      | .F =>
        { tests := [(zVar D P.source, portalTest ⟨o, lc, rc, .F, fm I D P.source, coreMap a⟩)],
          equal := [(coreVar D P.target, zVar D P.source)] }
      | .K b =>
        { atoms := [⟨edgeObs (.K b) (fun c => o.allows lc (fm I D P.source c))
            (fun c => o.allows rc (coreMap a c))
            (some ⟨o, lc, rc, .K b, fm I D P.source, coreMap a⟩), zVar D P.source, coreVar D P.target⟩] }
      | .S => {}
  | _, _ => {}

/-- Validity of one piece (the guards of `compile_diagram`). -/
def pieceValid (I : Instance k) (D : Diagram k) (ai pi : Nat) (o : Observer k) (P : Piece) : Bool :=
  let a := D.firstBit
  let n := D.groups
  P.lc < o.size && P.rc < o.size &&
  match P.kind with
  | .core => P.source < D.coreVars && P.target < D.coreVars
  | .forward =>
    P.source ≤ P.target && P.target < n &&
      (if P.source = P.target then P.lc == P.rc
       else (forwardControls D ai pi P.source P.target P).all fun x => x < o.size)
  | .enter => P.target == 0 && (P.label == .S || P.label == .K a) && P.source < D.coreVars
  | .wrap => P.source == n - 1 && P.target == 0 && P.label == .K a
  | .exit =>
    P.source < n && P.target < D.coreVars &&
      match P.label with
      | .F => true
      | .K b => some b != (if P.source == n - 1 then some a else nextOf D P.source)
      | .S => false

instance : Inhabited Piece := ⟨⟨.core, 0, 0, 0, 0, .F⟩⟩

/-- Total compilation of the pieces of atom `ai`. -/
def compileAtom (I : Instance k) (D : Diagram k) (ai : Nat) (o : Observer k) (ps : List Piece) :
    Emitted D :=
  ((List.range ps.length).map fun pi => compilePiece I D ai pi o (ps.getD pi default)).foldl
    appendEmitted {}

/-- Validity of the pieces of one atom: endpoints, acceptance, seams, pieces. -/
def atomValid (I : Instance k) (c : Clause k) (D : Diagram k) (ai : Nat) (atm : Atom k c.vars)
    (ps : List Piece) : Bool :=
  let o := atm.observer
  match ps.head?, ps.getLast? with
  | some first, some last =>
    (pieceSourceLoc first == locOf D atm.source.val) && (pieceTargetLoc last == locOf D atm.target.val) &&
    (o.initial.any fun q => q.val == first.lc) && (o.final.any fun q => q.val == last.rc) &&
    ((ps.zip ps.tail).all fun (l, r) => (pieceTargetLoc l == pieceSourceLoc r) && (l.rc == r.lc)) &&
    ((List.range ps.length).all fun pi => pieceValid I D ai pi o (ps.getD pi default))
  | _, _ => false

/-- Everything emitted by the atoms of the clause. -/
def allEmitted (I : Instance k) (c : Clause k) (D : Diagram k) : Emitted D :=
  ((List.range c.atoms.length).map fun ai =>
    match c.atoms[ai]? with
    | some atm => compileAtom I D ai atm.observer (piecesOf D ai)
    | none => {}).foldl appendEmitted {}

/-- Active observations of physical interval `g`, in emission order. -/
def itemsAt (I : Instance k) (c : Clause k) (D : Diagram k) (g : Nat) : List (Active k) :=
  ((allEmitted I c D).active.filter fun x => x.1 = g).map fun x => x.2

/-- The interval product atom of physical interval `g`. -/
def intervalAtom (I : Instance k) (c : Clause k) (D : Diagram k) (g : Nat) :
    Atom k (2 + D.groups + D.coreVars) :=
  ⟨intervalObs I (itemsAt I c D g) (markState D g) (nextOf D g) (markState D (g + 1)) (nextOf D (g + 1)),
    zVar D g, zVar D (g + 1)⟩

/-- Pulled-back unary test of clause variable `v`. -/
def queryTest (I : Instance k) (D : Diagram k) (v : Nat) (t : Colour k → Bool) :
    Var D × (Colour k → Bool) :=
  match locOf D v with
  | .core x => (coreVar D x, fun col => t (coreMap D.firstBit col))
  | .fresh g => (zVar D g, fun col => t (fm I D g col))

/-- Core-core equalities/disequalities of the clause (fresh ones are settled statically). -/
def corePairs (D : Diagram k) (l : List (Fin v × Fin v)) : List (Var D × Var D) :=
  l.filterMap fun (x, y) =>
    match locOf D x.val, locOf D y.val with
    | .core a, .core b => some (coreVar D a, coreVar D b)
    | _, _ => none

/-- The two base atoms: `END --F--> INITIAL` and `INITIAL --K_a--> z_0`. -/
def baseAtoms (I : Instance k) (D : Diagram k) : List (Atom k (2 + D.groups + D.coreVars)) :=
  [⟨oneEdge .F, endVar D, initVar D⟩,
   ⟨edgeObs (.K D.firstBit) (fun _ => true)
      (fun col => !col.mask.get (markState D 0) && (col.isEnd == decide (D.groups = 1))) none,
    initVar D, zVar D 0⟩]

/-- The total construction. -/
def compileValid (I : Instance k) (c : Clause k) (D : Diagram k) : Clause k :=
  let n := D.groups
  let e := allEmitted I c D
  { vars := 2 + n + D.coreVars
    tests := (endVar D, fun col => decide (col = D.oldEnd)) ::
      ((List.range (n - 1)).map fun j => (zVar D j, fun (col : Colour k) => !col.isEnd)) ++
      (c.tests.map fun (v, t) => queryTest I D v.val t) ++ e.tests
    equal := (zVar D (n - 1), endVar D) :: corePairs D c.equal ++ e.equal
    unequal := corePairs D c.unequal
    atoms := baseAtoms I D ++ e.atoms ++ (List.range (n - 1)).map (intervalAtom I c D) }

/-- Equalities and disequalities of the clause are compatible with the locations. -/
def pairsValid (D : Diagram k) (l : List (Fin v × Fin v)) (neg : Bool) : Bool :=
  l.all fun (x, y) =>
    match locOf D x.val, locOf D y.val with
    | .core a, .core b => a < D.coreVars && b < D.coreVars
    | .fresh g, .fresh h => (g < D.groups && h < D.groups) && ((g == h) != neg)
    | _, _ => neg

/-- The guards of `compile_diagram`. -/
def validDiagram (I : Instance k) (c : Clause k) (D : Diagram k) : Bool :=
  let n := D.groups
  let a := D.firstBit
  0 < n && D.states.length == n && D.nextBits.length == n && D.loc.length == c.vars &&
  D.pieces.length == c.atoms.length &&
  D.nextBits.getLast? == some none && (D.nextBits.take (n - 1)).all Option.isSome &&
  D.oldEnd.isEnd && !D.oldEnd.root && D.oldEnd.next == none &&
  step I (markState D 0) a == some D.oldEnd.state && !I.bad.get (markState D 0) &&
  !(I.flags.get (markState D 0)).get (markState D 0) &&
  (c.tests.all fun (v, _) => match locOf D v.val with
    | .core x => x < D.coreVars
    | .fresh g => g < n) &&
  pairsValid D c.equal false && pairsValid D c.unequal true &&
  (List.range c.atoms.length).all fun ai =>
    match c.atoms[ai]? with
    | some atm => atomValid I c D ai atm (piecesOf D ai)
    | none => false

/-- The compiled clause of one diagram, or `none` when the diagram is malformed.
This is `rank_preimage.compile_diagram`, with variables `END = 0`, `INITIAL = 1`,
origins `z_g = 2 + g` and core variables `2 + groups + x`. -/
def compileDiagram (I : Instance k) (c : Clause k) (D : Diagram k) : Option (Clause k) :=
  if validDiagram I c D then some (compileValid I c D) else none

/-- The clause-level preimage over a supplied finite list of diagrams. -/
def preimageOver (I : Instance k) (c : Clause k) (Ds : List (Diagram k)) : Query k :=
  Ds.filterMap (compileDiagram I c)

end RankQueryCompiler
end Subtail
