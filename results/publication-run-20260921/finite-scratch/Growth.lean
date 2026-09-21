import Subtail.FiniteTreeDecision
set_option maxHeartbeats 0
def m0 : Subtail.StackSummary.System 0 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m1 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m2 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1), (1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m3 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m4 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m5 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m6 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m7 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m8 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m9 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,3), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,2), (2,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,3), (1,true,3), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m10 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m11 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m12 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (1,true,1), (2,false,1), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m13 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m14 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,1), (3,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (1,false,1), (1,true,2), (2,false,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m15 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0), (1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (1,true,2), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m16 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m17 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (1,false,0), (1,true,1), (3,false,1), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m18 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m19 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m20 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,3), (2,false,1), (2,true,3), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m21 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m22 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,3), (2,false,3), (2,true,1), (3,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,2), (2,false,0), (2,false,1), (2,true,0), (2,true,3), (3,false,3), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m23 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m24 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m25 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,2), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m26 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m27 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,3), (0,true,2), (1,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m28 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,true,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m29 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,true,3), (1,true,2), (3,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m30 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m31 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,1), (1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m32 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m33 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m34 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m35 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,1), (3,2), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,0), (2,true,1), (2,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1), (2,true,0), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m36 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m37 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m38 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,1), (1,2), (3,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m39 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,0), (3,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (2,false,1), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m40 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m41 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (1,false,2), (1,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,3), (2,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m42 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (1,false,1), (1,true,3), (2,false,0), (2,true,0), (2,true,3), (3,true,1), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m43 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m44 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m45 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m46 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0), (0,2), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m47 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,1), (2,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m48 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m49 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,0), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (1,false,0), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m50 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m51 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m52 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,true,2), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (1,false,1), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m53 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,2), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m54 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m55 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m56 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m57 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,2), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,3), (0,true,2), (1,true,0), (1,true,2), (2,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m58 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m59 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0), (1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (1,false,1), (1,true,1), (1,true,2), (2,false,0), (2,true,2), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (0,true,3), (3,false,2), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m60 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(3,false,1), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m61 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m62 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m63 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,2), (2,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (1,false,2), (1,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m64 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m65 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m66 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m67 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m68 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,0), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m69 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m70 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m71 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m72 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m73 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m74 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,0), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2), (1,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m75 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (1,false,0), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m76 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2), (1,0), (1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m77 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m78 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (0,true,1), (0,true,2), (2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m79 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m80 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m81 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m82 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m83 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0), (1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m84 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,1), (1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (0,true,1), (1,false,0), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m85 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m86 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,3), (2,false,2), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2), (1,false,1), (3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m87 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (1,true,0), (2,false,1), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m88 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m89 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m90 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0), (0,3), (2,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (0,true,2), (2,true,0), (2,true,2), (3,false,0), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m91 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m92 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m93 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m94 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m95 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (1,1), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m96 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,1), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m97 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (1,false,3), (2,false,0), (2,true,0), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1), (1,true,2), (2,true,2), (3,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m98 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m99 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m100 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (0,true,1), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m101 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m102 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m103 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (1,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m104 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m105 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m106 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (1,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m107 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m108 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,false,1), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m109 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m110 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,3), (2,false,0), (2,false,3), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,3), (1,false,1), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m111 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m112 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0), (0,2), (3,2), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (0,true,0), (0,true,1), (1,false,0), (1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (2,true,0), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m113 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m114 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m115 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m116 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m117 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,true,0), (2,true,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m118 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m119 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m120 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m121 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,true,0), (1,false,0), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m122 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,true,2), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2), (1,true,1), (1,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m123 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m124 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m125 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,3), (1,false,2), (1,true,3), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m126 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m127 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (2,true,1), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (1,false,0), (1,false,2), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m128 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,2), (2,false,3), (2,true,0), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m129 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m130 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0), (1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m131 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m132 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m133 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m134 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m135 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (1,true,0), (2,false,1), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m136 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,0), (2,1), (2,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (3,false,2), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m137 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0), (0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m138 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m139 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m140 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,true,1), (2,false,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m141 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,3), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m142 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m143 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,0), (1,2), (3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,2), (1,true,3), (2,true,3), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,2), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m144 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m145 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m146 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m147 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m148 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,1), (1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (1,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m149 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m150 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,2), (2,false,0), (2,false,1), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m151 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m152 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m153 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m154 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m155 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0), (1,0), (1,1), (2,0), (2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m156 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m157 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,false,1), (1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m158 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (1,false,1), (1,false,2), (1,true,0), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m159 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m160 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m161 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,1), (2,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m162 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (1,true,1), (2,false,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m163 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m164 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,1), (1,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (1,true,0), (3,false,0), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2), (0,true,3), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m165 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1), (1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (1,true,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m166 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,1), (0,3), (2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,1), (2,false,2), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,3), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m167 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,1), (1,0), (2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m168 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m169 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,1), (0,2), (3,1), (3,2), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,3), (1,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m170 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m171 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,1), (2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m172 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m173 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m174 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,1), (3,false,0), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m175 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m176 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m177 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m178 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m179 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m180 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m181 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m182 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m183 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0), (1,true,1), (2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m184 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m185 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m186 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (1,true,1), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (2,false,1), (2,true,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m187 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,2), (2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1), (1,true,1), (2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m188 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m189 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m190 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,0), (2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m191 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m192 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m193 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2), (3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,0), (2,true,0), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1), (1,false,2), (1,true,0), (2,false,0), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m194 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m195 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0), (2,0), (3,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (1,true,3), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m196 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m197 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2), (3,0), (3,1), (3,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,false,3), (1,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m198 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m199 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,0), (3,1), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (0,true,2), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (1,false,1), (1,false,3), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m200 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m201 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m202 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m203 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (1,false,0), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1), (1,true,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m204 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m205 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,1), (1,3), (2,1), (3,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (0,false,2), (0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m206 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m207 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,2), (2,false,2), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m208 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m209 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m210 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0), (2,1), (3,0), (3,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,true,2), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (1,false,2), (2,false,1), (3,false,0), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m211 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m212 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m213 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m214 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m215 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m216 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m217 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (2,false,3), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (1,false,0), (1,false,3), (3,false,1), (3,true,1), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m218 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m219 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (1,true,2), (1,true,3), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,3), (3,false,0), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m220 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m221 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m222 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m223 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m224 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m225 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m226 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m227 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m228 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m229 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m230 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (0,true,2), (2,false,0), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m231 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m232 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (1,2), (1,3), (3,1), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (2,true,1), (2,true,3), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,true,1), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m233 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m234 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m235 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m236 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m237 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (2,true,0), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m238 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m239 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (2,0), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,0), (2,false,2), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m240 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m241 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (1,false,0), (3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (1,false,3), (1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m242 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m243 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (3,true,1), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,true,0), (3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m244 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (2,false,1), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (1,true,0), (2,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m245 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,0), (1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m246 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m247 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (2,false,2), (3,false,0), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(3,false,2), (3,false,3), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m248 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m249 : Subtail.StackSummary.System 4 where
  eps p q := ([(2,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (2,false,1), (3,false,1), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (0,true,0), (2,false,2), (2,true,2), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m250 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,1), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m251 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m252 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m253 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m254 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,0), (0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m255 : Subtail.StackSummary.System 4 where
  eps p q := ([(1,3), (2,3), (3,2), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (2,true,1), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (2,false,1), (2,true,1), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m256 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m257 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0), (2,false,3), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m258 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m259 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1), (1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,true,0), (1,true,0), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m260 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2), (1,0), (2,1), (3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0), (3,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m261 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (2,3), (3,0), (3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(2,false,1), (2,true,2), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m262 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m263 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2), (1,2), (1,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (1,false,1), (2,false,3), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,false,3), (0,true,3), (1,false,2), (2,false,1), (2,true,2), (3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m264 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m265 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m266 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m267 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (1,false,1), (1,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m268 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m269 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m270 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m271 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (0,true,0), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m272 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,true,0), (0,true,2), (1,false,2), (1,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m273 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,1), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m274 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,3), (3,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,3), (1,true,0), (2,false,0), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m275 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,0), (1,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m276 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2), (2,0), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (2,false,0), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m277 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m278 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m279 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m280 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m281 : Subtail.StackSummary.System 2 where
  eps p q := ([(1,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m282 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m283 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m284 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m285 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m286 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,0), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m287 : Subtail.StackSummary.System 3 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,0), (1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,1), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m288 : Subtail.StackSummary.System 3 where
  eps p q := ([(1,1), (2,2)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,true,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (2,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m289 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (0,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m290 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,2), (0,true,3), (1,true,3), (2,false,0), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (0,true,1), (2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m291 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,0), (3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (2,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,0), (1,true,2), (3,false,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m292 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2), (2,0), (2,3), (3,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,true,1), (0,true,3), (1,true,1), (2,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,3), (2,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m293 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m294 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (1,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,3), (2,false,3), (3,true,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,1), (2,false,2), (2,true,2), (3,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m295 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m296 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,2), (3,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,0), (0,false,3), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1), (2,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m297 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m298 : Subtail.StackSummary.System 3 where
  eps p q := ([(0,2), (1,1), (2,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m299 : Subtail.StackSummary.System 3 where
  eps p q := ([(2,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,true,2), (1,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m300 : Subtail.StackSummary.System 1 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m301 : Subtail.StackSummary.System 4 where
  eps p q := ([(0,3), (1,3)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(2,false,3), (2,true,2), (2,true,3), (3,false,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,true,1), (1,true,3), (2,true,0), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m302 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m303 : Subtail.StackSummary.System 1 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m304 : Subtail.StackSummary.System 4 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(1,false,3), (3,true,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,3), (0,true,1), (1,false,0)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m305 : Subtail.StackSummary.System 4 where
  eps p q := ([(3,1)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,2), (1,false,3), (3,false,0), (3,true,2)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(0,false,2), (2,true,3)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m306 : Subtail.StackSummary.System 2 where
  eps p q := ([] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([(0,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([(1,false,1)] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
def m307 : Subtail.StackSummary.System 2 where
  eps p q := ([(0,0)] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
#eval IO.println ("GROWTH_CORPUS:" ++ toString [Subtail.FiniteTreeDecision.growthCheck m0,Subtail.FiniteTreeDecision.growthCheck m1,Subtail.FiniteTreeDecision.growthCheck m2,Subtail.FiniteTreeDecision.growthCheck m3,Subtail.FiniteTreeDecision.growthCheck m4,Subtail.FiniteTreeDecision.growthCheck m5,Subtail.FiniteTreeDecision.growthCheck m6,Subtail.FiniteTreeDecision.growthCheck m7,Subtail.FiniteTreeDecision.growthCheck m8,Subtail.FiniteTreeDecision.growthCheck m9,Subtail.FiniteTreeDecision.growthCheck m10,Subtail.FiniteTreeDecision.growthCheck m11,Subtail.FiniteTreeDecision.growthCheck m12,Subtail.FiniteTreeDecision.growthCheck m13,Subtail.FiniteTreeDecision.growthCheck m14,Subtail.FiniteTreeDecision.growthCheck m15,Subtail.FiniteTreeDecision.growthCheck m16,Subtail.FiniteTreeDecision.growthCheck m17,Subtail.FiniteTreeDecision.growthCheck m18,Subtail.FiniteTreeDecision.growthCheck m19,Subtail.FiniteTreeDecision.growthCheck m20,Subtail.FiniteTreeDecision.growthCheck m21,Subtail.FiniteTreeDecision.growthCheck m22,Subtail.FiniteTreeDecision.growthCheck m23,Subtail.FiniteTreeDecision.growthCheck m24,Subtail.FiniteTreeDecision.growthCheck m25,Subtail.FiniteTreeDecision.growthCheck m26,Subtail.FiniteTreeDecision.growthCheck m27,Subtail.FiniteTreeDecision.growthCheck m28,Subtail.FiniteTreeDecision.growthCheck m29,Subtail.FiniteTreeDecision.growthCheck m30,Subtail.FiniteTreeDecision.growthCheck m31,Subtail.FiniteTreeDecision.growthCheck m32,Subtail.FiniteTreeDecision.growthCheck m33,Subtail.FiniteTreeDecision.growthCheck m34,Subtail.FiniteTreeDecision.growthCheck m35,Subtail.FiniteTreeDecision.growthCheck m36,Subtail.FiniteTreeDecision.growthCheck m37,Subtail.FiniteTreeDecision.growthCheck m38,Subtail.FiniteTreeDecision.growthCheck m39,Subtail.FiniteTreeDecision.growthCheck m40,Subtail.FiniteTreeDecision.growthCheck m41,Subtail.FiniteTreeDecision.growthCheck m42,Subtail.FiniteTreeDecision.growthCheck m43,Subtail.FiniteTreeDecision.growthCheck m44,Subtail.FiniteTreeDecision.growthCheck m45,Subtail.FiniteTreeDecision.growthCheck m46,Subtail.FiniteTreeDecision.growthCheck m47,Subtail.FiniteTreeDecision.growthCheck m48,Subtail.FiniteTreeDecision.growthCheck m49,Subtail.FiniteTreeDecision.growthCheck m50,Subtail.FiniteTreeDecision.growthCheck m51,Subtail.FiniteTreeDecision.growthCheck m52,Subtail.FiniteTreeDecision.growthCheck m53,Subtail.FiniteTreeDecision.growthCheck m54,Subtail.FiniteTreeDecision.growthCheck m55,Subtail.FiniteTreeDecision.growthCheck m56,Subtail.FiniteTreeDecision.growthCheck m57,Subtail.FiniteTreeDecision.growthCheck m58,Subtail.FiniteTreeDecision.growthCheck m59,Subtail.FiniteTreeDecision.growthCheck m60,Subtail.FiniteTreeDecision.growthCheck m61,Subtail.FiniteTreeDecision.growthCheck m62,Subtail.FiniteTreeDecision.growthCheck m63,Subtail.FiniteTreeDecision.growthCheck m64,Subtail.FiniteTreeDecision.growthCheck m65,Subtail.FiniteTreeDecision.growthCheck m66,Subtail.FiniteTreeDecision.growthCheck m67,Subtail.FiniteTreeDecision.growthCheck m68,Subtail.FiniteTreeDecision.growthCheck m69,Subtail.FiniteTreeDecision.growthCheck m70,Subtail.FiniteTreeDecision.growthCheck m71,Subtail.FiniteTreeDecision.growthCheck m72,Subtail.FiniteTreeDecision.growthCheck m73,Subtail.FiniteTreeDecision.growthCheck m74,Subtail.FiniteTreeDecision.growthCheck m75,Subtail.FiniteTreeDecision.growthCheck m76,Subtail.FiniteTreeDecision.growthCheck m77,Subtail.FiniteTreeDecision.growthCheck m78,Subtail.FiniteTreeDecision.growthCheck m79,Subtail.FiniteTreeDecision.growthCheck m80,Subtail.FiniteTreeDecision.growthCheck m81,Subtail.FiniteTreeDecision.growthCheck m82,Subtail.FiniteTreeDecision.growthCheck m83,Subtail.FiniteTreeDecision.growthCheck m84,Subtail.FiniteTreeDecision.growthCheck m85,Subtail.FiniteTreeDecision.growthCheck m86,Subtail.FiniteTreeDecision.growthCheck m87,Subtail.FiniteTreeDecision.growthCheck m88,Subtail.FiniteTreeDecision.growthCheck m89,Subtail.FiniteTreeDecision.growthCheck m90,Subtail.FiniteTreeDecision.growthCheck m91,Subtail.FiniteTreeDecision.growthCheck m92,Subtail.FiniteTreeDecision.growthCheck m93,Subtail.FiniteTreeDecision.growthCheck m94,Subtail.FiniteTreeDecision.growthCheck m95,Subtail.FiniteTreeDecision.growthCheck m96,Subtail.FiniteTreeDecision.growthCheck m97,Subtail.FiniteTreeDecision.growthCheck m98,Subtail.FiniteTreeDecision.growthCheck m99,Subtail.FiniteTreeDecision.growthCheck m100,Subtail.FiniteTreeDecision.growthCheck m101,Subtail.FiniteTreeDecision.growthCheck m102,Subtail.FiniteTreeDecision.growthCheck m103,Subtail.FiniteTreeDecision.growthCheck m104,Subtail.FiniteTreeDecision.growthCheck m105,Subtail.FiniteTreeDecision.growthCheck m106,Subtail.FiniteTreeDecision.growthCheck m107,Subtail.FiniteTreeDecision.growthCheck m108,Subtail.FiniteTreeDecision.growthCheck m109,Subtail.FiniteTreeDecision.growthCheck m110,Subtail.FiniteTreeDecision.growthCheck m111,Subtail.FiniteTreeDecision.growthCheck m112,Subtail.FiniteTreeDecision.growthCheck m113,Subtail.FiniteTreeDecision.growthCheck m114,Subtail.FiniteTreeDecision.growthCheck m115,Subtail.FiniteTreeDecision.growthCheck m116,Subtail.FiniteTreeDecision.growthCheck m117,Subtail.FiniteTreeDecision.growthCheck m118,Subtail.FiniteTreeDecision.growthCheck m119,Subtail.FiniteTreeDecision.growthCheck m120,Subtail.FiniteTreeDecision.growthCheck m121,Subtail.FiniteTreeDecision.growthCheck m122,Subtail.FiniteTreeDecision.growthCheck m123,Subtail.FiniteTreeDecision.growthCheck m124,Subtail.FiniteTreeDecision.growthCheck m125,Subtail.FiniteTreeDecision.growthCheck m126,Subtail.FiniteTreeDecision.growthCheck m127,Subtail.FiniteTreeDecision.growthCheck m128,Subtail.FiniteTreeDecision.growthCheck m129,Subtail.FiniteTreeDecision.growthCheck m130,Subtail.FiniteTreeDecision.growthCheck m131,Subtail.FiniteTreeDecision.growthCheck m132,Subtail.FiniteTreeDecision.growthCheck m133,Subtail.FiniteTreeDecision.growthCheck m134,Subtail.FiniteTreeDecision.growthCheck m135,Subtail.FiniteTreeDecision.growthCheck m136,Subtail.FiniteTreeDecision.growthCheck m137,Subtail.FiniteTreeDecision.growthCheck m138,Subtail.FiniteTreeDecision.growthCheck m139,Subtail.FiniteTreeDecision.growthCheck m140,Subtail.FiniteTreeDecision.growthCheck m141,Subtail.FiniteTreeDecision.growthCheck m142,Subtail.FiniteTreeDecision.growthCheck m143,Subtail.FiniteTreeDecision.growthCheck m144,Subtail.FiniteTreeDecision.growthCheck m145,Subtail.FiniteTreeDecision.growthCheck m146,Subtail.FiniteTreeDecision.growthCheck m147,Subtail.FiniteTreeDecision.growthCheck m148,Subtail.FiniteTreeDecision.growthCheck m149,Subtail.FiniteTreeDecision.growthCheck m150,Subtail.FiniteTreeDecision.growthCheck m151,Subtail.FiniteTreeDecision.growthCheck m152,Subtail.FiniteTreeDecision.growthCheck m153,Subtail.FiniteTreeDecision.growthCheck m154,Subtail.FiniteTreeDecision.growthCheck m155,Subtail.FiniteTreeDecision.growthCheck m156,Subtail.FiniteTreeDecision.growthCheck m157,Subtail.FiniteTreeDecision.growthCheck m158,Subtail.FiniteTreeDecision.growthCheck m159,Subtail.FiniteTreeDecision.growthCheck m160,Subtail.FiniteTreeDecision.growthCheck m161,Subtail.FiniteTreeDecision.growthCheck m162,Subtail.FiniteTreeDecision.growthCheck m163,Subtail.FiniteTreeDecision.growthCheck m164,Subtail.FiniteTreeDecision.growthCheck m165,Subtail.FiniteTreeDecision.growthCheck m166,Subtail.FiniteTreeDecision.growthCheck m167,Subtail.FiniteTreeDecision.growthCheck m168,Subtail.FiniteTreeDecision.growthCheck m169,Subtail.FiniteTreeDecision.growthCheck m170,Subtail.FiniteTreeDecision.growthCheck m171,Subtail.FiniteTreeDecision.growthCheck m172,Subtail.FiniteTreeDecision.growthCheck m173,Subtail.FiniteTreeDecision.growthCheck m174,Subtail.FiniteTreeDecision.growthCheck m175,Subtail.FiniteTreeDecision.growthCheck m176,Subtail.FiniteTreeDecision.growthCheck m177,Subtail.FiniteTreeDecision.growthCheck m178,Subtail.FiniteTreeDecision.growthCheck m179,Subtail.FiniteTreeDecision.growthCheck m180,Subtail.FiniteTreeDecision.growthCheck m181,Subtail.FiniteTreeDecision.growthCheck m182,Subtail.FiniteTreeDecision.growthCheck m183,Subtail.FiniteTreeDecision.growthCheck m184,Subtail.FiniteTreeDecision.growthCheck m185,Subtail.FiniteTreeDecision.growthCheck m186,Subtail.FiniteTreeDecision.growthCheck m187,Subtail.FiniteTreeDecision.growthCheck m188,Subtail.FiniteTreeDecision.growthCheck m189,Subtail.FiniteTreeDecision.growthCheck m190,Subtail.FiniteTreeDecision.growthCheck m191,Subtail.FiniteTreeDecision.growthCheck m192,Subtail.FiniteTreeDecision.growthCheck m193,Subtail.FiniteTreeDecision.growthCheck m194,Subtail.FiniteTreeDecision.growthCheck m195,Subtail.FiniteTreeDecision.growthCheck m196,Subtail.FiniteTreeDecision.growthCheck m197,Subtail.FiniteTreeDecision.growthCheck m198,Subtail.FiniteTreeDecision.growthCheck m199,Subtail.FiniteTreeDecision.growthCheck m200,Subtail.FiniteTreeDecision.growthCheck m201,Subtail.FiniteTreeDecision.growthCheck m202,Subtail.FiniteTreeDecision.growthCheck m203,Subtail.FiniteTreeDecision.growthCheck m204,Subtail.FiniteTreeDecision.growthCheck m205,Subtail.FiniteTreeDecision.growthCheck m206,Subtail.FiniteTreeDecision.growthCheck m207,Subtail.FiniteTreeDecision.growthCheck m208,Subtail.FiniteTreeDecision.growthCheck m209,Subtail.FiniteTreeDecision.growthCheck m210,Subtail.FiniteTreeDecision.growthCheck m211,Subtail.FiniteTreeDecision.growthCheck m212,Subtail.FiniteTreeDecision.growthCheck m213,Subtail.FiniteTreeDecision.growthCheck m214,Subtail.FiniteTreeDecision.growthCheck m215,Subtail.FiniteTreeDecision.growthCheck m216,Subtail.FiniteTreeDecision.growthCheck m217,Subtail.FiniteTreeDecision.growthCheck m218,Subtail.FiniteTreeDecision.growthCheck m219,Subtail.FiniteTreeDecision.growthCheck m220,Subtail.FiniteTreeDecision.growthCheck m221,Subtail.FiniteTreeDecision.growthCheck m222,Subtail.FiniteTreeDecision.growthCheck m223,Subtail.FiniteTreeDecision.growthCheck m224,Subtail.FiniteTreeDecision.growthCheck m225,Subtail.FiniteTreeDecision.growthCheck m226,Subtail.FiniteTreeDecision.growthCheck m227,Subtail.FiniteTreeDecision.growthCheck m228,Subtail.FiniteTreeDecision.growthCheck m229,Subtail.FiniteTreeDecision.growthCheck m230,Subtail.FiniteTreeDecision.growthCheck m231,Subtail.FiniteTreeDecision.growthCheck m232,Subtail.FiniteTreeDecision.growthCheck m233,Subtail.FiniteTreeDecision.growthCheck m234,Subtail.FiniteTreeDecision.growthCheck m235,Subtail.FiniteTreeDecision.growthCheck m236,Subtail.FiniteTreeDecision.growthCheck m237,Subtail.FiniteTreeDecision.growthCheck m238,Subtail.FiniteTreeDecision.growthCheck m239,Subtail.FiniteTreeDecision.growthCheck m240,Subtail.FiniteTreeDecision.growthCheck m241,Subtail.FiniteTreeDecision.growthCheck m242,Subtail.FiniteTreeDecision.growthCheck m243,Subtail.FiniteTreeDecision.growthCheck m244,Subtail.FiniteTreeDecision.growthCheck m245,Subtail.FiniteTreeDecision.growthCheck m246,Subtail.FiniteTreeDecision.growthCheck m247,Subtail.FiniteTreeDecision.growthCheck m248,Subtail.FiniteTreeDecision.growthCheck m249,Subtail.FiniteTreeDecision.growthCheck m250,Subtail.FiniteTreeDecision.growthCheck m251,Subtail.FiniteTreeDecision.growthCheck m252,Subtail.FiniteTreeDecision.growthCheck m253,Subtail.FiniteTreeDecision.growthCheck m254,Subtail.FiniteTreeDecision.growthCheck m255,Subtail.FiniteTreeDecision.growthCheck m256,Subtail.FiniteTreeDecision.growthCheck m257,Subtail.FiniteTreeDecision.growthCheck m258,Subtail.FiniteTreeDecision.growthCheck m259,Subtail.FiniteTreeDecision.growthCheck m260,Subtail.FiniteTreeDecision.growthCheck m261,Subtail.FiniteTreeDecision.growthCheck m262,Subtail.FiniteTreeDecision.growthCheck m263,Subtail.FiniteTreeDecision.growthCheck m264,Subtail.FiniteTreeDecision.growthCheck m265,Subtail.FiniteTreeDecision.growthCheck m266,Subtail.FiniteTreeDecision.growthCheck m267,Subtail.FiniteTreeDecision.growthCheck m268,Subtail.FiniteTreeDecision.growthCheck m269,Subtail.FiniteTreeDecision.growthCheck m270,Subtail.FiniteTreeDecision.growthCheck m271,Subtail.FiniteTreeDecision.growthCheck m272,Subtail.FiniteTreeDecision.growthCheck m273,Subtail.FiniteTreeDecision.growthCheck m274,Subtail.FiniteTreeDecision.growthCheck m275,Subtail.FiniteTreeDecision.growthCheck m276,Subtail.FiniteTreeDecision.growthCheck m277,Subtail.FiniteTreeDecision.growthCheck m278,Subtail.FiniteTreeDecision.growthCheck m279,Subtail.FiniteTreeDecision.growthCheck m280,Subtail.FiniteTreeDecision.growthCheck m281,Subtail.FiniteTreeDecision.growthCheck m282,Subtail.FiniteTreeDecision.growthCheck m283,Subtail.FiniteTreeDecision.growthCheck m284,Subtail.FiniteTreeDecision.growthCheck m285,Subtail.FiniteTreeDecision.growthCheck m286,Subtail.FiniteTreeDecision.growthCheck m287,Subtail.FiniteTreeDecision.growthCheck m288,Subtail.FiniteTreeDecision.growthCheck m289,Subtail.FiniteTreeDecision.growthCheck m290,Subtail.FiniteTreeDecision.growthCheck m291,Subtail.FiniteTreeDecision.growthCheck m292,Subtail.FiniteTreeDecision.growthCheck m293,Subtail.FiniteTreeDecision.growthCheck m294,Subtail.FiniteTreeDecision.growthCheck m295,Subtail.FiniteTreeDecision.growthCheck m296,Subtail.FiniteTreeDecision.growthCheck m297,Subtail.FiniteTreeDecision.growthCheck m298,Subtail.FiniteTreeDecision.growthCheck m299,Subtail.FiniteTreeDecision.growthCheck m300,Subtail.FiniteTreeDecision.growthCheck m301,Subtail.FiniteTreeDecision.growthCheck m302,Subtail.FiniteTreeDecision.growthCheck m303,Subtail.FiniteTreeDecision.growthCheck m304,Subtail.FiniteTreeDecision.growthCheck m305,Subtail.FiniteTreeDecision.growthCheck m306,Subtail.FiniteTreeDecision.growthCheck m307])
