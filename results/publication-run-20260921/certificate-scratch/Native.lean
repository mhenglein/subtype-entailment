import Subtail.RegularTreeCertificate

namespace Case0
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.var 0)
def graph : Graph 2 := ⟨#v[none, some (0, 0)]⟩
def rootTable : Vector (Fin 2) 2 := #v[0, 1]
def relationTable : Vector (Vector Bool 2) 2 := #v[#v[false, true], #v[false, false]]
def cert : Certificate 2 2 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 0 else
  if e == (.var 1) then 1 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_0:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case0

namespace Case1
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 1 := [((.prod (.var 0) .bot), (.var 0))]
def left : Expr 1 := (.var 0)
def right : Expr 1 := .bot
def graph : Graph 2 := ⟨#v[none, some (1, 0)]⟩
def rootTable : Vector (Fin 2) 1 := #v[1]
def relationTable : Vector (Vector Bool 2) 2 := #v[#v[true, false], #v[false, true]]
def cert : Certificate 1 2 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 1 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_1:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case1

namespace Case2
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_2:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case2

namespace Case3
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 0 := []
def left : Expr 0 := (.prod .bot (.prod .bot .bot))
def right : Expr 0 := (.prod .bot .bot)
def graph : Graph 3 := ⟨#v[none, some (0, 0), some (0, 1)]⟩
def rootTable : Vector (Fin 3) 0 := #v[]
def relationTable : Vector (Vector Bool 3) 3 := #v[#v[false, false, false], #v[false, false, false], #v[false, false, false]]
def cert : Certificate 0 3 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == .bot then 0 else
  if e == (.prod .bot .bot) then 1 else
  if e == (.prod .bot (.prod .bot .bot)) then 2 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_3:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case3

namespace Case4
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_4:" ++ toString (check input left right {cert with relation := fun _ _ => false}))
end Case4

namespace Case5
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_5:" ++ toString (check input left right {cert with relation := fun _ _ => true}))
end Case5

namespace Case6
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_6:" ++ toString (check input left right {cert with word := []}))
end Case6

namespace Case7
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_7:" ++ toString (check input left right {cert with embed := fun _ => 0}))
end Case7

namespace Case8
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_8:" ++ toString (check input left right {cert with roots := fun _ => 0}))
end Case8

namespace Case9
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.prod .bot (.var 1))), ((.prod .bot (.var 1)), (.var 0)), ((.var 1), (.prod (.var 0) .bot)), ((.prod (.var 0) .bot), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.prod .bot .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 2), some (1, 0), some (0, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, true, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.var 1) then 2 else
  if e == (.prod .bot (.var 1)) then 1 else
  if e == (.prod (.var 0) .bot) then 2 else
  if e == (.prod .bot .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_9:" ++ toString (check input left right {cert with graph := ⟨Vector.replicate _ none⟩}))
end Case9

namespace Case10
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (0, 3), some (0, 1), some (2, 1)]⟩
def rootTable : Vector (Fin 4) 2 := #v[2, 0]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[true, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 2 else
  if e == (.var 1) then 0 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_10:" ++ toString (check input left right cert))
end Case10

namespace Case11
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (2, 2), some (1, 2), some (1, 2), some (3, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[3, 3]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 3 else
  if e == (.var 0) then 3 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_11:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case11

namespace Case12
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (3, 0), some (0, 0), some (2, 1)]⟩
def rootTable : Vector (Fin 4) 2 := #v[2, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 2 else
  if e == (.var 1) then 2 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_12:" ++ toString (check input left right cert))
end Case12

namespace Case13
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (2, 1), some (1, 1), some (0, 2), some (1, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, true, true, false, false], #v[false, true, true, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == (.var 1) then 2 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_13:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case13

namespace Case14
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (3, 1), some (1, 3), some (2, 3)]⟩
def rootTable : Vector (Fin 4) 2 := #v[0, 1]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 0 else
  if e == (.var 1) then 1 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_14:" ++ toString (check input left right cert))
end Case14

namespace Case15
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (2, 2), some (0, 1), some (2, 1), some (2, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[2, 3]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 3 else
  if e == (.var 0) then 2 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_15:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case15

namespace Case16
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (1, 0), some (2, 1), some (0, 1)]⟩
def rootTable : Vector (Fin 4) 2 := #v[2, 0]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[true, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 2 else
  if e == (.var 1) then 0 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_16:" ++ toString (check input left right cert))
end Case16

namespace Case17
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (1, 1), some (3, 1), some (3, 0), some (1, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[1, 0]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 0 else
  if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_17:" ++ toString (check input left right cert))
end Case17

namespace Case18
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (1, 1), some (3, 0), some (1, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[3, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 3 else
  if e == (.var 1) then 2 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [false, true]
}
#eval IO.println ("CERT_18:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case18

namespace Case19
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (1, 2), some (1, 3), some (2, 1), some (1, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[1, 1]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, true, false, false, false], #v[false, false, true, false, false], #v[false, false, false, true, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == (.var 1) then 1 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_19:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case19

namespace Case20
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (0, 1), some (1, 3), some (2, 2)]⟩
def rootTable : Vector (Fin 4) 2 := #v[2, 3]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 2 else
  if e == (.var 1) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true, false, false]
}
#eval IO.println ("CERT_20:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case20

namespace Case21
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (1, 0), some (0, 3), some (2, 0), some (3, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[3, 3]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 3 else
  if e == (.var 0) then 3 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [false, true]
}
#eval IO.println ("CERT_21:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case21

namespace Case22
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (1, 0), some (1, 1), some (2, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[0, 3]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, true], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 0 else
  if e == (.var 1) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_22:" ++ toString (check input left right cert))
end Case22

namespace Case23
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (3, 2), some (1, 1), some (1, 2), some (1, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[1, 0]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 0 else
  if e == (.var 0) then 1 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_23:" ++ toString (check input left right cert))
end Case23

namespace Case24
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (2, 1), some (2, 3), some (1, 2)]⟩
def rootTable : Vector (Fin 4) 2 := #v[3, 0]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 3 else
  if e == (.var 1) then 0 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_24:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case24

namespace Case25
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (1, 2), some (0, 1), some (3, 2), some (0, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[0, 1]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, true, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 0 else
  if e == (.var 1) then 1 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [false]
}
#eval IO.println ("CERT_25:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case25

namespace Case26
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (2, 2), some (1, 2), some (2, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[3, 3]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 3 else
  if e == (.var 1) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_26:" ++ toString (check input left right cert))
end Case26

namespace Case27
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (2, 1), some (2, 1), some (0, 0), some (2, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[2, 3]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 3 else
  if e == (.var 0) then 2 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_27:" ++ toString (check input left right cert))
end Case27

namespace Case28
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (2, 2), some (2, 0), some (1, 3)]⟩
def rootTable : Vector (Fin 4) 2 := #v[0, 1]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, true, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 0 else
  if e == (.var 1) then 1 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_28:" ++ toString (check input left right cert))
end Case28

namespace Case29
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (2, 2), some (1, 3), some (2, 2), some (0, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[0, 0]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 0 else
  if e == (.var 0) then 0 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_29:" ++ toString (check input left right cert))
end Case29

namespace Case30
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (0, 3), some (3, 2), some (1, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[0, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 0 else
  if e == (.var 1) then 2 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_30:" ++ toString (check input left right cert))
end Case30

namespace Case31
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := [((.var 0), (.var 1))]
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 4 := ⟨#v[none, some (0, 0), some (1, 2), some (1, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 1]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[true, false, false, false], #v[false, true, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == (.var 1) then 1 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 3 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := []
}
#eval IO.println ("CERT_31:" ++ toString (check input left right cert))
end Case31

namespace Case32
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 0)
def right : Expr 2 := (.var 1)
def graph : Graph 4 := ⟨#v[none, some (3, 3), some (3, 1), some (1, 0)]⟩
def rootTable : Vector (Fin 4) 2 := #v[1, 2]
def relationTable : Vector (Vector Bool 4) 4 := #v[#v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false], #v[false, false, false, false]]
def cert : Certificate 2 4 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 0) then 1 else
  if e == (.var 1) then 2 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true, false, true]
}
#eval IO.println ("CERT_32:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case32

namespace Case33
open Subtail.ExpressionNormalization Subtail.RegularTreeCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input 2 := []
def left : Expr 2 := (.var 1)
def right : Expr 2 := (.prod (.var 0) .bot)
def graph : Graph 5 := ⟨#v[none, some (0, 0), some (2, 3), some (3, 1), some (2, 0)]⟩
def rootTable : Vector (Fin 5) 2 := #v[2, 2]
def relationTable : Vector (Vector Bool 5) 5 := #v[#v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false], #v[false, false, false, false, false]]
def cert : Certificate 2 5 := {
  graph := graph
  roots := fun x => rootTable.get x
  embed := fun e => if e == (.var 1) then 2 else
  if e == (.var 0) then 2 else
  if e == .bot then 0 else
  if e == (.prod (.var 0) .bot) then 4 else
  0
  relation := fun p q => (relationTable.get p).get q
  word := [true]
}
#eval IO.println ("CERT_33:" ++ toString (check input left right cert))
example : ¬ ExprEntails input left right :=
  check_not_entails input left right cert (by decide)
end Case33
