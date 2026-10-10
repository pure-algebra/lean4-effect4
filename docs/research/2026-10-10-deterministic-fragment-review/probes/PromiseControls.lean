import Controls
import ReviewRandomDescent
import Tools.Graph.Path

/-! Finite controls for the separate dependency and termination obligations in PLAN.md. -/
namespace DetProbe.PromiseControls
open Effect4 Effect4.Program Effect4.Machine Effect4.Program.Authoring
open DetProbe.Controls

/-- Each producer waits for the other's promise before completing its own. -/
def cycle : S :=
  bind "a" (Deferred.make .nat .never) (bind "b" (Deferred.make .nat .never)
    (workers
      (thenDo (Deferred.await (var "b")) (Forms.asVoid (Deferred.succeed (var "a") (nat 1))))
      (thenDo (Deferred.await (var "a")) (Forms.asVoid (Deferred.succeed (var "b") (nat 2))))
      Forms.void))

/-- The first producer publishes before waiting; an event graph admits this handshake. -/
def handshake : S :=
  bind "a" (Deferred.make .nat .never) (bind "b" (Deferred.make .nat .never)
    (workers
      (thenDo (Deferred.succeed (var "a") (nat 1)) (Forms.asVoid (Deferred.await (var "b"))))
      (thenDo (Deferred.await (var "a")) (Forms.asVoid (Deferred.succeed (var "b") (nat 2))))
      Forms.void))

#guard (elaborate cycle).toOption.isSome && (elaborate handshake).toOption.isSome
#guard (Api.explain (program cycle)).isNone && (Api.explain (program handshake)).isNone
#guard (Api.run (program cycle) 400).machine.armed.isEmpty
#guard !(Api.run (program cycle) 400).machine.finished
#guard (Api.run (program cycle) 400).machine.stuck.isNone
#guard (Api.run (program handshake) 400).machine.finished
#guard !accepted cycle && !accepted handshake
#eval ("single-writer cycle finished", (Api.run (program cycle) 400).machine.finished)
#eval ("ordered handshake finished", (Api.run (program handshake) 400).machine.finished)

/-- Passive occurrence edges use the existing graph path reader. -/
def endpoints : Nat × Nat → Nat × Nat := id
def cycleEdges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 0)]
#guard (Tools.Graph.Walk.read? endpoints 0 0 cycleEdges).isSome
#guard (Tools.Graph.Walk.read? endpoints 0 0 [(0, 1), (2, 0)]).isNone

/-- Checking a supplied event rank is finite evidence; rank synthesis is not part of this probe. -/
def rankFits (rank : List Nat) (edges : List (Nat × Nat)) : Bool :=
  edges.all fun (a,b) => match rank[a]?, rank[b]? with
    | some ra, some rb => ra < rb
    | _, _ => false
#guard !rankFits [0, 1, 2, 3] cycleEdges
-- a-produce -> b-await -> b-produce -> a-await
#guard rankFits [0, 3, 1, 2] [(0, 1), (2, 3), (0, 2), (3, 1)]
#guard !rankFits [0] [(0, 1)]

/-- Equal terminal results do not force equal numbers of steps. -/
def unequalLengths : Nat → Bool → Option Nat
  | 0, false => some 1
  | 0, true => some 2
  | 1, _ => some 3
  | 2, _ => some 4
  | 4, _ => some 3
  | _, _ => none
#guard RD.run unequalLengths 0 [false, false] = some 3
#guard RD.run unequalLengths 0 [true, false, false] = some 3
#guard unequalLengths 3 false = none && unequalLengths 3 true = none

end DetProbe.PromiseControls
