import Tools.View.Build
import Tools.View.Graph
import Tools.View.Algebra
import Effect4.Laws.Program.Typing.Rebase

/-! Finite audit controls at de2af691. No new general theorem or production representation.
The single law reader uses the existing checker-base-natural claim (R14).
The negative cache control changes its fixed environment premise.
The graph controls concern the tool layout, outside the semantics registry.
-/

open Effect4 Effect4.Program Tools.View

namespace GraphTreeAudit

def leaf : NativeEff := .succeed (.lit .unit)

def chain : Nat → NativeEff
  | 0 => leaf
  | n + 1 => .suspend (chain n)

def genCase : NativeEff := .gen (.cons (.yieldDiscard leaf)
  (.cons (.yieldDiscard (.suspend leaf)) (.cons (.ret (.lit .unit)) .nil)))

def actionCase : NativeEff := .withFiber (.fork leaf ⟨true, false, .inherit⟩)

def raceCase : NativeEff := .withFiber (.raceAll (.cons leaf (.cons (.suspend leaf) .nil)))

def layersCase : NativeEff := .provideLayer
  (.mergeAll (.cons (.effectDiscard leaf) (.cons (.fresh (.effectDiscard (.suspend leaf))) .nil)))
  false leaf

def cases : List (String × NativeEff) :=
  [("leaf", leaf), ("bind", .bind leaf (.bind leaf leaf)), ("gen", genCase),
   ("action", actionCase), ("race", raceCase), ("layers", layersCase)] ++
  [16, 32, 64].map (fun n => (s!"chain-{n}", chain n))

-- Two real readings share one existing product fold. No new syntax traversal is stored.
def countLayer (effectsOnly : Bool) : Algebra.Layer NativeOp (fun _ => Nat) :=
  fun fam _ args =>
    let here := if !effectsOnly || fam == .eff then 1 else 0
    args.foldl (fun n a => match a with | .child _ k => n + k | _ => n) here

def counts (p : NativeEff) : Nat × Nat :=
  Algebra.fold ((countLayer false).prod (countLayer true)) .eff p

#guard cases.all (fun (_, p) => counts p ==
  ((Node.addresses (.eff p)).length, (Build.effAddresses p).length))

-- Reader of the product law at a concrete program and two distinct carriers' readings.
example : counts genCase =
    (Algebra.fold (countLayer false) .eff genCase, Algebra.fold (countLayer true) .eff genCase) :=
  Algebra.cata_prod (countLayer false) (countLayer true) .eff genCase

-- Nearest Eff descendants cross other members of the syntax family.
#guard (view_eff genCase).2.all (fun a => match a with | .child .eff _ => false | _ => true)
#guard Build.frontier (Build.effAddresses genCase) [] == [[0, 0, 0], [0, 1, 0, 0]]
#guard Build.frontier (Build.effAddresses actionCase) [] == [[0, 0]]
#guard Build.filling actionCase (Build.effAddresses actionCase) [] ==
  some (.withFiber (.fork (Build.holeOf (Build.effAddresses actionCase) [0, 0]) ⟨true, false, .inherit⟩))

-- Positive relocation control and existing law reader, with the same environment/signature.
def readZero : NativeEff := .succeed (.var 0)
#guard Checker.check nativeSignature [.nat] [] readZero == .ok (EffTy.pure .nat)
#guard Checker.check nativeSignature [.nat] [4, 2] readZero == .ok (EffTy.pure .nat)
example : Checker.check nativeSignature [.nat] ([4, 2] ++ []) readZero =
    (Checker.check nativeSignature [.nat] [] readZero).mapError (TypeRefusal.rebase [4, 2]) :=
  Checker.check_rebase nativeSignature [4, 2] [.nat] [] readZero

-- Negative control: identical syntax does not determine the result independently of context.
#guard Checker.check nativeSignature [.string] [] readZero == .ok (EffTy.pure .string)
#guard Checker.check nativeSignature [] [] readZero == .error ⟨[], .term (.var 0)⟩

def graph (middle : String) : Graph :=
  { nodes := #[{ key := "a", line1 := "a" }, { key := middle, line1 := "middle" }, { key := "c", line1 := "c" }]
    edges := #[⟨"ab", 0, 1⟩, ⟨"bc", 1, 2⟩, ⟨"long", 0, 2⟩] }

-- The input keys are distinct and every endpoint exists in both cases.
#guard ((graph "b").nodes.toList.map (·.key)).eraseDups.length == 3
#guard ((graph "long@1").nodes.toList.map (·.key)).eraseDups.length == 3
#guard ((graph "long@1").edges.toList.map (·.key)).eraseDups.length == 3
#guard (graph "long@1").edges.all (fun e => e.src < 3 && e.dst < 3)
#guard (graph "b").ranks == [0, 1, 2]
#guard ((graph "b").layout.placed.toList.filter (·.node.isSome)).length == 3
#guard (graph "b").layout.boxesApart
#guard ((graph "long@1").layout.placed.toList.filter (·.node.isSome)).length == 4
#guard !(graph "long@1").layout.boxesApart

-- A backward-by-array-order edge does not imply a graph cycle.
def backwardDag : Graph := { nodes := #[{ key := "a", line1 := "a" }, { key := "b", line1 := "b" }], edges := #[⟨"ba", 1, 0⟩] }
#guard backwardDag.ranks == [0, 0]

-- Missing endpoints silently become empty keys; no input validation runs in chain.
def missingEndpoint : Graph := { nodes := #[{ key := "a", line1 := "a" }], edges := #[⟨"bad", 0, 8⟩] }
#guard Graph.chain missingEndpoint missingEndpoint.ranks ⟨"bad", 0, 8⟩ == ["a", ""]

def caseJson (name : String) (p : NativeEff) : Lean.Json :=
  let addrs := Build.effAddresses p
  Lean.Json.mkObj [
    ("name", Lean.toJson name),
    ("addresses", Lean.toJson addrs),
    ("productCounts", Lean.toJson (counts p)),
    ("frontiers", Lean.toJson (addrs.map (Build.frontier addrs))),
    ("fillingsPresent", Lean.toJson (addrs.all (fun a => (Build.filling p addrs a).isSome)))]

def graphJson (middle : String) : Lean.Json :=
  let laid := (graph middle).layout
  Lean.Json.mkObj [
    ("middle", Lean.toJson middle),
    ("boxes", Lean.toJson ((laid.placed.toList.filter (·.node.isSome)).map (·.key))),
    ("apart", Lean.toJson laid.boxesApart)]

end GraphTreeAudit

def main : IO Unit := do
  IO.println (Lean.Json.mkObj [
    ("cases", Lean.Json.arr (GraphTreeAudit.cases.map (fun (n, p) => GraphTreeAudit.caseJson n p)).toArray),
    ("graphControls", Lean.toJson (["b", "long@1"].map GraphTreeAudit.graphJson))]).compress
