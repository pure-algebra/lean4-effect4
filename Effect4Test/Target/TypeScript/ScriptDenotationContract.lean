/-
Contract packet: packet D5 of `docs/research/2026-09-03-reification-plan.md`.
Per-program receipts for the script embedding: on every program of
`harness/trace/Generate.lean`'s `programs` list the graph `Script.toFlow`
builds denotes the program the script says (`Script.toFlow_denote`), and both
faces are defined. The families and programs are re-declared here because the
harness is not a library module; the scripts are the ones the DSL emits.

Doc comments cannot precede `#guard` or `effect_program`, so the receipts carry
line comments.
-/

import Effect4.Target.TypeScript.ScriptDenotation
import Effect4.Meta.Derive

namespace Effect4Test.Target.TypeScript.ScriptDenotationContract

open Effects Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

effect_signature Cell where
  | get : Nat ⟪ "read the cell", "current value" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell", "store" ⟫

def succ (n : Nat) : Nat := n + 1

effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  let y ← Cell.get()
  return y

effect_program twice (n : Nat) over Cell : Nat :=
  let _ ← Cell.put(n)
  let _ ← Cell.put(succ n)
  let y ← Cell.get()
  return y

effect_signature ECell where
  | tryGet : Except String Nat ⟪ "try to read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

def orZero (e : Except String Nat) : Nat :=
  match e with
  | .ok n => n
  | .error _ => 0

effect_program recover (n : Nat) over ECell : Nat :=
  let r ← ECell.tryGet()
  let _ ← ECell.put(n)
  return orZero r

effect_signature FCell where
  | get : Nat !! String ⟪ "read the cell, may fail" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

effect_program fallible (n : Nat) over FCell : Nat :=
  let _ ← FCell.put(n)
  let x ← FCell.get()
  return x

/-- Both atoms the four scripts call. `harness/trace/Generate.lean` embeds only
the `Cell` programs, so its table carries `succ` alone; the receipts here cover
every program of its `programs` list, so `orZero` joins it. -/
def atoms : AtomTable :=
  [("succ", "number", "number"), ("orZero", "Result.Result<number, string>", "number")]

/-! ## The two faces are defined, and the graph is admitted -/

-- Whether a script embeds, its embedding is admitted, and its denotation is
-- defined: `some true` on all four.
def receipt (rows : ServiceRow) (script : Script) : Option Bool :=
  (Script.toFlow rows atoms script).map fun (table, raw) =>
    (match admit (tableAlphabet ⟨0⟩ table) raw with
      | .ok _ => true
      | .error _ => false) &&
    (denoteScript ⟨0⟩ rows atoms table script (.nat 0)).isSome

#guard receipt Cell.rows incr.script = some true
#guard receipt Cell.rows twice.script = some true
#guard receipt ECell.rows recover.script = some true
#guard receipt FCell.rows fallible.script = some true

-- The table each embedding mints: the family's rows first, then one row per
-- literal and atom the script materializes.
#guard (Script.toFlow Cell.rows atoms incr.script).map (·.1.length) = some 5
#guard (Script.toFlow Cell.rows atoms twice.script).map (·.1.length) = some 4
#guard (Script.toFlow ECell.rows atoms recover.script).map (·.1.length) = some 4
#guard (Script.toFlow FCell.rows atoms fallible.script).map (·.1.length) = some 3

-- One block per performed operation, plus the `ret`.
#guard (Script.toFlow Cell.rows atoms incr.script).map (·.2.blocks.length) = some 7
#guard (Script.toFlow Cell.rows atoms twice.script).map (·.2.blocks.length) = some 6
#guard (Script.toFlow ECell.rows atoms recover.script).map (·.2.blocks.length) = some 5
#guard (Script.toFlow FCell.rows atoms fallible.script).map (·.2.blocks.length) = some 4

-- The blocks carry the ids `0, 1, 2, …` in order: the `Build` invariant, read
-- off the embedding rather than proved about it.
def orderedIds (raw : RawFlow String) : Bool :=
  (raw.blocks.zipIdx.all fun (block, i) => block.id == ⟨i⟩)

#guard (Script.toFlow Cell.rows atoms incr.script).map (fun p => orderedIds p.2) = some true
#guard (Script.toFlow Cell.rows atoms twice.script).map (fun p => orderedIds p.2) = some true
#guard (Script.toFlow ECell.rows atoms recover.script).map (fun p => orderedIds p.2) = some true
#guard (Script.toFlow FCell.rows atoms fallible.script).map (fun p => orderedIds p.2) = some true

/-! ## `Script.toFlow_denote`, instance by instance

Each receipt is the theorem at that program's rows, atoms and script. The
hypotheses are the two `some` facts the `#guard`s above already witness; the
conclusion is the equality of the graph's denotation with the script's. -/

theorem incr_toFlow_denote (table : List OpSpec) (raw : RawFlow String)
    (embedded : Script.toFlow Cell.rows atoms incr.script = some (table, raw))
    (cycles : CyclesWF raw) (input : Val)
    (program : Program (Sig (tableAlphabet ⟨0⟩ table)) Val)
    (denoted : denoteScript ⟨0⟩ Cell.rows atoms table incr.script input = some program) :
    denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw cycles raw.entry [input] []
      = liftScript program :=
  Script.toFlow_denote embedded cycles denoted

theorem twice_toFlow_denote (table : List OpSpec) (raw : RawFlow String)
    (embedded : Script.toFlow Cell.rows atoms twice.script = some (table, raw))
    (cycles : CyclesWF raw) (input : Val)
    (program : Program (Sig (tableAlphabet ⟨0⟩ table)) Val)
    (denoted : denoteScript ⟨0⟩ Cell.rows atoms table twice.script input = some program) :
    denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw cycles raw.entry [input] []
      = liftScript program :=
  Script.toFlow_denote embedded cycles denoted

theorem recover_toFlow_denote (table : List OpSpec) (raw : RawFlow String)
    (embedded : Script.toFlow ECell.rows atoms recover.script = some (table, raw))
    (cycles : CyclesWF raw) (input : Val)
    (program : Program (Sig (tableAlphabet ⟨0⟩ table)) Val)
    (denoted : denoteScript ⟨0⟩ ECell.rows atoms table recover.script input = some program) :
    denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw cycles raw.entry [input] []
      = liftScript program :=
  Script.toFlow_denote embedded cycles denoted

theorem fallible_toFlow_denote (table : List OpSpec) (raw : RawFlow String)
    (embedded : Script.toFlow FCell.rows atoms fallible.script = some (table, raw))
    (cycles : CyclesWF raw) (input : Val)
    (program : Program (Sig (tableAlphabet ⟨0⟩ table)) Val)
    (denoted : denoteScript ⟨0⟩ FCell.rows atoms table fallible.script input = some program) :
    denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw cycles raw.entry [input] []
      = liftScript program :=
  Script.toFlow_denote embedded cycles denoted

/-! ## The per-program receipt `effect_program` now emits

The elaborator emits one `example` per program; these `#guard`s pin the two
sides it compares, so a regression in either traversal is visible here and not
only as a failed anonymous `example`. -/

#guard incr.script.operationNames = ["get", "put", "get"]
#guard twice.script.operationNames = ["put", "put", "get"]
#guard recover.script.operationNames = ["tryGet", "put"]
#guard fallible.script.operationNames = ["put", "get"]

#guard performedNames (F := Cell) Cell.Name.spelling Cell.answerDefault (incr 0)
  = incr.script.operationNames
#guard performedNames (F := Cell) Cell.Name.spelling Cell.answerDefault (twice 7)
  = twice.script.operationNames
#guard performedNames (F := ECell) ECell.Name.spelling ECell.answerDefault (recover 5)
  = recover.script.operationNames
#guard performedNames (F := FCell) FCell.Name.spelling FCell.answerDefault (fallible 5)
  = fallible.script.operationNames

/-! ## A pure operation erases

`interpret_vis_of_pure` at the table service: a literal row is answered purely,
so interpreting past it is interpreting the continuation at its value. -/

def litTable : List OpSpec :=
  [{ name := "lit", kind := .lit (.nat 7), requestTy := "number", answerTy := "number" }]

def litService : FlowService (tableAlphabet ⟨0⟩ litTable) Id :=
  tableService ⟨0⟩ litTable (fun _ _ => pure .unit) (fun _ v => v)

example (next : Val → Program (Sig (tableAlphabet ⟨0⟩ litTable)) Val) :
    interpret (FlowService.toService litService).toHandler
        (.vis (⟨⟨0, by decide⟩, .unit⟩ : (Sig (tableAlphabet ⟨0⟩ litTable)).Op) next)
      = interpret (FlowService.toService litService).toHandler (next (.nat 7)) :=
  interpret_vis_of_pure (S := Sig (tableAlphabet ⟨0⟩ litTable))
    (FlowService.toService litService).toHandler
    (⟨⟨0, by decide⟩, .unit⟩ : (Sig (tableAlphabet ⟨0⟩ litTable)).Op)
    (Effects.Trace.Val.nat 7) next rfl

end Effect4Test.Target.TypeScript.ScriptDenotationContract
