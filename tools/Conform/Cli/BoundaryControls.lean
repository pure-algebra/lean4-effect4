import Conform.Core.Proof
import Conform.Layout.Layout
import Conform.Layout.Reflect

/-! Permanent controls for the false acceptance paths found during integration. -/
namespace Conform.BoundaryControls
open Lean Meta Elab Command Conform.Layout

theorem reflexive (n : Nat) : n = n := rfl
theorem otherStatement (n : Nat) : n ≤ n := Nat.le_refl n
def ordinary : Nat := 32
def frozen : ProofRef := checked_theorem% reflexive

run_meta do
  let t ← getConstInfo ``reflexive
  let p : ProofRef := ⟨``reflexive, t.levelParams, t.type⟩
  unless (← p.validate).isOk do throwError "a valid theorem was refused"
  if (← ({ p with name := ``ordinary } : ProofRef).validate).isOk then
    throwError "a Nat definition was accepted as a proof"
  if (← ({ p with name := ``otherStatement } : ProofRef).validate).isOk then
    throwError "a different proposition was accepted"
  let classical ← getConstInfo ``Classical.em
  if (← (ProofRef.mk ``Classical.em classical.levelParams classical.type).validate).isOk then
    throwError "the axiom policy was bypassed"

private def specialized : Rule :=
  { type := ``Option, applies := some [.con ``Nat []], discrimination := .variant,
    container := .tupleC }
private def target : Target :=
  { name := "roundtrip", rules := #[specialized],
    usages := #[⟨"nested", .con ``Option [.con ``Option [.con ``Nat []]]⟩] }

#guard (target.ruleFor? (.con ``Option [.con ``Bool []])).isNone
#guard (target.ruleFor? (.con ``Option [.con ``Nat []])).isSome
#guard (target.rule? ``Option).isNone

-- The entire serialized table survives, including its restriction and applied usage.
#guard match Policy.run (Target.reader (toJson target)) with
  | .error _ => false
  | .ok decoded => (toJson decoded).compress == (toJson target).compress
#guard !(Policy.run (TypeRef.reader (Json.mkObj
  [("format", .str "conform-type-v1"), ("kind", .str "param"),
   ("index", .num 0), ("ignored", .bool true)]))).isOk

inductive Indexed : Nat → Type where
  | value : Indexed 0
structure Unsupported where
  payload : Indexed 0

run_meta do
  let (_, gaps) ← Conform.Layout.Reflect.readType .propsOnly ``Unsupported []
  unless gaps.size == 1 do throwError "a value-indexed field was silently erased"
  let r ← Conform.Layout.Reflect.readWorld .propsOnly
    #[( ``Option, [.con ``Nat []]), (``Option, [.con ``Bool []])]
  unless r.world.types.size == 1 && r.world.applications.size == 2 do
    throwError "distinct applied requests were collapsed"

end Conform.BoundaryControls
