/-
Contract packet: the trace lane (`docs/TRACE-DAG.md`), Effect4 consumer side.
Light ceremony by operator ruling D2: contract, battery and code land together.

Frozen: the profile's instance of the shared alphabet and the agreement
judgment. Executable receipts: the DSL's traced service logs exactly the
operations of `incr`, and forgetting the log is the plain run.
-/

import Effect4.Semantics.Observation
import Effect4.Meta.Derive

namespace Effect4Test.Semantics.ObservationContract

open Effects Effect4 Effect4.Meta

#check (@Effect4.Trace.Event : Type)
#check (@Effect4.Trace.Log : Type)
#check (@Effect4.Trace.maskTable : List (String × Effect4.Trace.Mask))
#check (@Effect4.Trace.agree : Effect4.Trace.Mask → Effect4.Trace.Log → Effect4.Trace.Log → Bool)
#check (@Effect4.Trace.agree_refl : ∀ (mask : Effect4.Trace.Mask) (log : Effect4.Trace.Log),
  Effect4.Trace.agree mask log log = true)
#check (@Effect4.Trace.agree_m1_of_agree_m2 : ∀ {left right : Effect4.Trace.Log},
  Effect4.Trace.agree Effects.Trace.Mask.m2 left right = true →
    Effect4.Trace.agree Effects.Trace.Mask.m1 left right = true)

/-- The mask table names exactly the three registered masks, in order. -/
example : Effect4.Trace.maskTable.map Prod.fst = ["outcome", "m1", "m2"] := by decide

/-! ## The DSL's trace face on the harness family -/

effect_signature Cell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

def succ (n : Nat) : Nat := n + 1

effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  let y ← Cell.get()
  return y

def cellLive : Cell.Service (StateT Nat Id) := fun name =>
  match name with
  | .get => fun _ => get
  | .put => fun n => set n

/-- The traced run as a first-order value: answer, log, final cell. -/
def receipt : (Nat × Effect4.Trace.Log) × Nat :=
  ((interpret (Cell.traced cellLive).toHandler (incr 0)).run []).run 41

example :
    receipt =
      ((42,
        [ .op "get" .unit, .answer "get" (.nat 41)
        , .op "put" (.nat 42), .answer "put" .unit
        , .op "get" .unit, .answer "get" (.nat 42) ]), 42) := by
  decide

/-- Forgetting the log is the plain run (the P-T1 law, instantiated). -/
example := Family.Service.interpret_traced_fst (δ := Nat) (ρ := Nat)
  Cell.Name.spelling Cell.encodeParam Cell.encodeAnswer cellLive (incr 0) []

/-- Agreement is a projection equality: the receipt's log agrees with itself
under every registered mask. -/
example : Effect4.Trace.maskTable.all (fun entry =>
    Effect4.Trace.agree entry.2 receipt.1.2 receipt.1.2) = true := by
  decide

end Effect4Test.Semantics.ObservationContract
