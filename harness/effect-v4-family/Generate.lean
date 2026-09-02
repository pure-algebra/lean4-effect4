import Effect4.Meta.Derive

/-!
The end-to-end fixture: one family, one program, its handler receipt in Lean,
and the generated Effect v4 module printed to stdout. `check.sh` byte-compares
the output with `fixture.ts` and runs the host harness over it with `tail.ts`.
-/

open Effects Effect4.Meta Effect4.Target.EffectV4

effect_signature Cell where
  | get : Nat ⟪ "read the cell", "current value" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell", "store" ⟫

/-- A pure atom; `atoms.ts` carries its host body. -/
def succ (n : Nat) : Nat := n + 1

effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  let y ← Cell.get()
  return y

/-- The Lean handler `tail.ts` mirrors with a `Ref`. -/
def cellLive : Cell.Service (StateT Nat Id) := fun name =>
  match name with
  | .get => fun _ => get
  | .put => fun n => set n

/-- The receipt the host run is compared against. -/
example : ((interpret cellLive.toHandler (incr 0)).run 41 : Nat × Nat) = (42, 42) := rfl

def main : IO Unit := do
  match source? Cell.rows [incr.script] [.named ["succ"] "./atoms.ts"] with
  | some source => IO.print source
  | none => throw (IO.userError "lowering refused the script")
