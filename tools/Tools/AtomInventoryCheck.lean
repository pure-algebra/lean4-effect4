import OCaml5.Eff.Emit

/-!
# Native atom emitter controls

Thin test driver over the real emitter check. Properties tested: actual target rows pass;
removing any native name fails; an empty consumer fails. This exercises generator refusal,
not just the Boolean inventory theorem, and writes no generated artifacts.
-/

open Effect4.Program OCaml5.Eff

def main : IO Unit := do
  match checkAtoms with
  | .ok () => pure ()
  | .error message => throw (IO.userError message)
  match checkAtomCoverage NativeAtom.names with
  | .ok () => pure ()
  | .error message => throw (IO.userError message)
  for atom in NativeAtom.all do
    match checkAtomCoverage (NativeAtom.names.filter (· != atom.name)) with
    | .error _ => pure ()
    | .ok () => throw (IO.userError s!"omission control accepted {atom.name}")
  match checkAtomCoverage [] with
  | .error _ => pure ()
  | .ok () => throw (IO.userError "empty consumer control accepted")
  IO.println s!"native atom emitter: {NativeAtom.all.length} names covered; {NativeAtom.all.length + 1} omission controls refused"
