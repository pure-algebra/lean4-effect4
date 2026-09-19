import Lean
import Tools.GeneratedStamp
import Effect4.Machine.Term

/-!
# Effect4Gen.Atoms — the atom inventory from the constructor list

The atom alphabet is one inductive (`Effect4.Program.NativeAtom`, `src/Effect4/Machine/Term.lean`).
`all` used to be a hand-written list whose only guard was a theorem: a constructor left out of
it failed `all_complete`, which is a compile error in a *proof* rather than in the table. This
generator reads the constructor list off the environment and writes `all`, so the list cannot
disagree with the inductive in the first place; `all_complete` stays as the acceptance guard on
the emitted file (appended verbatim from `tools/Effect4Gen/guards/atominventory.lean`).

    lake env lean -M 4096 --run tools/Effect4Gen/Atoms.lean --group AtomInventory
      --imports Effect4.Machine.Term --out src/Effect4/Program/AtomInventory.lean
      --append tools/Effect4Gen/guards/atominventory.lean

Declaration order is the inductive's own (`InductiveVal.ctors`), which is the order the
generated profile, the OCaml alphabet and the wire already publish, so regenerating moves no
byte on any face.

The prelude's atom block is the sibling group `PreludeAtoms` (`tools/Effect4Gen/PreludeAtoms.lean`),
in a file of its own because it reads the *typing* half, which imports this group's own output:
one emitter importing both would be a module importing the file it writes.

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library, and its own axioms
are not the emitted code's. The emitted file prints its own receipts.
-/

open Lean Meta Elab

namespace Effect4Gen.Atoms

def shortName (n : Name) : String := n.componentsRev.head!.toString

/-- A constructor name the emitted list may spell as `.name`. The anonymous-constructor
notation takes an identifier, so a name needing French quotes is refused rather than
mis-spelled (`Main.lean`'s binder sanitising, at the one place this generator needs it). -/
def plainIdent (s : String) : Bool :=
  !s.isEmpty && s.front.isAlpha && s.all fun c => c.isAlphanum || c == '_'

/-- The constructors of `NativeAtom`, in declaration order. A constructor with fields is
refused: the inventory spells each atom as a bare constructor, and an atom carrying data
would need an enumeration of its own before it could be listed. -/
def atomCtors : MetaM (List String) := do
  let iv ← getConstInfoInduct ``Effect4.Program.NativeAtom
  let mut out : List String := []
  for c in iv.ctors do
    let ci ← getConstInfoCtor c
    let name := shortName c
    if ci.numFields != 0 then
      throwError "NativeAtom.{name} takes {ci.numFields} field(s); the inventory spells \
        each atom as a bare constructor"
    if !plainIdent name then
      throwError "NativeAtom.{name} is not a plain identifier; the emitted list spells \
        each atom as `.{name}`"
    out := out ++ [name]
  return out

/-- `all` and the two projections over it, wrapped at a readable width rather than one atom
per line. `names` and `covers` are emitted here rather than appended as guards because they
are the list read through, and a projection of a generated list belongs beside it. -/
def renderAll (names : List String) : String :=
  let items := names.map fun n => "." ++ n
  let step := fun (lines : List String × String) (item : String) =>
    let (done, current) := lines
    let candidate := if current.isEmpty then item else current ++ ", " ++ item
    if candidate.length > 92 then (done ++ [current ++ ","], item) else (done, candidate)
  let (done, last) := items.foldl step ([], "")
  let body := String.intercalate "\n   " (done ++ [last])
  "/-- Every atom of the alphabet, in the inductive's declaration order (which is the order\n\
   the generated profile, the OCaml alphabet and the wire publish). -/\n\
   def all : List NativeAtom :=\n  [" ++ body ++ "]\n\n" ++
  "/-- Every atom's name, in the inventory's order. -/\n\
   def names : List String := all.map name\n\n" ++
  "/-- A consumer inventory must cover every constructor, not just its own supplied rows. -/\n\
   def covers (consumerNames : List String) : Bool := names.all consumerNames.contains\n"

structure Args where
  group : String := "AtomInventory"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  types : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a => parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--" :: rest, a => parseArgs rest a
  | t :: rest, a =>
    if t.startsWith "--" then .error s!"unknown option {t}" else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) : MetaM (Array String) := do
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Atoms.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
  let names ← atomCtors
  match args.group with
  | "AtomInventory" =>
    let mut lines : Array String := #[
      "-- GENERATED by tools/Effect4Gen/Atoms.lean from the NativeAtom constructor list \
       (Machine/Term.lean). Do not edit.",
      "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):",
      "--   " ++ head]
    if let some p := args.append then
      lines := lines.push s!"-- Acceptance guards appended verbatim from: {p.replace "\\" "/"}"
    lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
    lines := lines ++ #["", "set_option autoImplicit false", "",
      "namespace Effect4.Program", "", "namespace NativeAtom", "",
      renderAll names, "end NativeAtom", "end Effect4.Program", ""]
    if let some p := args.append then
      let txt ← IO.FS.readFile p
      lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
    return lines
  | g => throwError "unknown group {g}: AtomInventory"

end Effect4Gen.Atoms

open Effect4Gen.Atoms in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args
    let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/Atoms.lean"
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
