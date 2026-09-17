import Lean
import Tools.GeneratedStamp

/-!
# Effect4Gen.LayerView — the one-layer view of the program family (R4.2)

From the constructor declarations of the `Eff` block, nothing hand-listed:

* `ArgF Op R`: one argument of a constructor, by sort. A family member is a child at the
  carrier `R`; every other argument type of the block gets one constructor.
* `EffAlgebra.ofLayer`: a generic layer function `fam → ctor → List (ArgF Op R) → R fam` as an
  `EffAlgebra`, so the generated `cata_*` does the recursion and a table-driven printer has no
  arm per constructor.
* `argSorts`: the sorts of a constructor's arguments, by family and name.
* `build`: the inverse of the view at the tree itself, with one `rfl` equation per constructor.

An argument type the naming table below does not know is an error naming the constructor: a new
argument type must be given a sort here before anything downstream can ignore it.
-/

open Lean Meta Elab

namespace Effect4Gen.LayerView

def shortName (n : Name) : String := n.componentsRev.head!.toString

def famLabel : Name → String
  | `Effect4.Program.Eff => "eff"
  | `Effect4.Program.Stmt => "stmt"
  | `Effect4.Program.Stmts => "stmts"
  | `Effect4.Program.Effs => "effs"
  | `Effect4.Program.ActionTerm => "action"
  | `Effect4.Program.LayerTerm => "layer"
  | `Effect4.Program.LayerTerms => "layers"
  | n => n.componentsRev.head!.toString.toLower

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

/-- The sort name of a leaf argument type. The table is the generator's one hand list, and an
unknown type is refused rather than defaulted. -/
def leafSort : String → Option String
  | "Effect4.Program.Term" => some "term"
  | "Option Effect4.Program.Term" => some "optTerm"
  | "Effect4.Program.CauseTerm" => some "cause"
  | "Effect4.Program.Lit" => some "lit"
  | "Effect4.ServiceKey" => some "key"
  | "Effect4.Program.Decision" => some "decision"
  | "Effect4.Supervision.ForkOptions" => some "forkOptions"
  | "Effect4.Supervision.ObserverMode" => some "mode"
  | "Option Effect4.Program.Ty" => some "optTy"
  | "Bool" => some "bool"
  | "Nat" => some "nat"
  | "List Nat" => some "path"
  | "Op" => some "op"
  | _ => none

structure Arg where
  name : String
  /-- The family label when the argument is a member of the block. -/
  recFam : Option String
  /-- The sort name: `child` for a member, else the leaf sort. -/
  sort : String
  tyText : String

structure Ctor where
  fam : String
  famName : Name
  short : String
  field : String
  args : List Arg

def readBlock (root : Name) : MetaM (List (String × Name) × List Ctor) := do
  let iv ← getConstInfoInduct root
  let members := iv.all
  let mut fams := []
  let mut out := []
  for fam in members do
    let fv ← getConstInfoInduct fam
    let label := famLabel fam
    fams := fams ++ [(label, fam)]
    for c in fv.ctors do
      let ci ← getConstInfoCtor c
      let args ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
        let mut acc := []
        let mut i : Nat := 0
        for x in xs[ci.numParams:] do
          let ty ← inferType x
          let tyText ← srcOf ty
          let recFam := match ty.getAppFn with
            | .const n _ => if members.contains n then some (famLabel n) else none
            | _ => none
          let sort ← match recFam with
            | some _ => pure "child"
            | none => match leafSort tyText with
              | some s => pure s
              | none => throwError "LayerView: constructor {c} argument {i} has type {tyText}, \
                  which has no sort; add it to `leafSort` in tools/Effect4Gen/LayerView.lean"
          acc := acc ++ [({ name := s!"a{i}", recFam, sort, tyText } : Arg)]
          i := i + 1
        return acc
      out := out ++ [({ fam := label, famName := fam, short := shortName c,
                        field := s!"{label}_{shortName c}", args } : Ctor)]
  return (fams, out)

/-- The leaf sorts of the block, each with its type, in first-occurrence order. -/
def leafSorts (ctors : List Ctor) : List (String × String) := Id.run do
  let mut seen : List (String × String) := []
  for c in ctors do
    for a in c.args do
      if a.recFam.isNone && !(seen.any (·.1 == a.sort)) then
        seen := seen ++ [(a.sort, a.tyText)]
  return seen

def packArg (a : Arg) : String :=
  match a.recFam with
  | some f => s!".child .{f} {a.name}"
  | none => s!".{a.sort} {a.name}"

def emit (root : Name) : MetaM String := do
  let (fams, ctors) ← readBlock root
  let leaves := leafSorts ctors
  let mut s := ""
  s := s ++ "/-- One argument of a constructor, by sort. A member of the family is a child at the\n"
  s := s ++ "carrier; every other argument type of the block has its own constructor. -/\n"
  s := s ++ "inductive ArgF (Op : Type) (R : EffFam → Type u) where\n"
  s := s ++ "  | child (fam : EffFam) (r : R fam)\n"
  for (sort, ty) in leaves do
    s := s ++ s!"  | {sort} (v : {ty})\n"
  s := s ++ "\n"

  s := s ++ "/-- The sort of an argument, without its value. -/\n"
  s := s ++ "inductive ArgSort where\n"
  s := s ++ "  | child (fam : EffFam)\n"
  for (sort, _) in leaves do
    s := s ++ s!"  | {sort}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"

  s := s ++ "/-- A generic layer function as an algebra: every constructor packs its arguments, in\n"
  s := s ++ "declaration order, under its family and its name. -/\n"
  s := s ++ "def EffAlgebra.ofLayer {Op : Type} {R : EffFam → Type u}\n"
  s := s ++ "    (layer : (fam : EffFam) → String → List (ArgF Op R) → R fam) : EffAlgebra Op R where\n"
  for c in ctors do
    let binders := String.intercalate " " (c.args.map (·.name))
    let lhs := if c.args.isEmpty then "" else " " ++ binders
    let packed := String.intercalate ", " (c.args.map packArg)
    s := s ++ s!"  {c.field}{lhs} := layer .{c.fam} \"{c.short}\" [{packed}]\n"
  s := s ++ "\n"

  s := s ++ "/-- The sorts of a constructor's arguments, in declaration order; `none` for a name that\n"
  s := s ++ "is no constructor of the family. -/\n"
  s := s ++ "def argSorts : EffFam → String → Option (List ArgSort)\n"
  for c in ctors do
    let sorts := String.intercalate ", " (c.args.map fun a =>
      match a.recFam with
      | some f => s!".child .{f}"
      | none => s!".{a.sort}")
    s := s ++ s!"  | .{c.fam}, \"{c.short}\" => some [{sorts}]\n"
  s := s ++ "  | _, _ => none\n\n"

  s := s ++ "/-- The constructor names of a family, in declaration order. -/\n"
  s := s ++ "def ctorNames : EffFam → List String\n"
  for (label, _) in fams do
    let names := String.intercalate ", " ((ctors.filter (·.fam == label)).map fun c => s!"\"{c.short}\"")
    s := s ++ s!"  | .{label} => [{names}]\n"
  s := s ++ "\n"

  s := s ++ "/-- The inverse of the view at the tree itself: a constructor from its name and its\n"
  s := s ++ "arguments; `none` when the name or the sorts are not the constructor's. -/\n"
  s := s ++ "def build {Op : Type} : (fam : EffFam) → String → List (ArgF Op (EffSelfCarrier Op)) →\n"
  s := s ++ "    Option (EffSelfCarrier Op fam)\n"
  for c in ctors do
    let pats := String.intercalate ", " (c.args.map packArg)
    let binders := String.intercalate " " (c.args.map (·.name))
    let rhs := if c.args.isEmpty then s!"{c.famName}.{c.short}" else s!"{c.famName}.{c.short} {binders}"
    s := s ++ s!"  | .{c.fam}, \"{c.short}\", [{pats}] => some ({rhs})\n"
  s := s ++ "  | _, _, _ => none\n\n"

  s := s ++ "/-- The view rebuilt: the layer function that builds folds every tree to itself. One\n"
  s := s ++ "equation per constructor, each by `rfl`. -/\n"
  for c in ctors do
    let binders := String.intercalate " " (c.args.map (·.name))
    let quant := if c.args.isEmpty then "" else
      "(" ++ String.intercalate ") (" (c.args.map fun a =>
        match a.recFam with
        | some f => s!"{a.name} : EffSelfCarrier Op .{f}"
        | none => s!"{a.name} : {a.tyText}") ++ ") "
    let packed := String.intercalate ", " (c.args.map packArg)
    let rhs := if c.args.isEmpty then s!"{c.famName}.{c.short}" else s!"{c.famName}.{c.short} {binders}"
    s := s ++ s!"theorem build_{c.field} \{Op : Type} {quant}:\n"
    s := s ++ s!"    build (Op := Op) .{c.fam} \"{c.short}\" [{packed}] = some ({rhs}) := rfl\n"
  s := s ++ "\n"
  return s

structure Args where
  group : String := "LayerView"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  types : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a =>
    parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | t :: rest, a =>
    if t.startsWith "--" then
      if rest.isEmpty then .error s!"{t} needs a value" else .error s!"unknown option {t}"
    else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) : MetaM (Array String) := do
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/LayerView.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports
    ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
    ++ String.join (args.types.map fun t => " " ++ t)
  let mut lines : Array String := #[
    "-- GENERATED by tools/Effect4Gen/LayerView.lean from the Lean environment. Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):",
    "--   " ++ head]
  if let some p := args.append then
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {p.replace "\\" "/"}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #["", "set_option autoImplicit false", "", "namespace Effect4.Program", "",
    "universe u", ""]
  for t in args.types do
    lines := lines.push (← emit t.toName)
  lines := lines ++ #["end Effect4.Program", ""]
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
  return lines

end Effect4Gen.LayerView

open Effect4Gen.LayerView in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  if args.types.isEmpty then
    throw (IO.userError "no types to generate")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args
    let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/LayerView.lean"
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
