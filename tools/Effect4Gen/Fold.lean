import Lean
import Tools.GeneratedStamp

open Lean Meta Elab

namespace Effect4Gen.Fold

def famLabel : Name → String
  | `Effect4.Program.Eff => "eff"
  | `Effect4.Program.Stmt => "stmt"
  | `Effect4.Program.Stmts => "stmts"
  | `Effect4.Program.Effs => "effs"
  | `Effect4.Program.ActionTerm => "action"
  | `Effect4.Program.LayerTerm => "layer"
  | `Effect4.Program.LayerTerms => "layers"
  | `Effect4.Program.Ty => "ty"
  | `Effect4.Program.Term => "term"
  | `Effect4.Program.Terms => "terms"
  | `Effect4.Program.CauseTerm => "cause"
  | n => n.componentsRev.head!.toString.toLower

def shortName (n : Name) : String := n.componentsRev.head!.toString

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

structure Arg where
  name : String
  recFam : Option String
  tyText : String

structure CtorRow where
  fam : String
  ctor : String
  field : String
  args : List Arg

def readBlock (root : Name) : MetaM (Bool × String × List (String × Name × List CtorRow)) := do
  let iv ← getConstInfoInduct root
  let members := iv.all
  let isParam := iv.numParams > 0
  let blockName := match root with
    | `Effect4.Program.Eff => "Eff"
    | `Effect4.Program.Ty => "Ty"
    | `Effect4.Program.Term => "Term"
    | `Effect4.Program.CauseTerm => "CauseTerm"
    | n => shortName n
  let mut out := []
  for fam in members do
    let fv ← getConstInfoInduct fam
    let label := famLabel fam
    let mut rows := []
    for c in fv.ctors do
      let ci ← getConstInfoCtor c
      let args ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
        let mut acc := []
        let mut i := 0
        for x in xs[ci.numParams:] do
          let ty ← inferType x
          let head := ty.getAppFn
          let recFam := match head with
            | .const n _ => if members.contains n then some (famLabel n) else none
            | _ => none
          acc := acc ++ [({ name := s!"a{i}", recFam, tyText := ← srcOf ty } : Arg)]
          i := i + 1
        return acc
      rows := rows ++ [({ fam := label, ctor := shortName c,
                          field := s!"{label}_{shortName c}", args } : CtorRow)]
    out := out ++ [(label, fam, rows)]
  return (isParam, blockName, out)

def recComb (calls : List String) : String :=
  match calls with
  | [] => ""
  | [c] => c
  | c :: rest => s!"op {c} ({recComb rest})"

def emitBlock (root : Name) : MetaM (String × List String) := do
  let (isParam, blockName, block) ← readBlock root
  let labels := block.map (·.1)
  let famType := s!"{blockName}Fam"
  let algType := s!"{blockName}Algebra"
  let homType := s!"{blockName}Hom"
  let opParam := if isParam then "(Op : Type) " else ""
  let opArg := if isParam then "{Op : Type} " else ""
  let opApp := if isParam then " Op" else ""
  let mut s := ""
  s := s ++ s!"inductive {famType} where\n"
  for l in labels do s := s ++ s!"  | {l}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"

  s := s ++ s!"structure {algType} {opParam}(R : {famType} → Type u) where\n"
  for (label, _, rows) in block do
    for r in rows do
      let argTexts := r.args.map fun a =>
        match a.recFam with
        | some f => s!"R .{f}"
        | none => s!"({a.tyText})"
      let arrow := String.intercalate " → " (argTexts ++ [s!"R .{label}"])
      s := s ++ s!"  {r.field} : {arrow}\n"
  s := s ++ "\n"

  let isMutual := block.length > 1
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def cata_{label} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R)\n"
    s := s ++ s!"    (node : {fam}{opApp}) : R .{label} :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>"
        else s!"  | .{r.ctor} " ++ String.intercalate " " (r.args.map (·.name)) ++ " =>"
      let callArgs := r.args.map fun a =>
        match a.recFam with
        | some f => s!"(cata_{f} alg {a.name})"
        | none => a.name
      s := s ++ pat ++ s!" alg.{r.field}"
      for c in callArgs do s := s ++ " " ++ c
      s := s ++ "\n"
    s := s ++ "termination_by structural node\n"
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  s := s ++ s!"structure {homType} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R) where\n"
  for (label, fam, _) in block do
    s := s ++ s!"  f_{label} : {fam}{opApp} → R .{label}\n"
  for (label, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhsArgs := if r.args.isEmpty then "" else " " ++ binders
      let rhsArgs := String.intercalate " " (r.args.map fun a =>
        match a.recFam with
        | some f => s!"(f_{f} {a.name})"
        | none => a.name)
      let rhsArgs := if rhsArgs.isEmpty then "" else " " ++ rhsArgs
      let quant := if r.args.isEmpty then "" else s!"∀ {binders}, "
      s := s ++ s!"  h_{r.field} : {quant}f_{label} (.{r.ctor}{lhsArgs}) = alg.{r.field}{rhsArgs}\n"
  s := s ++ "\n"

  let mut receipts := []
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"theorem hom_eq_cata_{label} {opArg}\{R : {famType} → Type u}\n"
    s := s ++ s!"    \{alg : {algType}{opApp} R} (hom : {homType} alg) (node : {fam}{opApp}) :\n"
    s := s ++ s!"    hom.f_{label} node = cata_{label} alg node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let rewrites := (r.args.filterMap fun a =>
        a.recFam.map fun f => s!"hom_eq_cata_{f} hom {a.name}")
      let rwList := String.intercalate ", " ((s!"hom.h_{r.field}" ++
        (if r.args.isEmpty then "" else " " ++ binders)) :: rewrites)
      s := s ++ pat ++ s!"\n    simp only [cata_{label}, {rwList}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"hom_eq_cata_{label}"]
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  -- foldMap
  let fParams := String.intercalate " " (block.map fun (l, f, _) =>
    s!"(f_{l} : {f}{opApp} → M := fun _ => unit)")
  let fArgs := String.intercalate " " (block.map fun (l, _, _) => s!"f_{l}")
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def foldMap_{label} {opArg}\{M : Type u} (unit : M) (op : M → M → M) (node : {fam}{opApp})\n"
    s := s ++ s!"    {fParams} : M :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let childCalls := r.args.filterMap fun a =>
        a.recFam.map fun f => s!"(foldMap_{f} unit op {a.name} {fArgs})"
      let nodeExpr := if binders.isEmpty then s!".{r.ctor}" else s!".{r.ctor} {binders}"
      let rhs := match childCalls with
        | [] => s!"f_{label} ({nodeExpr})"
        | _ => s!"op (f_{label} ({nodeExpr})) ({recComb childCalls})"
      s := s ++ pat ++ s!"\n    {rhs}\n"
    s := s ++ "termination_by structural node\n"
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  return (s, receipts)

def weakenOf (tyText : String) (arg : String) : String :=
  if tyText == "Effect4.Program.Term" then s!"(Effect4.Program.Term.weaken cut {arg})"
  else if tyText == "Effect4.Program.CauseTerm" then s!"(Effect4.Program.CauseTerm.weaken cut {arg})"
  else if tyText == "Option Effect4.Program.Term" then
    s!"({arg}.map (Effect4.Program.Term.weaken cut))"
  else arg

def emitFrontier (root : Name) (frontier : List Name) : MetaM (String × List String) := do
  let iv ← getConstInfoInduct root
  let _ := iv
  let mut block := []
  for fam in frontier do
    let fv ← getConstInfoInduct fam
    let label := famLabel fam
    let mut rows := []
    for c in fv.ctors do
      let ci ← getConstInfoCtor c
      let args ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
        let mut acc := []
        let mut i := 0
        for x in xs[ci.numParams:] do
          let ty ← inferType x
          let recFam := match ty.getAppFn with
            | .const n _ => if frontier.contains n then some (famLabel n) else none
            | _ => none
          acc := acc ++ [({ name := s!"a{i}", recFam, tyText := ← srcOf ty } : Arg)]
          i := i + 1
        return acc
      rows := rows ++ [({ fam := label, ctor := shortName c, field := s!"{label}_{shortName c}", args } : CtorRow)]
    block := block ++ [(label, fam, rows)]
  let labels := block.map (·.1)
  let mut s := ""
  s := s ++ "inductive EffFrontierFam where\n"
  for l in labels do s := s ++ s!"  | {l}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"

  s := s ++ "structure EffFrontierAlgebra (Op : Type) (R : EffFrontierFam → Type u) where\n"
  for (label, _, rows) in block do
    for r in rows do
      let argTexts := r.args.map fun a =>
        match a.recFam with
        | some f => s!"R .{f}"
        | none => s!"({a.tyText})"
      s := s ++ s!"  {r.field} : " ++ String.intercalate " → " (argTexts ++ [s!"R .{label}"]) ++ "\n"
  s := s ++ "\nmutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def cata_frontier_{label} \{Op : Type} \{R : EffFrontierFam → Type u} (alg : EffFrontierAlgebra Op R)\n"
    s := s ++ s!"    (node : {fam} Op) : R .{label} :=\n  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let callArgs := r.args.map fun a =>
        match a.recFam with
        | some f => s!"(cata_frontier_{f} alg {a.name})"
        | none => a.name
      s := s ++ pat ++ s!" alg.{r.field}"
      for c in callArgs do s := s ++ " " ++ c
      s := s ++ "\n"
    s := s ++ "termination_by structural node\n"
  s := s ++ "end\n\n"

  s := s ++ "def frontierSelfCarrier (Op : Type) : EffFrontierFam → Type\n"
  for (label, fam, _) in block do
    s := s ++ s!"  | .{label} => {fam} Op\n"
  s := s ++ "\n"

  s := s ++ "def weakenAlg {Op : Type} (cut : Nat) : EffFrontierAlgebra Op (frontierSelfCarrier Op) where\n"
  for (_, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      let rhsArgs := r.args.map fun a =>
        match a.recFam with
        | some _ => a.name
        | none => weakenOf a.tyText a.name
      let rhs := if rhsArgs.isEmpty then "" else " " ++ String.intercalate " " rhsArgs
      s := s ++ s!"  {r.field}{lhs} := .{r.ctor}{rhs}\n"
  s := s ++ "\nmutual\n"
  let mut receipts := []
  for (label, fam, rows) in block do
    let handName := s!"{fam}.weaken"
    s := s ++ s!"theorem weaken_eq_cata_{label} \{Op : Type} (cut : Nat) (node : {fam} Op) :\n"
    s := s ++ s!"    {handName} cut node = cata_frontier_{label} (weakenAlg cut) node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let ihs := r.args.filterMap fun a =>
        a.recFam.map fun f => s!"weaken_eq_cata_{f} cut {a.name}"
      let lemmas := String.intercalate ", "
        ([s!"{handName}", s!"cata_frontier_{label}", "weakenAlg"] ++ ihs)
      s := s ++ pat ++ s!"\n    simp only [{lemmas}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"weaken_eq_cata_{label}"]
  s := s ++ "end\n\n"
  return (s, receipts)

structure Args where
  group : String := "Fold"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  kinds : List (String × String) := []
  types : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a =>
    parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--kind" :: k :: rest, a =>
    match k.splitOn "=" with
    | [ty, kind] => if ty.isEmpty || kind.isEmpty then .error s!"--kind {k}: expected <Type>=<kind>"
      else parseArgs rest { a with kinds := a.kinds ++ [(ty, kind)] }
    | _ => .error s!"--kind {k}: expected <Type>=<kind>"
  | t :: rest, a =>
    if t.startsWith "--" then
      if rest.isEmpty then .error s!"{t} needs a value" else .error s!"unknown option {t}"
    else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) : MetaM (Array String) := do
  let mut lines : Array String := #[]
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports
    ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
    ++ String.join (args.kinds.map fun (t, k) => " --kind " ++ t ++ "=" ++ k)
  let mut cmdLines : Array String := #["--   " ++ head ++ " \\"]
  let mut cur := "--    "
  for t in args.types do
    if cur.length + t.length + 1 > 96 then
      cmdLines := cmdLines.push (cur ++ " \\")
      cur := "--    " ++ t
    else
      cur := cur ++ " " ++ t
  cmdLines := cmdLines.push cur
  lines := lines ++ #["-- GENERATED by tools/Effect4Gen/Fold.lean from the Lean environment. Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):"]
  lines := lines ++ cmdLines
  if let some p := args.append then
    let rep := p.replace "\\" "/"
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {rep}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #[
    "",
    "set_option autoImplicit false",
    "",
    "namespace Effect4.Program",
    "",
    "universe u",
    ""
  ]

  let mut allReceipts : List String := []
  for t in args.types do
    let root := t.toName
    let (blockText, blockReceipts) ← emitBlock root
    lines := lines.push blockText
    allReceipts := allReceipts ++ blockReceipts

  if args.types.contains "Effect4.Program.Eff" then
    let (frontierText, frontierReceipts) ← emitFrontier `Effect4.Program.Eff [
      `Effect4.Program.Eff, `Effect4.Program.Stmt, `Effect4.Program.Stmts,
      `Effect4.Program.Effs, `Effect4.Program.ActionTerm]
    lines := lines.push frontierText
    allReceipts := allReceipts ++ frontierReceipts

  lines := lines ++ #["/-! ## Receipts -/", ""]
  for r in allReceipts do
    lines := lines.push s!"#print axioms {r}"
  lines := lines ++ #["", "end Effect4.Program", ""]

  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")

  return lines

end Effect4Gen.Fold

open Effect4Gen.Fold in
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
    let stamp ← Tools.GeneratedStamp.line "tools/Effect4Gen/Fold.lean" args.imports
      (["tools/Effect4Gen/manifest.json"] ++ args.append.toList)
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
