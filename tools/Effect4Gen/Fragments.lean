import Effect4Gen.LayerView

/-!
# Fragment classifiers from one constructor classification

The generator reads the existing program family metadata. The table below owns each
constructor's fragment rule. Missing, duplicate, and obsolete classifications refuse generation.
The emitted predicates retain direct recursive equations and early rejection.
Their existing `fold_of` consumers establish their connections to the program algebra.
-/

open Lean Meta

namespace Effect4Gen.Fragments

open LayerView (Ctor Args)

inductive Rule where
  | accept | children | operation | loop | conditional | reject
  deriving BEq, Repr

/-- Each constructor receives an explicit rule (decisions row 35). -/
def rules : List (String × Rule) :=
  [("succeed", .accept), ("fail", .accept), ("failCause", .accept), ("sync", .accept),
   ("suspend", .children), ("perform", .operation), ("bind", .children), ("gen", .reject),
   ("catchCause", .children), ("matchCause", .children), ("onExit", .children),
   ("exit", .children), ("uninterruptible", .reject), ("interruptible", .reject),
   ("yieldNow", .reject), ("awaitFiber", .reject), ("withFiber", .reject), ("scoped", .reject),
   ("acquireRelease", .reject), ("provideLayer", .reject), ("service", .reject),
   ("provideService", .reject), ("catchIf", .conditional), ("select", .children),
   ("iterate", .loop), ("restore", .reject), ("defs", .reject)]

/-- Classification covers exactly the declaration's constructors. Recursive rules visit only
program children. An operation rule requires the operation and request fields. -/
def validate (table : List (String × Rule)) (ctors : List Ctor) : Except String Unit := do
  let names := table.map Prod.fst
  if names.eraseDups.length != names.length then
    throw "Fragments: duplicate constructor classification"
  for name in names do
    unless ctors.any (·.short == name) do
      throw s!"Fragments: obsolete constructor classification {name}"
  for c in ctors do
    let some rule := table.lookup c.short
      | throw s!"Fragments: missing constructor classification {c.short}"
    let children := c.args.filter (·.recFam.isSome)
    match rule with
    | .accept =>
      unless children.isEmpty do
        throw s!"Fragments: accepted leaf {c.short} has recursive children"
    | .children | .loop | .conditional =>
      unless !children.isEmpty && children.all (·.recFam == some "eff") do
        throw s!"Fragments: {c.short} requires direct program children"
    | .operation =>
      unless c.args.map (·.sort) == ["op", "term"] do
        throw s!"Fragments: {c.short} requires an operation and request"
    | .reject => pure ()

/-! Controls for the generator's refusal boundary. They run whenever the generator builds. -/

private def leafControl : Ctor :=
  { fam := "eff", famName := `Effect4.Program.Eff, short := "leaf", field := "eff_leaf", args := [] }

private def childControl : LayerView.Arg :=
  { name := "body", recFam := some "eff", sort := "child", tyText := "Effect4.Program.Eff Op" }

#guard (validate [("leaf", .accept)] [leafControl]).isOk
#guard !(validate [] [leafControl]).isOk
#guard !(validate [("leaf", .accept), ("leaf", .reject)] [leafControl]).isOk
#guard !(validate [("obsolete", .reject)] [leafControl]).isOk
#guard !(validate [("leaf", .accept)] [leafControl, { leafControl with short := "newForm" }]).isOk
#guard !(validate [("leaf", .accept)] [{ leafControl with args := [childControl] }]).isOk
#guard (validate [("leaf", .children)] [{ leafControl with args := [childControl] }]).isOk
#guard !(validate [("leaf", .children)]
  [{ leafControl with args := [{ childControl with recFam := some "stmt" }] }]).isOk
#guard !(validate [("leaf", .operation)] [leafControl]).isOk

inductive Profile where
  | straight | looped | rows | loopedRows
  deriving BEq

def Profile.name : Profile → String
  | .straight => "Straight"
  | .looped => "Looped"
  | .rows => "StraightRows"
  | .loopedRows => "LoopedRows"

/-- A loop rule visits its body. -/
def Profile.loops : Profile → Bool
  | .looped | .loopedRows => true
  | .straight | .rows => false

/-- A conditional rule visits its children. -/
def Profile.conditionals : Profile → Bool
  | .rows | .loopedRows => true
  | .straight | .looped => false

/-- The pattern variable and the admission of a host row's call, for a profile that admits one:
`StraightRows` admits a data row of its table (`dataRow`), and `LoopedRows` admits every row,
since the machine half of H8 reads no row (`Agreement/Hosted.lean`). -/
def Profile.hostCall : Profile → Option (String × String)
  | .rows => some ("i", "dataRow table i")
  | .loopedRows => some ("_", "true")
  | .straight | .looped => none

/-- Operation-kind admission has one template, including the row-aware specialization. -/
def syncOperation (op : String) : String :=
  s!"match {op}.kind with\n    | .sync => true\n    | _ => false"

def emitPredicate (profile : Profile) (ctors : List Ctor) : Except String String := do
  validate rules ctors
  let name := profile.name
  let fixed := if profile == .rows then " table" else ""
  let params := if profile == .rows then " (table : RowTable)" else ""
  let mut out := s!"/-- The {name} fragment. Constructor classification comes from the shared generator table. -/\ndef {name}{params} : NativeEff → Bool\n"
  for c in ctors do
    let some rule := rules.lookup c.short
      | throw s!"Fragments: missing constructor classification {c.short}"
    let descends := rule == .children || (rule == .loop && profile.loops) ||
      (rule == .conditional && profile.conditionals)
    let used := c.args.filter fun a =>
      (descends && a.recFam == some "eff") || (rule == .operation && a.sort == "op")
    let pattern := String.intercalate " " (c.args.map fun a =>
      if used.any (·.name == a.name) then a.name else "_")
    let rhs ← if descends then
        pure (String.intercalate " && " (used.map fun a => s!"{name}{fixed} {a.name}"))
      else if rule == .accept then pure "true"
      else if rule == .operation then
        match used with
        | [op] =>
          match profile.hostCall with
          | some (var, admit) =>
            pure (s!"\n    match {op.name} with\n    | .external {var} => {admit}\n    | _ => " ++
              (syncOperation op.name).replace "\n    " "\n      ")
          | none => pure ("\n    " ++ syncOperation op.name)
        | _ => throw s!"Fragments: {c.short} has no unique operation field"
      else pure "false"
    let separator := if rhs.startsWith "\n" then "" else " "
    out := out ++ s!"  | .{c.short} {pattern} =>{separator}{rhs}\n"
  return out

def run (args : Args) : MetaM String := do
  unless args.types == ["Effect4.Program.Eff"] do
    throwError "Fragments: expected the Effect4.Program.Eff family"
  let profiles ← match args.group with
    | "Fragments" => pure [Profile.straight]
    | "FragmentLooped" => pure [Profile.looped]
    | "FragmentRows" => pure [Profile.rows]
    | "FragmentLoopedRows" => pure [Profile.loopedRows]
    | other => throwError "Fragments: unknown group {other}"
  let (_, block) ← LayerView.readBlock `Effect4.Program.Eff
  let ctors := block.filter (·.fam == "eff")
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let command := "lake exe effect4gen Fragments --group " ++ args.group ++
    Tools.GeneratedStamp.moduleFlags args.moduleHeader args.metaImports ++
    " --imports " ++ String.intercalate "," args.imports ++ " --out " ++ outPath ++
    (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "") ++
    " Effect4.Program.Eff"
  let mut out := "-- " ++ Tools.GeneratedStamp.note "tools/Effect4Gen/Fragments.lean" ++ "\n" ++
    "-- GENERATED from the program family and the shared fragment rules. Do not edit.\n" ++
    "-- Regenerate: " ++ command ++ "\n" ++
    String.join (args.imports.map fun name => s!"import {name}\n") ++
    "\nset_option autoImplicit false\n\nnamespace Effect4.Program.Denote\n\n" ++
    "open Effect4 Effect4.Machine Effect4.Program\n\n"
  for profile in profiles do
    match emitPredicate profile ctors with
    | .ok text => out := out ++ text ++ "\n"
    | .error reason => throwError reason
  out := out ++ "end Effect4.Program.Denote\n"
  if let some path := args.append then out := out ++ "\n" ++ (← IO.FS.readFile path)
  let text := Tools.GeneratedStamp.endWithOneNewline out
  return if args.moduleHeader then Tools.GeneratedStamp.moduleText args.metaImports text else text

/-- The existing derived-code driver owns invocation, ordering, installation, and drift checks. -/
def cli (argv : List String) : IO Unit := do
  let args ← match LayerView.parseArgs argv {} with
    | .ok args => pure args
    | .error reason => throw (IO.userError reason)
  if args.imports.isEmpty then throw (IO.userError "Fragments: --imports is required")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun name => { module := name.toName }).toArray {} 0
  let action : MetaM Unit := do
    let text ← run args
    match args.out with
    | some path => IO.FS.writeFile path text
    | none => IO.println text
  let _ ← (action.run' {}).toIO { fileName := "<fragments>", fileMap := default } { env }

end Effect4Gen.Fragments
