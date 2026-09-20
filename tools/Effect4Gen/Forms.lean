import Lean
import Tools.GeneratedStamp
import Effect4.Codegen.Forms

/-!
# Effect4Gen.Forms — the derived forms as authoring combinators, from the form table

Reads `Codegen.Forms.all`, the admitted derived forms of the printer (each a `Template`
over argument slots, printed back by recognition), and emits:

* group `Forms` → `src/Effect4/Codegen/Authoring/Forms.lean`: one `Src NativeOp`
  combinator per form, the template read on the scope-reader carrier. A template binder an
  argument can see becomes a name parameter (`tapContinuation answer body continuation`);
  a binder no argument sees is internal. The template's own `here k` references and the
  argument's own names resolve through the one scope, so the offset-and-count weakening
  the printer's `Template.expand` performs is nothing here: the reader elaborates each
  argument at the depth of its slot. Every form carries a guard that its elaboration on
  the table's example arguments is exactly `Template.expand` of the same form, so the two
  owners of a form (this reading, the printer's expansion) cannot drift.
* group `FormsLaws` → `src/Effect4/Laws/Program/Authoring/Forms.lean`: the scope lemma of
  every combinator, `unfold` then `authoring_scoped`.

    lake env lean -M 4096 --run tools/Effect4Gen/Forms.lean --group Forms
      --imports Effect4.Program.Authoring.Lifts --out src/Effect4/Codegen/Authoring/Forms.lean
-/

open Lean Meta
open Effect4 Effect4.Program Effect4.Codegen.Forms

namespace Effect4Gen.Forms

/-- One occurrence of a slot in the template: the binder names in scope there, and how many of
them the argument sees (an effect argument at depth `d` inserted with `count` shifted binders
sees `d - count`; a term argument sees all `d`). -/
structure Occurrence where
  scope : List String
  seen : Nat

structure Emit where
  /-- Name parameters, in order of encounter: (role, parameter name). -/
  binderParams : List String := []
  effScopes : List (Nat × Occurrence) := []
  termScopes : List (Nat × Occurrence) := []
  counter : Nat := 0

/-- How many binders the arguments see at most: binders below this get name parameters. -/
partial def maxSeen : Template → Nat → Nat
  | .argument _ _ count, d => d - count
  | .succeed t, d => termSeen t d
  | .die t, d => termSeen t d
  | .bind a b, d => max (maxSeen a d) (maxSeen b (d + 1))
  | .onExit a b, d => max (maxSeen a d) (maxSeen b (d + 1))
  | .matchCause a b c, d => max (maxSeen a d) (max (maxSeen b (d + 1)) (maxSeen c (d + 1)))
  | .acquireRelease a b, d => max (maxSeen a d) (maxSeen b (d + 2))
  | .fork body _, d => maxSeen body d
  | .forkScoped body _, d => maxSeen body d
  | .forkIn body scope _, d => max (maxSeen body d) (termSeen scope d)
  | .service _, _ => 0
  | .yieldNow _, _ => 0
where termSeen : TermTemplate → Nat → Nat
  | .argument _, d => d
  | _, _ => 0

def litText : Lit → String
  | .unit => "Authoring.unit"
  | .nat n => s!"(Authoring.nat {n})"
  | .bool b => s!"(Authoring.bool {b})"
  | .str s => s!"(Authoring.str {repr s})"

def optionsText (o : Supervision.ForkOptions) : Except String String :=
  if o == defaults true then .ok "(Effect4.Codegen.Forms.defaults true)"
  else if o == defaults false then .ok "(Effect4.Codegen.Forms.defaults false)"
  else .error "a form's fork options are not `defaults`"

/-- A binder's name at depth `d` with a role: a parameter when arguments can see it, an
internal name otherwise. -/
def binderName (named : Nat) (d : Nat) (role : String) : StateM Emit String := do
  if d < named then
    let st ← get
    let base := role
    let name := if st.binderParams.contains base then s!"{base}{st.counter}" else base
    set { st with binderParams := st.binderParams ++ [name], counter := st.counter + 1 }
    return name
  else
    return s!"\"_{role}{d}\""

/-- The template on the scope reader: the text of a `Src NativeOp`. -/
partial def emitTemplate (named : Nat) (effNames termNames keyNames : List String) :
    Template → List String → StateM Emit (Except String String)
  | .argument slot _ count, ns => do
    modify fun st => { st with effScopes := st.effScopes ++ [(slot, ⟨ns, ns.length - count⟩)] }
    return .ok (effNames.getD slot s!"?e{slot}")
  | .succeed t, ns => do return (← emitTerm t ns).map fun x => s!"Authoring.succeed {x}"
  | .die t, ns => do return (← emitTerm t ns).map fun x => s!"Authoring.failCause (Authoring.Cause.die {x})"
  | .bind a b, ns => do
    let x ← binderName named ns.length "answer"
    let ta ← emitTemplate named effNames termNames keyNames a ns
    let tb ← emitTemplate named effNames termNames keyNames b (ns ++ [x])
    return do pure s!"Authoring.bind {x} ({← ta}) ({← tb})"
  | .onExit a b, ns => do
    let x ← binderName named ns.length "exit"
    let ta ← emitTemplate named effNames termNames keyNames a ns
    let tb ← emitTemplate named effNames termNames keyNames b (ns ++ [x])
    return do pure s!"Authoring.onExit {x} ({← ta}) ({← tb})"
  | .matchCause a b c, ns => do
    let v ← binderName named ns.length "value"
    let w ← binderName named ns.length "cause"
    let ta ← emitTemplate named effNames termNames keyNames a ns
    let tb ← emitTemplate named effNames termNames keyNames b (ns ++ [v])
    let tc ← emitTemplate named effNames termNames keyNames c (ns ++ [w])
    return do pure s!"Authoring.matchCause {v} {w} ({← ta}) ({← tb}) ({← tc})"
  | .acquireRelease a b, ns => do
    let r ← binderName named ns.length "resource"
    let x ← binderName named (ns.length + 1) "exit"
    let ta ← emitTemplate named effNames termNames keyNames a ns
    let tb ← emitTemplate named effNames termNames keyNames b (ns ++ [r, x])
    return do pure s!"Authoring.acquireRelease {r} {x} ({← ta}) ({← tb})"
  | .fork body o, ns => do
    let tb ← emitTemplate named effNames termNames keyNames body ns
    return do pure s!"Authoring.withFiber (Authoring.Action.fork ({← tb}) {← optionsText o})"
  | .forkScoped body o, ns => do
    let tb ← emitTemplate named effNames termNames keyNames body ns
    return do pure s!"Authoring.withFiber (Authoring.Action.forkScoped ({← tb}) {← optionsText o})"
  | .forkIn body scope o, ns => do
    let tb ← emitTemplate named effNames termNames keyNames body ns
    let ts ← emitTerm scope ns
    return do pure s!"Authoring.withFiber (Authoring.Action.forkIn ({← tb}) {← optionsText o} {← ts})"
  | .service i, _ => return .ok s!"Authoring.service {keyNames.getD i s!"?k{i}"}"
  | .yieldNow p, _ => return .ok s!"Authoring.yieldNow {p}"
where
  emitTerm : TermTemplate → List String → StateM Emit (Except String String)
    | .literal v, _ => return .ok (litText v)
    | .argument k, ns => do
      modify fun st => { st with termScopes := st.termScopes ++ [(k, ⟨ns, ns.length⟩)] }
      return .ok (termNames.getD k s!"?t{k}")
    | .here k, ns => return .ok s!"(Authoring.var {ns.getD k s!"?h{k}"})"

/-- Parameter names by argument class, in slot order. -/
def argumentNames (classes : List ArgClass) : List String × List String × List String :=
  Id.run do
    let mut effs : List String := []
    let mut terms : List String := []
    let mut keys : List String := []
    let mut termArms := 0
    for c in classes do
      match c with
      | .effect => effs := effs ++ [if effs.isEmpty then "effect" else s!"effect{effs.length}"]
      | .continuation => effs := effs ++ ["continuation"]
      | .thunk => effs := effs ++ ["thunk"]
      | .releaseOne => effs := effs ++ ["release"]
      | .handlers => effs := effs ++ ["onValue", "onCause"]
      | .literal => terms := terms ++ ["value"]
      | .term => terms := terms ++ ["scope"]
      | .termArm => terms := terms ++ [if termArms == 0 then "onValue" else "onCause"]; termArms := termArms + 1
      | .key => keys := keys ++ ["key"]
    return (effs, terms, keys)

structure Emitted where
  id : String
  wrapper : String
  lemma : String
  guard : String

def emitForm (f : Form) : Except String Emitted := do
  let (effNames, termNames, keyNames) := argumentNames f.arguments
  let named := maxSeen f.expansion 0
  let (body?, st) := (emitTemplate named effNames termNames keyNames f.expansion []).run {}
  let body ← body?
  let binderParams := st.binderParams
  let paramText := String.intercalate " " (
    binderParams.map (fun n => s!"({n} : String)") ++
    effNames.map (fun n => s!"({n} : Src NativeOp)") ++
    termNames.map (fun n => s!"({n} : TermSrc)") ++
    keyNames.map (fun n => s!"({n} : Effect4.ServiceKey)"))
  let header := if paramText.isEmpty then s!"def {f.id} : Src NativeOp :=" else s!"def {f.id} {paramText} : Src NativeOp :="
  let wrapper := s!"/-- `{f.head}` (`{f.citation}`). -/\n{header}\n  {body}\n"
  -- the lemma
  let hyps := (effNames ++ termNames).zipIdx.map fun (n, i) => s!"(h{i} : {n}.Scoped)"
  let implicits := (effNames.map (fun n => s!"\{{n} : Src NativeOp}") ++ termNames.map (fun n => s!"\{{n} : TermSrc}"))
  let lemmaParams := String.intercalate " " (
    binderParams.map (fun n => s!"({n} : String)") ++ implicits ++
    keyNames.map (fun n => s!"({n} : Effect4.ServiceKey)") ++ hyps)
  let app := String.intercalate " " ([f.id] ++ binderParams ++ effNames ++ termNames ++ keyNames)
  let lemma := s!"theorem {f.id}_scoped {lemmaParams} :\n    (({app}) : Src NativeOp).Scoped := by\n  unfold {f.id}; authoring_scoped\n"
  -- the guard: the form read on the reader, at the table's example arguments, is its expansion
  let binderArgs := binderParams.zipIdx.map fun (_, i) => s!"\"b{i}\""
  let exampleName (occ : Option (Nat × Occurrence)) : String :=
    match occ with
    | some (_, o) => match o.scope.head? with
      | some n => if n.startsWith "_" then n else s!"b{binderParams.findIdx (· == n)}"
      | none => "?"
    | none => "?"
  let effArgs := effNames.zipIdx.map fun (_, slot) =>
    let occ := st.effScopes.find? (·.1 == slot)
    let sees := (occ.map (·.2.seen)).getD 0
    if slot == 0 then "(succeed (nat 11))"
    else if sees == 0 then "(bind \"x\" (succeed (nat 22)) (succeed (var \"x\")))"
    else s!"(succeed (var {repr (exampleName occ)}))"
  let termArgs := termNames.zipIdx.map fun (_, k) =>
    let occ := st.termScopes.find? (·.1 == k)
    if f.arguments.contains .termArm then s!"(var {repr (exampleName occ)})"
    else if k == 0 then "(nat 7)" else "(nat 8)"
  let keyArgs := keyNames.map fun _ => "⟨⟨4⟩, ⟨4⟩⟩"
  let guardApp := String.intercalate " " ([f.id] ++ binderArgs ++ effArgs ++ termArgs ++ keyArgs)
  let guard := s!"#guard (elaborate ({guardApp})).toOption =\n  (Effect4.Codegen.Forms.all.find? (·.id == {repr f.id})).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)"
  return { id := f.id, wrapper, lemma, guard }

structure Args where
  group : String := "Forms"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a => parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--" :: rest, a => parseArgs rest a
  | t :: rest, a => if t.startsWith "--" then .error s!"unknown option {t}" else parseArgs rest a

def run (args : Args) : IO (Array String) := do
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Forms.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
  let mut lines : Array String := #[
    "-- GENERATED by tools/Effect4Gen/Forms.lean from Codegen.Forms.all. Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):",
    "--   " ++ head]
  if let some p := args.append then
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {p.replace "\\" "/"}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #["", "set_option autoImplicit false", "", "namespace Effect4.Program.Authoring.Forms", "", "open Effect4.Program Effect4.Program.Authoring", ""]
  let mut emitted : List Emitted := []
  for f in Effect4.Codegen.Forms.all do
    match emitForm f with
    | .ok e => emitted := emitted ++ [e]
    | .error msg => throw (IO.userError s!"form {f.id}: {msg}")
  match args.group with
  | "Forms" =>
    for e in emitted do lines := lines.push e.wrapper
    lines := lines ++ #["/-! ## Each form read on the reader is its printed expansion -/", ""]
    for e in emitted do lines := lines.push (e.guard ++ "\n")
  | "FormsLaws" =>
    for e in emitted do lines := lines.push e.lemma
  | g => throw (IO.userError s!"unknown group {g}: Forms or FormsLaws")
  lines := lines ++ #["/-! ## Receipts -/", ""]
  for e in emitted do
    lines := lines.push s!"#print axioms Effect4.Program.Authoring.Forms.{e.id}{if args.group == "FormsLaws" then "_scoped" else ""}"
  lines := lines ++ #["", "end Effect4.Program.Authoring.Forms", ""]
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
  return lines

end Effect4Gen.Forms

open Effect4Gen.Forms in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  let lines ← run args
  let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/Forms.lean"
  let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
  match args.out with
  | some p => IO.FS.writeFile p text
  | none => IO.println text
