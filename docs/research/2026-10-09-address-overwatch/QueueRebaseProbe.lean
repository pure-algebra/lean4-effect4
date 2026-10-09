import Effect4.Laws.Program.Typing.Rebase
import ProofGraph.Audit
import ProofGraph.Axioms
import Effect4.Author
import Effect4.Library

/-!
# Acceptance: an edit session on an authored module, through the entry modules alone

Codex's overwatch of the edit session (finding EDIT-OW-02,
`docs/research/2026-10-08-edit-session-overwatch-receipt.md`) found that the author's entry modules
did not reach the edit session. This program imports `Effect4.Author`, `Effect4.Library` and
`Effect4.Laws.Author` only. It builds a module with the Queue's definitions installed, a block at
its root, and opens an edit session on it.

* **Finite evaluations.** An edit inside the main program that keeps its focus's type splices the
  table, and the view keeps the module's type; an edit inside a body splices too.
* This review uses the authoring data and finite guards, then checks the new base laws below.
-/

set_option autoImplicit false

namespace Test.Dogfood.EditSession

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The Queue's definitions at numbers. -/
def numbers := Queue.Definitions.make "numbers" .nat

/-- The client: a queue, one offer through the installed definition, and a take. -/
def client : Module NativeOp :=
  numbers.module (eff do
    let q ← Queue.bounded .nat 2
    let _ ← numbers.offer q (nat 3)
    let x ← numbers.take q
    return x)

/-- The built client as a sketch with no hole, and its application. -/
def built : Option (Sketch × SigApp) :=
  (Api.Author.build client).toOption.map fun b => ({ program := b.program.expandRefs }, ⟨b.table, []⟩)

/-- The sketch, or the empty program where the build refuses. -/
def sketch : Sketch := (built.map (·.1)).getD { program := .succeed (.lit .unit) }

/-- The application, or the empty one where the build refuses. -/
def app : SigApp := (built.map (·.2)).getD {}

/-- The session opened on the client. -/
def opened : EditSession := EditSession.open app sketch

/-- The edit that wraps the sub-program at an address in `suspend`, which keeps its type. -/
def wrap (a : List Nat) : Option Edit :=
  match (Node.eff sketch.program).at_ a with
  | some (.eff q) => some (.fill a (.suspend q))
  | _ => none

/-- Whether an edit spliced, and whether the view keeps the opened session's type. -/
def splicesKeepingType (e : Edit) : Bool :=
  let (l', d) := opened.feed e
  (match d with
    | .spliced _ => true
    | _ => false) && l'.view.type == opened.view.type && opened.view.type.isSome

-- finite evaluation: the client builds, with a block at its root, and the session shows a type
#guard built.isSome && opened.view.type.isSome && opened.view.refusals.isEmpty
-- finite evaluation: an edit inside the main program, under `[1]`, splices and keeps the type
#guard (wrap [1, 0]).map splicesKeepingType == some true
-- finite evaluation: an edit inside the first body, under `[0, 0]`, splices and keeps the type
#guard (wrap [0, 0]).map splicesKeepingType == some true

end Test.Dogfood.EditSession

namespace AddressOverwatch
open Effect4 Effect4.Program

-- Finite controls at a real Queue definition body and at its client.
def queuePartRebases (path : List Nat) : Bool :=
  let app := Test.Dogfood.EditSession.app
  let program := Test.Dogfood.EditSession.sketch.program
  match program.partAt app.signature [] path with
  | some (part, []) =>
      let old := Annotate.check part.sig part.env [] part.program
      let moved := Annotate.check part.sig part.env [7, 3] part.program
      old.2.toOption.isSome && moved.2.toOption.isSome &&
        decide (moved.1 = old.1.map (Table.Entry.rebase [7, 3])) &&
        decide (moved.2 = old.2.mapError (TypeRefusal.rebase [7, 3]))
  | _ => false

#guard queuePartRebases [0, 0]
#guard queuePartRebases [1]

-- The structural checker law does not turn a block into a subtree.
#guard !(Checker.check Test.Dogfood.EditSession.app.signature [] []
  Test.Dogfood.EditSession.sketch.program).toOption.isSome
#guard Test.Dogfood.EditSession.opened.view.type.isSome

-- The same bytes have a different answer in a different context.
def freeRead : Eff NativeOp := .succeed (.var 0)
def emptySig : Signature NativeOp := ({} : SigApp).signature
#guard (Checker.check emptySig [.nat] [] freeRead).toOption.map (·.answer) == some .nat
#guard (Checker.check emptySig [.bool] [] freeRead).toOption.map (·.answer) == some .bool
#guard (Checker.check emptySig [] [] freeRead).toOption.isNone
#guard (Checker.check emptySig [] [7, 3] freeRead) =
  (Checker.check emptySig [] [] freeRead).mapError (TypeRefusal.rebase [7, 3])

end AddressOverwatch

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n, d) =>
    (n, d.imports.map (·.module))
  for root in #[`Effect4.Author] do
    let closure := ProofGraph.Audit.moduleImportClosure graph root
    for m in closure do
      if (`Effect4.Laws).isPrefixOf m then throwError "core entry reaches law: {root} -> {m}"
  let targetModules := #[`Effect4.Laws.Program.Address, `Effect4.Laws.Auto.ExceptMap,
    `Effect4.Laws.Program.Typing.Rebase]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if let some idx := env.getModuleIdxFor? name then
        if targetModules.contains env.header.moduleNames[idx.toNat]! then
          names := names.push name
  let (results, _) := ProofGraph.reachedAxiomsMany env names {}
  let allowed := #[`propext, `Quot.sound]
  for (name, result) in names.zip results do
    let some axioms := result | throwError "audit exhausted: {name}"
    for ax in axioms do
      unless allowed.contains ax do throwError "unexpected axiom: {name} -> {ax}"
    logInfo m!"{name}: {axioms}"
  liftIO <| IO.FS.writeFile "imported-modules.txt"
    (String.intercalate "\n" (env.header.moduleNames.toList.map (·.toString)) ++ "\n")
  logInfo m!"PASS: {names.size} theorem declarations in the three audited modules stay within [propext, Quot.sound]; Author imports no Laws module. Queue body and main tables rebase; changed contexts and the module root remain separate controls."
