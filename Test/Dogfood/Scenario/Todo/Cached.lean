import Test.Dogfood.Scenario.Todo.Entries
import Test.Dogfood.Scenario.Todo.CachedProgram
import Test.Dogfood.ApplicationDefs
import Effect4.Program.Authoring.ApplicationService
import Effect4.Laws.Library.Ref.Cache
import Effect4.Laws.Program.FragmentBlock
import Effect4.Emit

/-!
# The to-do with the banked Ref cache imposed on its service

Decisions row 378 (8), (4) and (23). The to-do's service holds the banked cache
(`Test.Dogfood.Scenario.Todo.listCache`; `Application.Imposed`,
`src/Effect4/Program/Authoring/Application.lean`): the cell is the service's state beside the
context, made once by the cache's `make`. The method `list` reads through the cache with the entry
`list`, `TodoRepo.all()`, as its loader, and `add`, `complete` and `remove` invalidate the cell after
their program succeeds. The entries do not change, so neither do their modules.

* **The pin** (row 378 (4)). The built service's first three definitions, as a block, have the
  bank's recorded digest (`refCache`, `Test/Dogfood/Bank.lean`).
* **The restated claim** (`cached_list_after_add`). Over the built service `built? cached`, calling
  `TodoApp_add` and then `TodoApp_list` (`addThenList`) at the block's row meaning under the
  reference model (`hostRunBlockB`, `src/Effect4/Laws/Program/BlockMeaning.lean`) answers what the
  repository holds, the new to-do included, whatever the cache held. `TodoApp_add` runs `add` under
  `provideContext` and calls `listCacheInvalidate`; `TodoApp_list` invokes `listCacheGet`
  (`Eff.invoke`) with `list` under `provideContext` as its loader. It is the original clause
  `list_after_add` proved of the built service's own definitions through `denoteBlockB` and the
  cache's law `invalidate_get` (`src/Effect4/Laws/Library/Ref/Cache.lean`, the registry claim
  `ref-cache-invalidated-reads-through`).
* **The runs** (tested). On the Lean machine, a consumer of the built service lists, adds and
  lists again. With the invalidation the second list holds the new to-do; without it the second
  list is stale (the control of row 378 (23)).

* **The emitted file** (HO-5, decisions rows 340 and 378 (8), (23)). The service module emits as a
  file (`ModuleEmission.file`) declaring both `ListCache` and `TodoApp`, with their imports and no
  free names, and both the file and the envelope read back to the built program (`Api.readFile`,
  `Api.readModule`).

The consumer builder serves the recorded-request checker through `H9Blocks` and the block
validated claims. Their fragment and tree-level premises remain separate from runtime checks.
The runs below remain finite probes. They establish no layer-build, persistent-session or
outside-host agreement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Todo.Cached

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Denote
open Effect4.Store (Image)
open Effect4.Run (reactorHost)
open Effect4.Ref.Cache (invalidateBody getBody invalidate_get)
open Test.Dogfood.Scenario.Todo (application listCache readingThrough repository Repo todo todoOf
  addAt listAt)
open Test.Dogfood.Bank (refCache milk observe)
open Test.Dogfood.ApplicationDefs (prefixBlock)

-- control: an unknown method has no consumer.
#guard (consumerBuiltAt "missing" []).isNone
-- finite admission: each method's representative consumer belongs to the block fragment.
#guard (consumerBuiltAt "list" []).map (fun b => BlockRows b.table b.program) = some true
#guard (consumerBuiltAt "add" [str "tea"]).map (fun b => BlockRows b.table b.program) = some true
#guard (consumerBuiltAt "complete" [nat 1]).map (fun b => BlockRows b.table b.program) = some true
#guard (consumerBuiltAt "remove" [nat 1]).map (fun b => BlockRows b.table b.program) = some true

/-! ## The service and the pin -/

-- finite evaluation (row 378 (4)): the built service holds the bank's block first, byte for byte,
-- so it pins the bank's recorded digest
#guard ((built? cached).bind fun b => prefixBlock 3 b.program).map
    (fun p => (Store.Canonical.digest p).hex) = some refCache.digest
-- finite evaluation: the cache's three definitions, then the service's initial program and its
-- four methods
#guard (built? cached).map (fun b => b.program.defsOf.map (·.name)) =
  some ["listCacheMake", "listCacheGet", "listCacheInvalidate", "TodoAppContext", "TodoApp_add",
    "TodoApp_list", "TodoApp_complete", "TodoApp_remove"]
-- finite evaluation: the state is the context beside the cache's cell, and each method declares
-- its entry's open type, as without the cache
#guard cached.stateTy =
  .prod (.contextOf cached.contextKeys) (Effect4.Ref.Cache.cellTy Test.Dogfood.Scenario.Todo.Todo.ty)
#guard (built? cached).map (fun b => (b.program.defsOf.drop 4).map fun d => (d.answer, d.error)) =
  (built? application).map (fun b => (b.program.defsOf.drop 1).map fun d => (d.answer, d.error))
-- control: with nothing imposed the service is E1's: no kept block, the context alone
#guard (built? application).map (fun b => b.program.defsOf.length) = some 5 &&
  application.stateTy == .contextOf application.contextKeys
-- finite evaluation: the loader that `list` passes is the entry's program, one call of the row
-- `all` at position 1, which `get`'s body reads as that row in the claim below
#guard listAt = .perform (.external 1) (.lit .unit)

/-! ## The restated claim -/

/-- The reference model as a host. -/
abbrev modelHost : Effects.Comodel (RowSig application.table) Repo :=
  reactorHost application.table repository

/-- The consumer that invokes `TodoApp_add` at `(state, title)` and then `TodoApp_list` at `state`,
over the service's definition block (definitions 4 and 5). -/
def addThenList : NativeEff :=
  .bind (.perform (.call 4) (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))
    (.perform (.call 5) (.var 0))

/-- The elaborated bodies of the cached service module. -/
def cachedBodies : List NativeEff :=
  match (cached.serviceModule service).toOption.bind (fun m => (elaborateModule m).toOption) with
  | some p => bodiesOf p
  | none => []

/-! ## The runs -/

/-- A consumer of the service: it makes the state once, lists, adds "tea" and lists again, and
answers the two lists. -/
def listAddList : Src NativeOp :=
  bindWith (Def.invoke "TodoAppContext" []) fun st =>
    bindWith (Def.invoke "TodoApp_list" [st]) fun first =>
      bindWith (Def.invoke "TodoApp_add" [st, str "tea"]) fun _ =>
        bindWith (Def.invoke "TodoApp_list" [st]) fun second =>
          succeed (app "pair" [first, second])

/-- The shipped cache composite: one fresh service state, two lists, an add, and another list.
The result retains the first list, the cache hit, the new item and the refreshed list. -/
def listListAddList : Src NativeOp :=
  bindWith (Def.invoke "TodoAppContext" []) fun st =>
    bindWith (Def.invoke "TodoApp_list" [st]) fun first =>
      bindWith (Def.invoke "TodoApp_list" [st]) fun hit =>
        bindWith (Def.invoke "TodoApp_add" [st, str "tea"]) fun item =>
          bindWith (Def.invoke "TodoApp_list" [st]) fun after =>
            succeed (app "tuple" [first, hit, item, after])

/-- One finite named script for the keyed service gate, driven from the stocked reference model.
A failed build remains absent, so the gate must refuse it rather than omit the case. -/
def cachedListAfterAddRun : Option Test.Dogfood.Scenario.NamedRun :=
  (buildConsumer listListAddList).map fun b =>
    { name := "cached-list-after-add"
      opened := Run.open b application.name
      moves := (Run.runWith b repository (2, [(1, "milk", false)]) application.name).1.journal.map .wire }

/-- The consumer, over an application's service module, elaborated. -/
def consumerOf (app : Application NativeOp) : Option NativeEff :=
  (app.serviceModule service).toOption.bind fun m =>
    (elaborateModule { m with main := listAddList }).toOption

/-- The stored to-do and the new one, as the repository lists them. -/
def both : Val := Val.list [todo 1 "milk" false, todo 2 "tea" false]

-- finite admission: the composite reaches the fragment of `H9Blocks`.
#guard cachedListAfterAddRun.map (fun run => BlockRows run.opened.built.table run.opened.built.program) =
  some true
-- finite observation: the repeated list hits the cache; the write makes the last list read again.
#guard cachedListAfterAddRun.map (fun run =>
  (Test.Dogfood.Scenario.applications run.played).map (·.row)) =
    some ["TodoRepo.all", "TodoRepo.insert", "TodoRepo.all"]
#guard cachedListAfterAddRun.map (fun run => run.played.exit) =
  some (some (Exit.success (Val.list [milk, milk, todo 2 "tea" false, both])))
-- finite observation: replay starts without a cache cell and allocates its own single cell.
#guard cachedListAfterAddRun.map (fun run =>
  (run.opened.machine.state.refs.length, run.played.machine.state.refs.length)) = some (0, 1)

/-- The service with the cache, whose writes do not invalidate it. -/
def forgetting : Application NativeOp :=
  { application with imposed := [{ listCache with around := [("list", readingThrough)] }] }

-- control: at the block meaning `hostRunBlockB`, when `TodoApp_add` omits invalidation (`forgetting`)
-- and the cache holds `milk`, `addThenList` answers the stale `milk` instead of `both`
#guard ((built? forgetting).bind fun b =>
  (hostRunBlockB modelHost (bodiesOf b.program) 2 [] addThenList
      emptyCtx
    [Val.list [Val.context { services := .empty, maxOpsBeforeYield := 0, preventYield := false },
      Val.cell ⟨0⟩], .str "tea"]
    { Stores.empty with refs := [Store.Val.some milk] }
    (2, [(1, "milk", false)])).map (·.1)) = some (some (Exit.success milk))

-- tested: under the reference model, from one stored to-do, the first list holds it, and after
-- `add` the second list holds both: the invalidation empties the cache, so the second read asks
-- the repository again (three answers: `all`, `insert`, `all`)
#guard (consumerOf cached).bind observe == some (some (Exit.success (Val.list [milk, both])), 3)
-- control (row 378 (23)): writes that do not invalidate leave the second list stale, answered from
-- the cache without the new to-do, which the repository holds (two answers)
#guard (consumerOf forgetting).bind observe == some (some (Exit.success (Val.list [milk, milk])), 2)

/-! ## The emitted file -/

/-- The built program, its table, its envelope and its file (the prelude at `./prelude.ts`). -/
def emitted? (app : Application NativeOp) :
    Option (Api.Program × RowTable × TypeScript.Module × TypeScript.Module) :=
  (built? app).bind fun b => (Api.emitModule "main" b.program b.table).toOption.bind fun e =>
    (e.file "./prelude.ts").toOption.map fun f => (b.program, b.table, e.module, f)

-- finite evaluation: the file declares the payload class `NotFound`, the row service `TodoRepo`,
-- the eight definitions, the two block services `ListCache` and `TodoApp` with their layers, and
-- `main`, with no free name
#guard (emitted? cached).map (fun (_, _, _, file) => (file.decls.drop 1).map fun
  | .const c => c.name
  | _ => "") =
  some ["TodoRepoKey", "TodoRepo", "listCacheMake", "listCacheGet", "listCacheInvalidate",
    "TodoAppContext", "TodoApp_add", "TodoApp_list", "TodoApp_complete", "TodoApp_remove",
    "ListCache", "ListCacheLayer", "TodoApp", "TodoAppLayer", "main"]
#guard (emitted? cached).map (fun (_, _, _, file) => Effect4.Codegen.freeNames file) = some []
-- reader: `Ref.Ref<A>` reads in definition headers (`Signature.typeEnv`), and `Todo.ty` is
-- normalized when declared (`eff_record`), so every definition header of `cached` is in
-- `DefDecl.readable` and both the emitted file and the envelope read back to the built program
-- (decisions row 378 (8))
#guard (emitted? cached).map (fun (program, table, _, _) =>
  program.defsOf.all (DefDecl.readable ((nativeSignature table).typeEnv (classesOf program)))) =
  some true
#guard (emitted? cached).map (fun (program, table, envelope, file) =>
  decide (Api.readFile file table = .ok program) &&
    decide (Api.readModule envelope table = .ok program)) = some true

end Test.Dogfood.Scenario.Todo.Cached

