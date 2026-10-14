import Test.Dogfood.Scenario.Todo.Tree
import Test.Dogfood.ApplicationDefs
import Effect4.Program.Authoring.ApplicationService
import Effect4.Laws.Library.Ref.Cache

/-!
# The to-do with the banked Ref cache imposed on its service

Decisions row 378 (8), (4) and (23). The to-do's service holds the banked cache
(`Test.Dogfood.Scenario.Todo.listCache`; `Application.Imposed`,
`src/Effect4/Program/Authoring/Application.lean`): the cell is the service's state beside the
context, made once by the cache's `make`. The method `list` reads through the cache with the entry
`list`, `TodoRepo.all()`, as its loader, and `add`, `complete` and `remove` invalidate the cell after
their program succeeds. The entries do not change, so neither do their modules and the five proved
clauses of `serves` (`Test/Dogfood/Scenario/Todo/Claims.lean`).

* **The pin** (row 378 (4)). The built service's first three definitions, as a block, have the
  bank's recorded digest (`refCache`, `Test/Dogfood/Bank.lean`).
* **The restated claim** (`cached_list_after_add`). After `add` and its invalidation, `get` with
  the to-do's loader answers what the repository holds, the new to-do included, whatever the
  cache held. It is the original clause `list_after_add` read through the cache, carried by the
  cache's law `invalidate_get` (`src/Effect4/Laws/Library/Ref/Cache.lean`, the registry claim
  `ref-cache-invalidated-reads-through`). It holds at the call tree's meaning under the reference
  model, of the code that the service runs: `add`'s program, the cache's `invalidate`, and `get`'s
  body with its loader read as the row of `all`.
* **The runs** (tested). On the Lean machine, a consumer of the built service lists, adds and
  lists again. With the invalidation the second list holds the new to-do; without it the second
  list is stale (the control of row 378 (23)).

* **The emitted file** (HO-5, decisions rows 340 and 378 (8), (23)). The service module emits as a
  file (`ModuleEmission.file`) declaring both `ListCache` and `TodoApp`, with their imports and no
  free names.

What it does not establish. That a run of the service observes that meaning: the service's `list`
invokes `get` by `Eff.invoke`, which no meaning reads (HO-2's `invoke-unfolds`, row 378 (23)), and
its methods run under `provideContext`, outside the row fragment. The runs are finite probes. The
emitted file does not read back yet: `Classes.readNamed` refuses `Ref.Ref<…>` under the frozen
contract (`Test/contracts/faces.contract.md`, §B19), so `readDefHead` refuses the cache's
declarations (`shape "definition"`).
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
  addAt add_tree listAt)
open Test.Dogfood.Bank (refCache milk observe)
open Test.Dogfood.ApplicationDefs (prefixBlock)

/-- The to-do with the banked cache imposed on its service. -/
def cached : Application NativeOp := { application with imposed := [listCache] }

/-- The service's name. -/
def service : String := "TodoApp"

/-- An application's service module, built. -/
def built? (app : Application NativeOp) : Option Api.Built :=
  (app.serviceModule service).toOption.bind fun m => (Api.Author.build m).toOption

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

/-- **`add` under the model, at any stores**: it stores the to-do under the next id and answers
it, and it leaves the stores. A step of `cached_list_after_add`, as `add_on_model` (at the empty
stores) is of `list_after_add`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem add_on_model_at (title : String) (hne : title ≠ "") (st : Repo) (s : Stores) :
    hostRun modelHost (addAt title) [] s st =
      some (.success (todo st.1 title false), (s, (st.1 + 1, st.2 ++ [(st.1, title, false)]))) := by
  unfold hostRun
  rw [add_tree title hne]
  kernel_rfl

/-- The proposition of `cached_list_after_add`. -/
def CachedListAfterAdd : Prop :=
  ∀ (title : String) (start : Repo) (c : Option Val) (q : RefKey) (s : Stores), title ≠ "" →
    refPeek s.refs q = some ((Image.option Image.ident).toVal c) →
    ((hostRun modelHost (addAt title) [] s start).bind fun r =>
      (hostRun modelHost invalidateBody [Val.cell q] r.2.1 r.2.2).bind fun r' =>
        hostRun modelHost (paramsAsRows 1 getBody) [Val.cell q] r'.2.1 r'.2.2).map (·.1) =
      some (.success (.list ((start.2 ++ [(start.1, title, false)]).map todoOf)))

/-- **After `add`, `list` through the cache holds the new to-do**, under the reference model, from
any cache content. At a title that is not empty, `add` stores the to-do, the cache's `invalidate`
empties the cell, and `get` with the to-do's loader, the row `all`, answers the stored to-dos,
the new one among them. It is `list_after_add` (`Test/Dogfood/Scenario/Todo/Claims.lean`) read
through the imposed cache.

Placement: concept `translation-simulation`; property: a composed module's law (R10), the claim
of an application carried to the imposed module's code by the module's agreement (row 378 (2)).
Question: the registry claim `ref-cache-invalidated-reads-through`, of which this is the first
reader; the to-do's modules load under no root of the registry (row 336 (9)). Reach: every title
but the empty one, every start state of the model, every cached value and cell, at the call tree's
meaning under the model. Does not establish: that a run of the service observes this meaning
(HO-2's `invoke-unfolds` and the service's context, row 378 (23)); anything of a host that
disagrees with the model. Unlocks: the slice's claim of the imposed to-do (row 378 (8)).

Proof: `add_on_model_at`, then the cache's `invalidate_get`, then the model's answer at `all`, by
computation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cached_list_after_add : CachedListAfterAdd := by
  intro title start c q s hne held
  rw [add_on_model_at title hne start s, Option.bind_some]
  dsimp only
  rw [invalidate_get modelHost Image.ident (n := 1) (by decide) c _ held]
  kernel_rfl

/-! ## The runs -/

/-- A consumer of the service: it makes the state once, lists, adds "tea" and lists again, and
answers the two lists. -/
def listAddList : Src NativeOp :=
  bindWith (Def.invoke "TodoAppContext" []) fun st =>
    bindWith (Def.invoke "TodoApp_list" [st]) fun first =>
      bindWith (Def.invoke "TodoApp_add" [st, str "tea"]) fun _ =>
        bindWith (Def.invoke "TodoApp_list" [st]) fun second =>
          succeed (app "pair" [first, second])

/-- The consumer, over an application's service module, elaborated. -/
def consumerOf (app : Application NativeOp) : Option NativeEff :=
  (app.serviceModule service).toOption.bind fun m =>
    (elaborateModule { m with main := listAddList }).toOption

/-- The stored to-do and the new one, as the repository lists them. -/
def both : Val := Val.list [todo 1 "milk" false, todo 2 "tea" false]

/-- The service with the cache, whose writes do not invalidate it. -/
def forgetting : Application NativeOp :=
  { application with imposed := [{ listCache with around := [("list", readingThrough)] }] }

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
-- control: `Classes.readNamed` refuses `Ref.Ref<…>` under the frozen contract
-- (`Test/contracts/faces.contract.md`, §B19), so the file and envelope readers refuse the cache's
-- definition headers as `shape "definition"`
#guard (emitted? cached).map (fun (_, table, envelope, file) =>
  (Api.readFile file table matches .error (.shape "definition")) &&
    (Api.readModule envelope table matches .error (.shape "definition"))) = some true

end Test.Dogfood.Scenario.Todo.Cached
