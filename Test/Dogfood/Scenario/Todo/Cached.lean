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

What it does not establish. Machine replay agreement for `denoteBlockB`
(PROC-6, row 378 (23)): the machine runs are finite probes.
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
      some (Exit.success (todo st.1 title false), (s, (st.1 + 1, st.2 ++ [(st.1, title, false)]))) := by
  unfold hostRun
  rw [add_tree title hne]
  kernel_rfl

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

/-- A built cached service module has `cachedBodies` as its definition bodies
(`Api.Author.build_retains`). A step of `cached_list_after_add`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem built_cached_bodies {b : Api.Built} (h : built? cached = some b) :
    bodiesOf b.program = cachedBodies := by
  unfold built? at h
  cases hm : (cached.serviceModule service).toOption with
  | none =>
    rw [hm] at h
    cases h
  | some m =>
    rw [hm, Option.bind_some] at h
    cases hb : Api.Author.build m with
    | error _ =>
      rw [hb] at h
      cases h
    | ok b' =>
      rw [hb] at h
      cases h
      obtain ⟨hprog, -, -⟩ := Api.Author.build_retains hb
      unfold cachedBodies
      rw [hm, Option.bind_some, hprog]
      rfl

/-- Calling `TodoApp_add` (definition 4 of `cachedBodies`) at `(state, title)` unfolds to `addAt
title`, then `listCacheInvalidate` (`invalidateBody`) at the cache's cell, and answers the new
to-do. A step of `cached_list_after_add`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBlockB_call_add (title : String) (ctx outerCtx : Ctx) (q : RefKey) :
    denoteBlockB application.table cachedBodies 2 []
      (.perform (.call 4) (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))
      outerCtx [Val.list [Val.context ctx, Val.cell q], .str title] =
    some <$> (denoteRows application.table (addAt title) []).bind
      (seqRows fun v =>
        (denoteRows application.table invalidateBody [Val.cell q]).bind
          (seqRows fun _ => pure (Exit.success v))) := by
  have h1 :
      denoteBlockB application.table cachedBodies 2 []
        (.perform (.call 4) (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))
        outerCtx [Val.list [Val.context ctx, Val.cell q], .str title] =
      thenOpt (match Val.context? (Val.context ctx) with
        | some supplied => denoteBlockB application.table cachedBodies 1 [] (addAt title)
            (provided (.provide supplied.services) outerCtx) []
        | none => pure (some badShapeExit)) fun ex => match ex with
          | Exit.success v => thenOpt
              (denoteBlockB application.table cachedBodies 0 [] invalidateBody outerCtx [Val.cell q])
              (fun next => match next with
                | Exit.success _ => pure (some (Exit.success v))
                | Exit.failure cause => pure (some (Exit.failure cause)))
          | Exit.failure cause => pure (some (Exit.failure cause)) := by
    kernel_rfl
  rw [h1, Val.context?_context ctx]
  dsimp only
  rw [denoteBlockB_loopedDataRows application.table cachedBodies 1 [] (addAt title) _ [] (by kernel_rfl)]
  rw [denoteRowsB_straight application.table 1 (addAt title) [] (by kernel_rfl)]
  rw [denoteBlockB_loopedDataRows application.table cachedBodies 0 [] invalidateBody outerCtx [Val.cell q] (by kernel_rfl)]
  rw [denoteRowsB_straight application.table 0 invalidateBody [Val.cell q] (by kernel_rfl)]
  rw [thenOpt_map_some, map_programBind]
  congr 1
  funext ex
  cases ex with
  | failure cause => rfl
  | success v =>
    dsimp only [seqRows]
    rw [thenOpt_map_some, map_programBind]
    congr 1
    funext next
    cases next <;> rfl

/-- Calling the built service's list unfolds the imposed cache under the current context.
Placement: translation-simulation, ref-cache-invalidated-reads-through/R10;
consumer: `cached_list_after_add`. This is a tree equation, not machine agreement. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBlockB_call_list (ctx outerCtx : Ctx) (q : RefKey) (title : String) (v : Val) :
    denoteBlockB application.table cachedBodies 2 []
      (.perform (.call 5) (.var 0)) outerCtx
      ([Val.list [Val.context ctx, Val.cell q], .str title] ++ [v]) =
    some <$> denoteRows application.table (paramsAsRows 1 getBody) [Val.cell q] := by
  have h1 :
      denoteBlockB application.table cachedBodies 2 []
        (.perform (.call 5) (.var 0)) outerCtx
        ([Val.list [Val.context ctx, Val.cell q], .str title] ++ [v]) =
      denoteBlockB application.table cachedBodies 0
        [fun _ _ =>
          match Val.context? (Val.context ctx) with
          | some _ => some <$> denoteRows application.table (.perform (.external 1) (.lit .unit)) []
          | none => pure (some badShapeExit)]
        getBody outerCtx [Val.cell q] := by
    kernel_rfl
  rw [h1, Val.context?_context ctx]
  exact Effect4.Ref.Cache.denoteBlockB_getBody application.table cachedBodies 0 1 _ [Val.cell q] outerCtx rfl

/-- The proposition of `cached_list_after_add`: over the built service `built? cached`, calling
`TodoApp_add` and then `TodoApp_list` (`addThenList`) under the reference model answers the stored
to-dos with the new one appended, from any cache content. -/
def CachedListAfterAdd : Prop :=
  ∀ (b : Api.Built) (title : String) (start : Repo) (ctx outerCtx : Ctx) (c : Option Val)
    (q : RefKey) (s : Stores),
    built? cached = some b → title ≠ "" →
    refPeek s.refs q = some ((Image.option Image.ident).toVal c) →
    (hostRunBlockB modelHost (bodiesOf b.program) 2 [] addThenList
      outerCtx
      [Val.list [Val.context ctx, Val.cell q], .str title] s start).map (·.1) =
      some (some (Exit.success (.list ((start.2 ++ [(start.1, title, false)]).map todoOf))))

/-- **After `TodoApp_add`, `TodoApp_list` through the imposed cache holds the new to-do**, over the
built service `built? cached` under the reference model, from any cache content. At a title that is
not empty, `TodoApp_add` runs `add` under `provideContext`, invalidates the cache's cell by calling
`listCacheInvalidate`, and `TodoApp_list` invokes `listCacheGet` (`Eff.invoke`) with `list` under
`provideContext` as its loader, answering the stored to-dos with the new one among them. It is
`list_after_add` (`Test/Dogfood/Scenario/Todo/Claims.lean`) proved of the built service's own
definitions through `hostRunBlockB` and `invalidate_get`.

Placement: concept `translation-simulation`; property: a composed module's law (R10), the claim
of an application carried to the imposed module's code by the module's agreement (row 378 (2) and
(8)). Question: the registry claim `ref-cache-invalidated-reads-through`, of which this is the
application reader; the to-do's modules load under no root of the registry (row 336 (9)). Reach:
the built service `built? cached`, every title but the empty one, every start state of the model,
every context, cached value and cell, at the block's row meaning under the model (`hostRunBlockB`).
Does not establish: the PROC-6 machine replay agreement (PROC-6, row 378 (23)); anything
of a host that disagrees with the model. Unlocks: the slice's claim of the imposed to-do over the
code that builds and emits (row 378 (8)).

Proof: `built_cached_bodies`, `hostRunBlockB_bind`, `denoteBlockB_call_add` with `add_on_model_at`,
`denoteBlockB_call_list`, then the cache's `invalidate_get`, and the model's answer at `all` by
computation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cached_list_after_add : CachedListAfterAdd := by
  intro b title start ctx outerCtx c q s hbuilt hne held
  unfold addThenList
  rw [built_cached_bodies hbuilt, hostRunBlockB_bind]
  have hadd0 :
      runRowsH modelHost
        ((denoteRows application.table (addAt title) []).bind
          (seqRows fun v =>
            (denoteRows application.table invalidateBody [Val.cell q]).bind
              (seqRows fun _ => pure (Exit.success v)))) s start =
      (hostRun modelHost invalidateBody [Val.cell q] s
          (start.1 + 1, start.2 ++ [(start.1, title, false)])).map fun r' =>
        match r'.1 with
        | Exit.success _ => (Exit.success (todo start.1 title false), r'.2)
        | Exit.failure cause => (Exit.failure cause, r'.2) := by
    rw [runRowsH_bind]
    change (hostRun modelHost (addAt title) [] s start).bind _ = _
    rw [add_on_model_at title hne start s, Option.bind_some]
    dsimp only [seqRows]
    rw [runRowsH_bind]
    change (hostRun modelHost invalidateBody [Val.cell q] s
        (start.1 + 1, start.2 ++ [(start.1, title, false)])).bind _ = _
    cases hostRun modelHost invalidateBody [Val.cell q] s
        (start.1 + 1, start.2 ++ [(start.1, title, false)]) with
    | none => rfl
    | some result =>
      obtain ⟨ex, stores, state⟩ := result
      cases ex <;> rfl
  have hadd :
      hostRunBlockB modelHost cachedBodies 2 []
        (.perform (.call 4) (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))
        outerCtx [Val.list [Val.context ctx, Val.cell q], .str title] s start =
      ((hostRun modelHost invalidateBody [Val.cell q] s
          (start.1 + 1, start.2 ++ [(start.1, title, false)])).map fun r' =>
        match r'.1 with
        | Exit.success _ => (Exit.success (todo start.1 title false), r'.2)
        | Exit.failure cause => (Exit.failure cause, r'.2)).map fun r' => (some r'.1, r'.2) := by
    unfold hostRunBlockB
    rw [denoteBlockB_call_add title ctx outerCtx q, runRowsH_map_some, hadd0]
  rw [hadd]
  have hlist :
      hostRunBlockB modelHost cachedBodies 2 []
        (.perform (.call 5) (.var 0)) outerCtx
        ([Val.list [Val.context ctx, Val.cell q], .str title] ++ [todo start.1 title false]) =
      fun stores state =>
        (hostRun modelHost (paramsAsRows 1 getBody) [Val.cell q] stores state).map
          fun result => (some result.1, result.2) := by
    funext stores state
    unfold hostRunBlockB hostRun
    rw [denoteBlockB_call_list ctx outerCtx q title (todo start.1 title false), runRowsH_map_some]
  have hstep :
      (((hostRun modelHost invalidateBody [Val.cell q] s
          (start.1 + 1, start.2 ++ [(start.1, title, false)])).map fun r' =>
        match r'.1 with
        | Exit.success _ => (Exit.success (todo start.1 title false), r'.2)
        | Exit.failure cause => (Exit.failure cause, r'.2)).map fun r' => (some r'.1, r'.2)).bind
        (fun result => match result.1 with
          | none => some (none, result.2)
          | some (Exit.success v) =>
            hostRunBlockB modelHost cachedBodies 2 [] (.perform (.call 5) (.var 0)) outerCtx
              ([Val.list [Val.context ctx, Val.cell q], .str title] ++ [v]) result.2.1 result.2.2
          | some (Exit.failure cause) => some (some (Exit.failure cause), result.2)) =
      ((hostRun modelHost invalidateBody [Val.cell q] s
          (start.1 + 1, start.2 ++ [(start.1, title, false)])).bind
        (fun result => hostRun modelHost (paramsAsRows 1 getBody) [Val.cell q] result.2.1 result.2.2)).map
          fun result => (some result.1, result.2) := by
    rw [Effect4.Ref.Cache.invalidate_run modelHost Image.ident c _ held]
    dsimp only [Option.map, Option.bind]
    exact congrFun (congrFun hlist _) _
  refine (congrArg (Option.map (·.1)) hstep).trans ?_
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
