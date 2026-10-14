import Effect4.Laws.Program.Block
import Effect4.Laws.Program.Folds.DenoteRows
import Effect4.Laws.Program.HostRuns

/-!
# Program.ParamRows — a body's parameter runs as rows, and `invoke` unfolds on the row meaning

A definition's body runs its parameters by `NativeOp.param` (decisions row 340). The call tree
`denoteRows` (`src/Effect4/Laws/Program/DenoteRows.lean`) gives a parameter's run no node: it is
outside its fragment, and its exit is `outsideExit`. PROC-5's block meaning reads each
invocation as a row (`callsAsRows`, `src/Effect4/Laws/Program/Block.lean`), and it reads no
parameter run.

* **A body's parameters as rows** (`paramsAsRows`). `paramsAsRows n` reads parameter `j` as the row
  `n + j`, after a table's `n` rows. Both readings rename a program's operations by one fold,
  `mapOps` (`src/Effect4/Laws/Program/Block.lean`): `callsAsRows n` is `mapOps (callAsRow n)` and
  `paramsAsRows n` is `mapOps (paramAsRow n)`.
* **The block meaning over rows and parameters** (`denoteBody`, `hostRunBody`, `hostRunDefs`).
  `blockStepAlg` is the `EffAlgebra` that extends `denoteRows.alg`
  (`src/Effect4/Laws/Program/Folds/DenoteRows.lean`) with four rules:
  - `perform (call k) r` calls definition `k` at the evaluated request `v` with no program
    arguments;
  - `perform (param j) r` runs parameter `j` at the evaluated request `w`;
  - `invoke k r args` calls definition `k` at the evaluated request `v`, passing each program
    argument `arg` as `fun w => denoteBody … arg (env ++ [w])` in the caller's environment;
  - `provideContext c body` checks that `c` evaluates to a context and runs `body` in the caller's
    environment.
  `denoteBody` iterates `cata_eff (blockStepAlg …)` over a call budget `fuel : Nat`. Every traversal
  of `Eff` is `cata_eff`.
* **The laws** (`denoteBody_invoke_one`, `denoteBody_call`, `denoteBody_provideContext`,
  `denoteBody_straightRows`, `hostRunBody_invoke_one`, `hostRunBody_call`,
  `hostRunBody_provideContext`, `hostRunBody_straightRows`). On `StraightRows`, `denoteBody` is
  `denoteRows` at every budget, parameter list and body table. At a positive budget, `invoke` and
  `perform (call k)` unfold to the definition's body at `[v]` with the caller's denoted arguments.

Placement:

- Concept: `translation-simulation`; property: an invocation of a definition unfolds to its body at
  the evaluated request and the caller's denoted program arguments, and agrees with `denoteRows` on
  `StraightRows` (R10, decisions rows 340 and 378 (8), (23)).
- Question: the registry claim `ref-cache-invalidated-reads-through` (role compatibility), whose
  application reader `cached_list_after_add` (`Test/Dogfood/Scenario/Todo/Cached.lean`) states its
  claim over the built service's own definitions through `hostRunDefs`.
- Reach: every row table, host comodel, definition block and parameter list; exact agreement with
  `denoteRows` on `StraightRows` at any budget; one-step unfolding of `invoke`, `call`, `param` and
  `provideContext` at a positive call budget.
- Does not establish: machine replay agreement (`Run.denoteRows_eq_session`) for `Eff.invoke` or
  `provideContext` before block inlining (PROC-6); unbounded recursion without a call budget;
  anything of a fiber-sharing schedule.
- Unlocks: stating and proving claims about an application's built service definitions and imposed
  banked modules directly over `(built? app).program` (decisions row 378 (8) and (23)).
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- A parameter's run as a row: parameter `j` is the row `n + j`, after a table's `n` rows. -/
def paramAsRow (n : Nat) : NativeOp → NativeOp
  | .param j => .external (n + j)
  | op => op

/-- **A body's parameter runs as rows**: every `perform (param j) r` becomes
`perform (external (n + j)) r`. -/
def paramsAsRows (n : Nat) : NativeEff → NativeEff := mapOps (paramAsRow n)

/-! ## The block meaning over rows and program parameters -/

/-- A denoted program parameter over `table`: a function from the parameter's request `Val` to its
call tree in `Effects.Program (RowsSig table) ExitV`. -/
abbrev ParamTree (table : RowTable) : Type :=
  Val → Effects.Program (RowsSig table) ExitV

/-- Carrier family for the one-step block algebra over `table`: `.eff` is `List Val →
Effects.Program (RowsSig table) ExitV`, `.effs` is a list of those trees (the program arguments of
`Eff.invoke`), and all other sorts are `Unit`. -/
abbrev BlockCarrier (table : RowTable) : EffFam → Type
  | .eff => List Val → Effects.Program (RowsSig table) ExitV
  | .stmt => Unit
  | .stmts => Unit
  | .effs => List (List Val → Effects.Program (RowsSig table) ExitV)
  | .action => Unit
  | .layer => Unit
  | .layers => Unit

/-- The `EffAlgebra` for one call depth of a definition block over `table`, with program parameters
`params` and recursive call handler `call`. On `StraightRows` constructors it delegates to
`denoteRows.alg` (`src/Effect4/Laws/Program/Folds/DenoteRows.lean`). -/
def blockStepAlg (table : RowTable) (params : List (ParamTree table))
    (call : Nat → Val → List (ParamTree table) → Effects.Program (RowsSig table) ExitV) :
    EffAlgebra NativeOp (BlockCarrier table) where
  eff_succeed := (denoteRows.alg table).eff_succeed
  eff_fail := (denoteRows.alg table).eff_fail
  eff_failCause := (denoteRows.alg table).eff_failCause
  eff_sync := (denoteRows.alg table).eff_sync
  eff_suspend := (denoteRows.alg table).eff_suspend
  eff_perform op r := fun env =>
    match op with
    | .call k =>
      match evalTerm env r with
      | some v => call k v []
      | none => pure badShapeExit
    | .param j =>
      match evalTerm env r, params[j]? with
      | some w, some param => param w
      | _, _ => pure outsideExit
    | _ => (denoteRows.alg table).eff_perform op r env
  eff_bind := (denoteRows.alg table).eff_bind
  eff_gen := (denoteRows.alg table).eff_gen
  eff_catchCause := (denoteRows.alg table).eff_catchCause
  eff_matchCause := (denoteRows.alg table).eff_matchCause
  eff_onExit := (denoteRows.alg table).eff_onExit
  eff_exit := (denoteRows.alg table).eff_exit
  eff_uninterruptible := (denoteRows.alg table).eff_uninterruptible
  eff_interruptible := (denoteRows.alg table).eff_interruptible
  eff_yieldNow := (denoteRows.alg table).eff_yieldNow
  eff_awaitFiber := (denoteRows.alg table).eff_awaitFiber
  eff_withFiber := (denoteRows.alg table).eff_withFiber
  eff_scoped := (denoteRows.alg table).eff_scoped
  eff_acquireRelease := (denoteRows.alg table).eff_acquireRelease
  eff_provideLayer := (denoteRows.alg table).eff_provideLayer
  eff_service := (denoteRows.alg table).eff_service
  eff_provideService := (denoteRows.alg table).eff_provideService
  eff_catchIf := (denoteRows.alg table).eff_catchIf
  eff_select := (denoteRows.alg table).eff_select
  eff_iterate := (denoteRows.alg table).eff_iterate
  eff_restore := (denoteRows.alg table).eff_restore
  eff_defs _ _ _ _ := fun _ => pure outsideExit
  eff_invoke k r args := fun env =>
    match evalTerm env r with
    | some v => call k v (args.map fun arg w => arg (env ++ [w]))
    | none => pure badShapeExit
  eff_provideContext c body := fun env =>
    match (evalTerm env c).bind Val.context? with
    | some _ => body env
    | none => pure badShapeExit
  stmt_bindYield _ := ()
  stmt_yieldDiscard _ := ()
  stmt_ret _ := ()
  stmt_ifElse _ _ _ := ()
  stmt_whileTrue _ := ()
  stmt_breakLoop := ()
  stmts_nil := ()
  stmts_cons _ _ := ()
  effs_nil := []
  effs_cons head tail := head :: tail
  action_fork _ _ := ()
  action_forkIn _ _ _ := ()
  action_forkScoped _ _ := ()
  action_runIn _ _ := ()
  action_interrupt _ := ()
  action_interruptScoped _ := ()
  action_interruptAll _ _ := ()
  action_awaitAll _ := ()
  action_awaitAllFailFast _ := ()
  action_snapshotChildren := ()
  action_awaitNewChildren _ := ()
  action_raceAll _ := ()
  action_getId := ()
  action_closeScope _ _ := ()
  action_getInterruptible := ()
  action_raceAllFirst _ := ()
  action_context _ := ()
  layer_succeed _ _ := ()
  layer_effect _ _ := ()
  layer_effectDiscard _ := ()
  layer_provide _ _ := ()
  layer_provideMerge _ _ := ()
  layer_merge _ _ := ()
  layer_fresh _ := ()
  layer_orDie _ := ()
  layer_ref _ := ()
  layer_mergeAll _ := ()
  layers_nil := ()
  layers_cons _ _ := ()

/-- The call tree of `e` over `table`, definition bodies `bodies`, call budget `fuel`, and denoted
program parameters `params`. Each step traverses `e` by `cata_eff`. -/
def denoteBody (table : RowTable) (bodies : List NativeEff) :
    Nat → List (ParamTree table) → NativeEff → List Val → Effects.Program (RowsSig table) ExitV
  | 0, params, e, env =>
    cata_eff (blockStepAlg table params (fun _ _ _ => pure outsideExit)) e env
  | fuel + 1, params, e, env =>
    cata_eff
      (blockStepAlg table params fun k v args =>
        match bodies[k]? with
        | some body => denoteBody table bodies fuel args body [v]
        | none => pure outsideExit)
      e env

/-- Run `denoteBody` under a host comodel `host` from stores `s` and host state `st`. -/
def hostRunBody {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (bodies : List NativeEff) (fuel : Nat) (params : List (ParamTree table))
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    Option (ExitV × (Stores × σ)) :=
  runRowsH host (denoteBody table bodies fuel params e env) s st

/-- The definition bodies of a program's leading definition block (`blockOf?`,
`src/Effect4/Laws/Program/Block.lean`), or `[]` when the program has no block. -/
def bodiesOf (p : NativeEff) : List NativeEff :=
  match blockOf? p with
  | some (_, bodies, _) => bodies
  | none => []

/-- Run `e` over the definition bodies of `block` under `host` with no outer program parameters. -/
def hostRunDefs {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (block : NativeEff) (fuel : Nat) (e : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    Option (ExitV × (Stores × σ)) :=
  hostRunBody host (bodiesOf block) fuel [] e env s st

/-! ## Unfolding and agreement laws -/

/-- `denoteBody` on `succeed` evaluates the term in `env`. Placement: as module docstring; helper of
service-method proofs. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_succeed (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (t : Term) (env : List Val) :
    denoteBody table bodies fuel params (.succeed t) env =
      pure (match evalTerm env t with | some x => Exit.success x | none => badShapeExit) := by
  cases fuel <;> rfl

/-- `denoteBody` on `bind` sequences the first tree into the second by `Effects.Program.bind` and
`seqRows`. Placement: as module docstring; consumer: `hostRunBody_bind`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_bind (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (a b : NativeEff) (env : List Val) :
    denoteBody table bodies fuel params (.bind a b) env =
      Effects.Program.bind (denoteBody table bodies fuel params a env)
        (seqRows fun v => denoteBody table bodies fuel params b (env ++ [v])) := by
  cases fuel <;> rfl

/-- `denoteBody` on `provideContext` runs `body` in `env` when `c` evaluates to a context.
Placement: as module docstring; consumer: `hostRunBody_provideContext`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_provideContext (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (c : Term) (body : NativeEff) (env : List Val)
    (ctx : Ctx) (hc : (evalTerm env c).bind Val.context? = some ctx) :
    denoteBody table bodies fuel params (.provideContext c body) env =
      denoteBody table bodies fuel params body env := by
  cases fuel with
  | zero =>
    change (match (evalTerm env c).bind Val.context? with
      | some _ => denoteBody table bodies 0 params body env
      | none => pure badShapeExit) = _
    rw [hc]
  | succ fuel =>
    change (match (evalTerm env c).bind Val.context? with
      | some _ => denoteBody table bodies (fuel + 1) params body env
      | none => pure badShapeExit) = _
    rw [hc]

/-- At a positive call budget, `perform (call k) r` unfolds to definition `k`'s body at `[v]` with
no program parameters. Placement: as module docstring; consumer: `hostRunBody_call`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_call (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (k : Nat) (r : Term) (env : List Val)
    (body : NativeEff) (v : Val) (hk : bodies[k]? = some body) (hr : evalTerm env r = some v) :
    denoteBody table bodies (fuel + 1) params (.perform (.call k) r) env =
      denoteBody table bodies fuel [] body [v] := by
  change (match evalTerm env r with
    | some v =>
      match bodies[k]? with
      | some body => denoteBody table bodies fuel [] body [v]
      | none => pure outsideExit
    | none => pure badShapeExit) = _
  rw [hr, hk]

/-- At a positive call budget, `invoke k r (.cons a .nil)` unfolds to definition `k`'s body at `[v]`
with one denoted program parameter `fun w => denoteBody table bodies (fuel + 1) params a (env ++ [w])`.
Placement: as module docstring; consumer: `hostRunBody_invoke_one`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_invoke_one (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (k : Nat) (r : Term) (a : NativeEff) (env : List Val)
    (body : NativeEff) (v : Val) (hk : bodies[k]? = some body) (hr : evalTerm env r = some v) :
    denoteBody table bodies (fuel + 1) params (.invoke k r (.cons a .nil)) env =
      denoteBody table bodies fuel
        [fun w => denoteBody table bodies (fuel + 1) params a (env ++ [w])] body [v] := by
  change (match evalTerm env r with
    | some v =>
      match bodies[k]? with
      | some body =>
        denoteBody table bodies fuel
          [fun w => denoteBody table bodies (fuel + 1) params a (env ++ [w])] body [v]
      | none => pure outsideExit
    | none => pure badShapeExit) = _
  rw [hr, hk]

/-- `perform (param j) r` runs parameter `j` at the evaluated request `w`. Placement: as module
docstring; consumer: `Effect4.Ref.Cache.denoteBody_getBody`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_param (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (j : Nat) (r : Term) (env : List Val)
    (param : ParamTree table) (w : Val) (hj : params[j]? = some param)
    (hr : evalTerm env r = some w) :
    denoteBody table bodies fuel params (.perform (.param j) r) env = param w := by
  cases fuel <;> {
    change (match evalTerm env r, params[j]? with
      | some w, some param => param w
      | _, _ => pure outsideExit) = _
    rw [hr, hj]
  }

/-- On `StraightRows`, `cata_eff (blockStepAlg table params call)` agrees with `denoteRows` for any
parameter list `params` and call handler `call`. Placement: as module docstring; consumer:
`denoteBody_straightRows`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cata_blockStepAlg_straightRows (table : RowTable) (params : List (ParamTree table))
    (call : Nat → Val → List (ParamTree table) → Effects.Program (RowsSig table) ExitV) :
    ∀ (e : NativeEff) (env : List Val), StraightRows table e = true →
      cata_eff (blockStepAlg table params call) e env = denoteRows table e env
  | .succeed _, _, _ => rfl
  | .fail _, _, _ => rfl
  | .failCause _, _, _ => rfl
  | .sync _, _, _ => rfl
  | .suspend b, env, hs => cata_blockStepAlg_straightRows table params call b env hs
  | .perform op _, _, hs => by
    cases op with
    | call _ => exact absurd hs Bool.false_ne_true
    | param _ => exact absurd hs Bool.false_ne_true
    | _ => rfl
  | .bind a b, env, hs => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) a env)
        (seqRows fun v => cata_eff (blockStepAlg table params call) b (env ++ [v])) =
      Effects.Program.bind (denoteRows table a env)
        (seqRows fun v => denoteRows table b (env ++ [v]))
    rw [cata_blockStepAlg_straightRows table params call a env ha]
    congr 1
    funext ex
    cases ex with
    | failure c => rfl
    | success v => exact cata_blockStepAlg_straightRows table params call b (env ++ [v]) hb
  | .select t d a b, env, hs => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs
    change (match (evalTerm env t).bind d.decide with
      | some (true, bound) => cata_eff (blockStepAlg table params call) a (env ++ bound.toList)
      | some (false, bound) => cata_eff (blockStepAlg table params call) b (env ++ bound.toList)
      | none => pure badShapeExit) =
      (match (evalTerm env t).bind d.decide with
      | some (true, bound) => denoteRows table a (env ++ bound.toList)
      | some (false, bound) => denoteRows table b (env ++ bound.toList)
      | none => pure badShapeExit)
    rcases (evalTerm env t).bind d.decide with _ | ⟨_ | _, bound⟩
    · rfl
    · exact cata_blockStepAlg_straightRows table params call b (env ++ bound.toList) hb
    · exact cata_blockStepAlg_straightRows table params call a (env ++ bound.toList) ha
  | .exit b, env, hs => by
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) b env) _ =
      Effects.Program.bind (denoteRows table b env) _
    rw [cata_blockStepAlg_straightRows table params call b env hs]
  | .catchCause b h, env, hs => by
    obtain ⟨hb, hh⟩ := Bool.and_eq_true_iff.mp hs
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) b env) _ =
      Effects.Program.bind (denoteRows table b env) _
    rw [cata_blockStepAlg_straightRows table params call b env hb]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact cata_blockStepAlg_straightRows table params call h (env ++ [Val.exitErr c]) hh
  | .catchIf test b h, env, hs => by
    obtain ⟨hb, hh⟩ := Bool.and_eq_true_iff.mp hs
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) b env) _ =
      Effects.Program.bind (denoteRows table b env) _
    rw [cata_blockStepAlg_straightRows table params call b env hb]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure cause =>
      dsimp only
      cases caughtErrorValue? env test cause with
      | none => rfl
      | some value => exact cata_blockStepAlg_straightRows table params call h (env ++ [value]) hh
  | .matchCause b v c, env, hs => by
    obtain ⟨hbv, hc⟩ := Bool.and_eq_true_iff.mp hs
    obtain ⟨hb, hv⟩ := Bool.and_eq_true_iff.mp hbv
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) b env) _ =
      Effects.Program.bind (denoteRows table b env) _
    rw [cata_blockStepAlg_straightRows table params call b env hb]
    congr 1
    funext ex
    cases ex with
    | success x => exact cata_blockStepAlg_straightRows table params call v (env ++ [x]) hv
    | failure cause =>
      exact cata_blockStepAlg_straightRows table params call c (env ++ [Val.exitErr cause]) hc
  | .onExit b f, env, hs => by
    obtain ⟨hb, hf⟩ := Bool.and_eq_true_iff.mp hs
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) b env) _ =
      Effects.Program.bind (denoteRows table b env) _
    rw [cata_blockStepAlg_straightRows table params call b env hb]
    congr 1
    funext ex
    change Effects.Program.bind (cata_eff (blockStepAlg table params call) f (env ++ [reifyExitVal ex])) _ =
      Effects.Program.bind (denoteRows table f (env ++ [reifyExitVal ex])) _
    rw [cata_blockStepAlg_straightRows table params call f (env ++ [reifyExitVal ex]) hf]
  | .gen _, _, hs
  | .uninterruptible _, _, hs
  | .interruptible _, _, hs
  | .yieldNow _, _, hs
  | .awaitFiber _ _, _, hs
  | .withFiber _, _, hs
  | .scoped _, _, hs
  | .acquireRelease _ _, _, hs
  | .provideLayer _ _ _, _, hs
  | .service _, _, hs
  | .provideService _ _ _, _, hs
  | .iterate _ _ _ _ _ _, _, hs
  | .restore _ _, _, hs
  | .defs _ _ _ _, _, hs
  | .invoke _ _ _, _, hs
  | .provideContext _ _, _, hs => absurd hs Bool.false_ne_true

/-- **On `StraightRows`, `denoteBody` is `denoteRows`** at every call budget, definition block and
parameter list. Placement: as module docstring; consumer: `hostRunBody_straightRows`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBody_straightRows (table : RowTable) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (e : NativeEff) (env : List Val)
    (hs : StraightRows table e = true) :
    denoteBody table bodies fuel params e env = denoteRows table e env := by
  cases fuel <;> exact cata_blockStepAlg_straightRows table params _ e env hs

/-- **On `StraightRows`, `hostRunBody` is `hostRun`** at every call budget, definition block and
parameter list. Placement: as module docstring; consumer: `Test.Dogfood.Scenario.Todo.Cached`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBody_straightRows {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (e : NativeEff) (env : List Val) (s : Stores) (st : σ)
    (hs : StraightRows table e = true) :
    hostRunBody host bodies fuel params e env s st = hostRun host e env s st := by
  unfold hostRunBody hostRun
  rw [denoteBody_straightRows table bodies fuel params e env hs]

/-- `hostRunBody` on `succeed` returns the evaluated term in `env`. Placement: as module docstring;
consumer: `Test.Dogfood.Scenario.Todo.Cached`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBody_succeed {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (t : Term) (env : List Val) (s : Stores) (st : σ)
    (v : Val) (ht : evalTerm env t = some v) :
    hostRunBody host bodies fuel params (.succeed t) env s st =
      some (.success v, (s, st)) := by
  unfold hostRunBody
  rw [denoteBody_succeed, ht]
  rfl

/-- `hostRunBody` on `bind` threads a successful first exit into the continuation and propagates a
failure exit. Placement: as module docstring; consumer: `Test.Dogfood.Scenario.Todo.Cached`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBody_bind {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (a b : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    hostRunBody host bodies fuel params (.bind a b) env s st =
      (hostRunBody host bodies fuel params a env s st).bind fun r =>
        match r.1 with
        | .success v => hostRunBody host bodies fuel params b (env ++ [v]) r.2.1 r.2.2
        | .failure c => some (.failure c, r.2) := by
  unfold hostRunBody
  rw [denoteBody_bind, runRowsH_bind]
  cases runRowsH host (denoteBody table bodies fuel params a env) s st with
  | none => rfl
  | some r =>
    obtain ⟨ex, s', st'⟩ := r
    cases ex <;> rfl

/-- `hostRunBody` on `provideContext` runs `body` when `c` evaluates to a context. Placement: as
module docstring; consumer: `Test.Dogfood.Scenario.Todo.Cached`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBody_provideContext {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (c : Term) (body : NativeEff) (env : List Val)
    (s : Stores) (st : σ) (ctx : Ctx)
    (hc : (evalTerm env c).bind Val.context? = some ctx) :
    hostRunBody host bodies fuel params (.provideContext c body) env s st =
      hostRunBody host bodies fuel params body env s st := by
  unfold hostRunBody
  rw [denoteBody_provideContext table bodies fuel params c body env ctx hc]

/-- At a positive call budget, `hostRunBody` on `perform (call k) r` runs definition `k`'s body at
`[v]` with no program parameters. Placement: as module docstring; consumer:
`Test.Dogfood.Scenario.Todo.Cached`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBody_call {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (k : Nat) (r : Term) (env : List Val)
    (s : Stores) (st : σ) (body : NativeEff) (v : Val)
    (hk : bodies[k]? = some body) (hr : evalTerm env r = some v) :
    hostRunBody host bodies (fuel + 1) params (.perform (.call k) r) env s st =
      hostRunBody host bodies fuel [] body [v] s st := by
  unfold hostRunBody
  rw [denoteBody_call table bodies fuel params k r env body v hk hr]

/-- At a positive call budget, `hostRunBody` on `invoke k r (.cons a .nil)` runs definition `k`'s
body at `[v]` with one denoted program parameter. Placement: as module docstring; consumer:
`Effect4.Ref.Cache.hostRunBody_invoke_get`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBody_invoke_one {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (fuel : Nat)
    (params : List (ParamTree table)) (k : Nat) (r : Term) (a : NativeEff) (env : List Val)
    (s : Stores) (st : σ) (body : NativeEff) (v : Val)
    (hk : bodies[k]? = some body) (hr : evalTerm env r = some v) :
    hostRunBody host bodies (fuel + 1) params (.invoke k r (.cons a .nil)) env s st =
      hostRunBody host bodies fuel
        [fun w => denoteBody table bodies (fuel + 1) params a (env ++ [w])] body [v] s st := by
  unfold hostRunBody
  rw [denoteBody_invoke_one table bodies fuel params k r a env body v hk hr]

end Effect4.Program.Denote


