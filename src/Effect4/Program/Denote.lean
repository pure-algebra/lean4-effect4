import Effect4.Program.Compile
import Effects.Algebra.Laws

/-!
# Program.Denote — the straight-line fragment of `Eff` in the algebra

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §4; packet
`Test/contracts/program-denotation.contract.md`; battery `Test/Program/DenoteContract.lean`.

`denote` sends the straight-line fragment of `Eff` (`Straight`: exits, `sync`, `suspend`,
the `sync` rows, `bind`, `branch`, `exit`, `catchCause`, `matchCause`, `onExit`) into
`Effects.Program` over the store signature `StoreSig` (every `SyncOp`, answered by one
`Val`), and `storeHandler` interprets that signature into `StateT Stores Id` by `syncOpStep`
with the machine's own fallback. `meaning e env s` is the exit and the stores the algebra
answers. Every arm of `denote` mirrors one arm of `compileEff`
(`src/Effect4/Program/Compile.lean:280-356`) and the hook it reaches: `syncValueAt` (`:593`),
`suspendBodyAt` (`:602`), `contAOf` (`:552`), `contEOf` (`:574`), `finalizerProgram` (`:693`).
The machine itself is not imported into the meaning; it meets the meaning in the battery, one
program at a time, and in `run_eq_meaning` (the packet's stated theorem, slice 2).

Two asymmetries are the compile's, kept on purpose: an ill-formed `sync` term answers
`Val.unit` (`syncValueAt`'s `getD`, `E4-DEN-CE-001`) where an ill-formed `succeed` is the
`badName` defect; and a store operation on a key the store never minted answers `Val.unit`
(`Fibers.lean:834-840`: `syncState = none` falls back to `syncValue`, `E4-DEN-CE-002`).

The equations below are the algebra's laws specialised: `interpret_bind` and
`interpret_perform` of `Effects.Algebra.Laws`, at `propext`/`Quot.sound`.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-! ## The store signature and the exits -/

/-- The store signature: every `sync` operation of the stores, answered by one value. An
`abbrev`, so `StoreSig.Op` is `SyncOp` under every transparency. -/
abbrev StoreSig : Effects.Signature.{0, 0} := ⟨SyncOp, fun _ => Val⟩

/-- `Compile.badShape` (`Compile.lean:250`), as an exit. -/
def badShapeExit : ExitV := Exit.failure (Cause.die Defect.badName)

/-- Outside the fragment; never reached under `Straight`. -/
def outsideExit : ExitV := Exit.failure (Cause.die Defect.notImplemented)

/-- A finalizer's exit as `Exit.restoreAfterFinalizer` reads it: `contAOf (.restore exit)`
restores the body's exit on a succeeding finalizer (`Compile.lean:555`) and `contEOf` merges a
failing one (`:577`). -/
def finVoid : ExitV → VoidExitV
  | Exit.success _ => Exit.void
  | Exit.failure c => Exit.failure c

/-- Short-circuit on failure: the `OnSuccess` frame passes a cause through
(`Frames.lean`, `armA` is `none` on a failure). -/
def seqExit (k : Val → Effects.Program StoreSig ExitV) : ExitV → Effects.Program StoreSig ExitV
  | Exit.success v => k v
  | Exit.failure c => pure (Exit.failure c)

/-! ## The fragment -/

/-- The straight-line fragment: one fiber, no park, no fork, no loop, no tape. A `perform`
is in the fragment exactly when its row is a `sync` row. -/
def Straight : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .yieldError _ => true
  | .sync _ => true
  | .suspend b => Straight b
  | .perform op _ =>
    match (NativeOp.row op).kind with
    | .sync => true
    | _ => false
  | .bind a b => Straight a && Straight b
  | .branch _ a b => Straight a && Straight b
  | .exit b => Straight b
  | .catchCause b h => Straight b && Straight h
  | .matchCause b v c => Straight b && Straight v && Straight c
  | .onExit b f => Straight b && Straight f
  | _ => false

/-! ## The denotation -/

/-- The straight-line fragment in the algebra. Each arm names the `compileEff` arm it
mirrors (`Compile.lean`, lines in the comments). -/
def denote : NativeEff → List Val → Effects.Program StoreSig ExitV
  -- `:286-289`: `succeed v` is `Prim.success (eval v)`, or `badShape`.
  | .succeed v, env =>
    pure (match evalTerm env v with | some x => Exit.success x | none => badShapeExit)
  -- `:290-293`: `fail e` is `Prim.failure (Cause.fail (errOf val))`, or `badShape`.
  | .fail e, env =>
    pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => badShapeExit)
  -- `:294-297`: `failCause c` is `Prim.failure (causeOf c)`, or `badShape`.
  | .failCause c, env =>
    pure (match causeOf env c with | some cause => Exit.failure cause | none => badShapeExit)
  -- `:298-301`: `yieldError e` is `Prim.yieldableError (errOf val)`, which steps to
  -- `Prim.failure (Cause.fail error)` (`Frames.lean`, `step`).
  | .yieldError e, env =>
    pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => badShapeExit)
  -- `:302` and `syncValueAt` (`:593-598`): the term's value, `Val.unit` when it has none.
  | .sync t, env => pure (Exit.success ((evalTerm env t).getD Val.unit))
  -- `:303` and `suspendBodyAt` (`:602-614`): the body at the child point.
  | .suspend b, env => denote b env
  -- `:304-318`: a `sync` row runs `syncOpOf op val` through the stores; a request that does
  -- not evaluate, or does not decode, is `badShape`. Async and program rows are outside.
  | .perform op r, env =>
    match (NativeOp.row op).kind with
    | .sync =>
      match (evalTerm env r).bind (NativeOp.syncOpOf op) with
      | some o =>
        Effects.Program.bind (Effects.Program.perform (S := StoreSig) o) fun v =>
          pure (Exit.success v)
      | none => pure badShapeExit
    | _ => pure outsideExit
  -- `:319` and `contAOf (.cont p)` (`:553`): the rest at `env ++ [v]`; a failure passes the
  -- `OnSuccess` frame.
  | .bind a b, env => Effects.Program.bind (denote a env) (seqExit fun v => denote b (env ++ [v]))
  -- `:329` and `suspendBodyAt` (`:608-612`): the branch the environment decides.
  | .branch t a b, env =>
    match evalTerm env t with
    | some (Val.bool true) => denote a env
    | some (Val.bool false) => denote b env
    | _ => pure badShapeExit
  -- `:326` and the `exitFrame` arm of `armA`/`armE`: the body's exit as a value.
  | .exit b, env =>
    Effects.Program.bind (denote b env) fun ex => pure (Exit.success (reifyExitVal ex))
  -- `:321` and `contEOf (.caught p)` (`:575`): the handler at `env ++ [exitErr cause]`; a
  -- success passes the `OnFailure` frame.
  | .catchCause b h, env => Effects.Program.bind (denote b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure c => denote h (env ++ [Val.exitErr c])
  -- `:322-324`, `contAOf (.onValue p)` (`:554`) and `contEOf (.onCause p)` (`:576`).
  | .matchCause b v c, env => Effects.Program.bind (denote b env) fun
    | Exit.success x => denote v (env ++ [x])
    | Exit.failure cause => denote c (env ++ [Val.exitErr cause])
  -- `:325`, `finalizerProgram (.fin p)` (`:695`) at `env ++ [reifyExitVal exit]`, then the
  -- restore names (`:555`, `:577`).
  | .onExit b f, env => Effects.Program.bind (denote b env) fun ex =>
    Effects.Program.bind (denote f (env ++ [reifyExitVal ex])) fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex))
  | _, _ => pure outsideExit

/-! ## The handler and the meaning -/

/-- The one handler: the store step (`Stores.lean:1209`), with the machine's fallback on
`none` (`Fibers.lean:834-840` through `syncValueAt`, `Compile.lean:593-598`). -/
def storeHandler : Effects.Handler StoreSig (StateT Stores Id) where
  handle o := fun s => match syncOpStep o s with
    | some (s', v) => (v, s')
    | none => (Val.unit, s)

/-- The meaning of a program at an environment: the exit it answers and the stores it leaves. -/
def meaning (e : NativeEff) (env : List Val) (s : Stores) : ExitV × Stores :=
  (Effects.interpret storeHandler (denote e env)).run s

/-! ## The fragment is closed under subprograms -/

theorem Straight.suspend {b : NativeEff} (h : Straight (.suspend b) = true) :
    Straight b = true := h

theorem Straight.bind {a b : NativeEff} (h : Straight (.bind a b) = true) :
    Straight a = true ∧ Straight b = true := by
  simpa [Straight, Bool.and_eq_true] using h

theorem Straight.branch {t : Term} {a b : NativeEff} (h : Straight (.branch t a b) = true) :
    Straight a = true ∧ Straight b = true := by
  simpa [Straight, Bool.and_eq_true] using h

theorem Straight.exit {b : NativeEff} (h : Straight (.exit b) = true) : Straight b = true := h

theorem Straight.catchCause {b h' : NativeEff} (h : Straight (.catchCause b h') = true) :
    Straight b = true ∧ Straight h' = true := by
  simpa [Straight, Bool.and_eq_true] using h

theorem Straight.matchCause {b v c : NativeEff} (h : Straight (.matchCause b v c) = true) :
    Straight b = true ∧ Straight v = true ∧ Straight c = true := by
  simpa [Straight, Bool.and_eq_true, and_assoc] using h

theorem Straight.onExit {b f : NativeEff} (h : Straight (.onExit b f) = true) :
    Straight b = true ∧ Straight f = true := by
  simpa [Straight, Bool.and_eq_true] using h

theorem Straight.perform_sync {op : NativeOp} {r : Term} (h : Straight (.perform op r) = true) :
    (NativeOp.row op).kind = .sync := by
  unfold Straight at h
  revert h
  cases (NativeOp.row op).kind <;> simp

/-! ## The equations of the meaning -/

theorem meaning_succeed_some (v : Term) (env : List Val) (s : Stores) {x : Val}
    (hx : evalTerm env v = some x) : meaning (.succeed v) env s = (Exit.success x, s) := by
  unfold meaning; simp only [denote, hx]; rfl

theorem meaning_succeed_none (v : Term) (env : List Val) (s : Stores)
    (hx : evalTerm env v = none) : meaning (.succeed v) env s = (badShapeExit, s) := by
  unfold meaning; simp only [denote, hx]; rfl

theorem meaning_fail_some (e : Term) (env : List Val) (s : Stores) {x : Val}
    (hx : evalTerm env e = some x) :
    meaning (.fail e) env s = (Exit.failure (Cause.fail (errOf x)), s) := by
  unfold meaning; simp only [denote, hx]; rfl

theorem meaning_fail_none (e : Term) (env : List Val) (s : Stores)
    (hx : evalTerm env e = none) : meaning (.fail e) env s = (badShapeExit, s) := by
  unfold meaning; simp only [denote, hx]; rfl

theorem meaning_failCause_some (c : CauseTerm) (env : List Val) (s : Stores) {cause : CauseV}
    (hc : causeOf env c = some cause) :
    meaning (.failCause c) env s = (Exit.failure cause, s) := by
  unfold meaning; simp only [denote, hc]; rfl

theorem meaning_failCause_none (c : CauseTerm) (env : List Val) (s : Stores)
    (hc : causeOf env c = none) : meaning (.failCause c) env s = (badShapeExit, s) := by
  unfold meaning; simp only [denote, hc]; rfl

theorem meaning_yieldError_some (e : Term) (env : List Val) (s : Stores) {x : Val}
    (hx : evalTerm env e = some x) :
    meaning (.yieldError e) env s = (Exit.failure (Cause.fail (errOf x)), s) := by
  unfold meaning; simp only [denote, hx]; rfl

theorem meaning_yieldError_none (e : Term) (env : List Val) (s : Stores)
    (hx : evalTerm env e = none) : meaning (.yieldError e) env s = (badShapeExit, s) := by
  unfold meaning; simp only [denote, hx]; rfl

theorem meaning_sync (t : Term) (env : List Val) (s : Stores) :
    meaning (.sync t) env s = (Exit.success ((evalTerm env t).getD Val.unit), s) := rfl

theorem meaning_suspend (b : NativeEff) (env : List Val) (s : Stores) :
    meaning (.suspend b) env s = meaning b env s := rfl

/-- A `sync` row whose request evaluates and decodes: the store step, with the fallback. -/
theorem meaning_perform_sync (op : NativeOp) (r : Term) (env : List Val) (s : Stores)
    (hkind : (NativeOp.row op).kind = .sync) {x : Val} (hx : evalTerm env r = some x)
    {o : SyncOp} (ho : NativeOp.syncOpOf op x = some o) :
    meaning (.perform op r) env s =
      (match syncOpStep o s with
       | some (s', v) => (Exit.success v, s')
       | none => (Exit.success Val.unit, s)) := by
  unfold meaning
  simp only [denote, hkind, hx, Option.bind, ho]
  rw [Effects.interpret_bind, Effects.interpret_perform, StateT.run_bind]
  rcases h : syncOpStep o s with _ | ⟨s', v⟩
  · simp only [StateT.run, storeHandler, h] <;> rfl
  · simp only [StateT.run, storeHandler, h] <;> rfl

/-- A `sync` row whose request does not evaluate: the defect. -/
theorem meaning_perform_noEval (op : NativeOp) (r : Term) (env : List Val) (s : Stores)
    (hkind : (NativeOp.row op).kind = .sync) (hx : evalTerm env r = none) :
    meaning (.perform op r) env s = (badShapeExit, s) := by
  unfold meaning
  simp only [denote, hkind, hx, Option.bind]
  rfl

/-- A `sync` row whose request evaluates to a value of the wrong shape: the defect. -/
theorem meaning_perform_noDecode (op : NativeOp) (r : Term) (env : List Val) (s : Stores)
    (hkind : (NativeOp.row op).kind = .sync) {x : Val} (hx : evalTerm env r = some x)
    (ho : NativeOp.syncOpOf op x = none) :
    meaning (.perform op r) env s = (badShapeExit, s) := by
  unfold meaning
  simp only [denote, hkind, hx, Option.bind, ho]
  rfl

theorem meaning_bind (a b : NativeEff) (env : List Val) (s : Stores) :
    meaning (.bind a b) env s =
      (match meaning a env s with
       | (Exit.success v, s') => meaning b (env ++ [v]) s'
       | (Exit.failure c, s') => (Exit.failure c, s')) := by
  unfold meaning
  rw [denote, Effects.interpret_bind, StateT.run_bind]
  rcases h : (Effects.interpret storeHandler (denote a env)).run s with ⟨ex, s'⟩
  cases ex <;> rfl

theorem meaning_branch_true (t : Term) (a b : NativeEff) (env : List Val) (s : Stores)
    (ht : evalTerm env t = some (Val.bool true)) :
    meaning (.branch t a b) env s = meaning a env s := by
  unfold meaning; simp only [denote, ht]

theorem meaning_branch_false (t : Term) (a b : NativeEff) (env : List Val) (s : Stores)
    (ht : evalTerm env t = some (Val.bool false)) :
    meaning (.branch t a b) env s = meaning b env s := by
  unfold meaning; simp only [denote, ht]

theorem meaning_branch_bad (t : Term) (a b : NativeEff) (env : List Val) (s : Stores)
    (ht : ∀ flag, evalTerm env t ≠ some (Val.bool flag)) :
    meaning (.branch t a b) env s = (badShapeExit, s) := by
  unfold meaning
  rcases h : evalTerm env t with _ | v
  · simp only [denote, h]; rfl
  · cases v <;> simp only [denote, h] <;> (try rfl)
    rename_i flag
    cases flag <;> exact absurd h (ht _)

theorem meaning_exit (b : NativeEff) (env : List Val) (s : Stores) :
    meaning (.exit b) env s =
      (match meaning b env s with
       | (ex, s') => (Exit.success (reifyExitVal ex), s')) := by
  unfold meaning
  rw [denote, Effects.interpret_bind, StateT.run_bind]
  rcases h : (Effects.interpret storeHandler (denote b env)).run s with ⟨ex, s'⟩
  rfl

theorem meaning_catchCause (b h : NativeEff) (env : List Val) (s : Stores) :
    meaning (.catchCause b h) env s =
      (match meaning b env s with
       | (Exit.success v, s') => (Exit.success v, s')
       | (Exit.failure c, s') => meaning h (env ++ [Val.exitErr c]) s') := by
  unfold meaning
  rw [denote, Effects.interpret_bind, StateT.run_bind]
  rcases hb : (Effects.interpret storeHandler (denote b env)).run s with ⟨ex, s'⟩
  cases ex <;> rfl

theorem meaning_matchCause (b v c : NativeEff) (env : List Val) (s : Stores) :
    meaning (.matchCause b v c) env s =
      (match meaning b env s with
       | (Exit.success x, s') => meaning v (env ++ [x]) s'
       | (Exit.failure cause, s') => meaning c (env ++ [Val.exitErr cause]) s') := by
  unfold meaning
  rw [denote, Effects.interpret_bind, StateT.run_bind]
  rcases hb : (Effects.interpret storeHandler (denote b env)).run s with ⟨ex, s'⟩
  cases ex <;> rfl

theorem meaning_onExit (b f : NativeEff) (env : List Val) (s : Stores) :
    meaning (.onExit b f) env s =
      (match meaning b env s with
       | (ex, s') =>
         match meaning f (env ++ [reifyExitVal ex]) s' with
         | (fex, s'') => (Exit.restoreAfterFinalizer ex (finVoid fex), s'')) := by
  unfold meaning
  rw [denote, Effects.interpret_bind, StateT.run_bind]
  rcases hb : (Effects.interpret storeHandler (denote b env)).run s with ⟨ex, s'⟩
  show (Effects.interpret storeHandler
    (Effects.Program.bind (denote f (env ++ [reifyExitVal ex])) fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex)))).run s' = _
  rw [Effects.interpret_bind, StateT.run_bind]
  dsimp only
  rcases hf : (Effects.interpret storeHandler (denote f (env ++ [reifyExitVal ex]))).run s'
    with ⟨fex, s''⟩
  rfl

/-! ## Separation gate: the denotation carries no closure of the machine -/

example : DecidableEq SyncOp := inferInstance

end Effect4.Program.Denote
