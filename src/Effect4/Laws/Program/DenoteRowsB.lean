import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Folds.DenoteRows
import Effect4.Laws.Program.HostRuns
import Effect4.Laws.Auto.Semantics

/-!
# Program.DenoteRowsB: host rows inside loops, at a budget

Slice L1 of `docs/research/2026-10-10-host-meaning-widening/README.md` (§1.2, §5.1 Q1 and Q3).
`denoteRowsB table k e env` is the call tree of a program over the stores and its host rows,
with loops cut at the budget `k`: `denoteRows`'s arms, `denoteB`'s loop arm, and `none` for a
program the budget leaves unfinished. The program stays `Eff`; no compiler, local run or machine
runs this meaning. It has no scope, acquisition, external allocation, interruption or fork arm.

The budget counts the tests of each loop invocation, the last false test included, and every
nested body gets the same `k`, as in `denoteB`. It is not compile fuel, a machine step count,
session command fuel or a driver round.

The sequence and the loop round are `denoteB`'s, generic over the signature (`thenOpt`,
`loopStep`): `thenB` and `iterateStep` are their store-signature instances by definition. Two
connectors place the meaning (Q1): on `StraightRows` it is `denoteRows` finished
(`denoteRowsB_straight`), and on `Looped` it is `denoteB` injected (`denoteRowsB_looped`).
`observeRows` (Q3) keeps what the host meaning's outer `Option` forgets at a wait: the stores,
the host state and the waiting row and request (`observeRows_project`).

Placement: concept `translation-simulation` (`docs/core/semantics.md`); the connectors are steps
of `rows-denotation-straight` and of the loop session claim (`h8_loopedRows`,
`Laws/Api/SessionMeaningLoop.lean`), requirements R2 and R6. They establish no machine relation,
no host progress and no table extension.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-! ## The row fragment with loops -/

/-- **The row-admitting fragment with loops**: `StraightRows`'s algebra with its loop clause
widened to the body's. It keeps the host-row admission (`dataRow`) that `LoopedRows` does not
check, so a missing row or a handle answer stays outside. -/
def LoopedDataRows (table : RowTable) (e : NativeEff) : Bool :=
  cata_eff { StraightRows.alg table with eff_iterate := fun _ _ _ _ _ body => body } e

/-! ## Sequencing and one loop round, at any signature -/

section Generic

variable {S : Effects.Signature.{0, 0}}

/-- Sequencing at a budget: an unfinished first program ends the whole unfinished. -/
def thenOpt (p : Effects.Program S (Option ExitV))
    (rest : ExitV → Effects.Program S (Option ExitV)) : Effects.Program S (Option ExitV) :=
  p >>= fun
    | none => pure none
    | some ex => rest ex

/-- One round of a loop at the cursor `c`, in `iter`'s shape: `iterateStep` at any signature. -/
def loopStep (body : List Val → Effects.Program S (Option ExitV)) (env : List Val)
    (test step result : Term) (c : Val) : Effects.Program S (Option ExitV ⊕ Val) :=
  match evalTerm (env ++ [c]) test with
  | some (Val.bool true) => body (env ++ [c]) >>= fun
    | none => pure (.inl none)
    | some (Exit.failure cause) => pure (.inl (some (Exit.failure cause)))
    | some (Exit.success a) =>
      match evalTerm (env ++ [c, a]) step with
      | some c' => pure (.inr c')
      | none => pure (.inl (some badShapeExit))
  | some (Val.bool false) =>
    pure (.inl (some (match evalTerm (env ++ [c]) result with
      | some v => Exit.success v
      | none => badShapeExit)))
  | _ => pure (.inl (some badShapeExit))

/-- `map_bind` at `Effects.Program.bind`, the form `denoteRows` writes its sequences in. -/
theorem map_programBind {A B C : Type} (f : B → C) (p : Effects.Program S A)
    (g : A → Effects.Program S B) : f <$> p.bind g = p >>= fun a => f <$> g a :=
  map_bind f p g

/-- Over a program that always finishes, `thenOpt` is the plain sequence. -/
theorem thenOpt_map_some (p : Effects.Program S ExitV)
    (rest : ExitV → Effects.Program S (Option ExitV)) :
    thenOpt (some <$> p) rest = p >>= rest := by
  unfold thenOpt
  rw [bind_map_left]

/-! ### The approximation order across budgets -/

/-- Approximation is a congruence for a bind whose continuation keeps a cut a cut. A step of
`denoteRowsB_approx`. -/
theorem approx_bind {A B : Type} {p q : Effects.Program S (Option A)}
    {F G : Option A → Effects.Program S (Option B)} (h : Effects.Program.Approx p q)
    (hcut : F none = pure none) (hk : ∀ a, Effects.Program.Approx (F (some a)) (G (some a))) :
    Effects.Program.Approx (p >>= F) (q >>= G) := by
  induction h with
  | cut other =>
    show Effects.Program.Approx (F none) _
    rw [hcut]
    exact .cut _
  | done v => exact hk v
  | vis op _ ih => exact .vis op ih

/-- `thenOpt` is monotone in both its parts. A step of `denoteRowsB_approx`. -/
theorem approx_thenOpt {p q : Effects.Program S (Option ExitV)}
    {f g : ExitV → Effects.Program S (Option ExitV)} (h : Effects.Program.Approx p q)
    (hk : ∀ ex, Effects.Program.Approx (f ex) (g ex)) :
    Effects.Program.Approx (thenOpt p f) (thenOpt q g) :=
  approx_bind h rfl hk

/-- **A loop at a budget approximates the same loop at a larger budget over a larger body.** A
step of `denoteRowsB_approx`. -/
theorem approx_iter_loopStep {body body' : List Val → Effects.Program S (Option ExitV)}
    (hb : ∀ env, Effects.Program.Approx (body env) (body' env)) (env : List Val)
    (test step result : Term) :
    ∀ {k k' : Nat}, k ≤ k' → ∀ c : Val,
      Effects.Program.Approx (Option.join <$> iter (loopStep body env test step result) k c)
        (Option.join <$> iter (loopStep body' env test step result) k' c)
  | 0, _, _, _ => .cut _
  | _ + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero _)
  | k + 1, j + 1, h, c => by
    rw [iter_succ, iter_succ, map_bind, map_bind]
    unfold loopStep
    split
    · rw [bind_assoc, bind_assoc]
      refine approx_bind (hb _) rfl fun o => ?_
      cases o with
      | failure cause => exact .refl _
      | success a =>
        dsimp only
        cases evalTerm (env ++ [c, a]) step with
        | none => exact .refl _
        | some c' => exact approx_iter_loopStep hb env test step result (Nat.le_of_succ_le_succ h) c'
    · exact .refl _
    · exact .refl _

end Generic

theorem thenB_eq_thenOpt : @thenB = @thenOpt StoreSig := rfl

theorem iterateStep_eq_loopStep : @iterateStep = @loopStep StoreSig := rfl

/-! ## The budgeted meaning -/

/-- **The call tree of a program over the stores and its host rows, loops cut at a budget.**
Each arm is `denoteRows`'s, with `thenOpt` for the sequence, and the loop arm is `denoteB`'s.
`none` is a program the budget leaves unfinished. A finalizer starts on a failure and never on
a budget cut. -/
def denoteRowsB (table : RowTable) (k : Nat) :
    NativeEff → List Val → Effects.Program (RowsSig table) (Option ExitV)
  | .iterate _ initial test step result body, env =>
    match evalTerm env initial with
    | some c₀ => Option.join <$> iter (loopStep (denoteRowsB table k body) env test step result) k c₀
    | none => pure (some badShapeExit)
  | .suspend b, env => denoteRowsB table k b env
  | .bind a b, env => thenOpt (denoteRowsB table k a env) fun
    | Exit.success v => denoteRowsB table k b (env ++ [v])
    | Exit.failure c => pure (some (Exit.failure c))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteRowsB table k a (env ++ bound.toList)
    | some (false, bound) => denoteRowsB table k b (env ++ bound.toList)
    | none => pure (some badShapeExit)
  | .exit b, env => thenOpt (denoteRowsB table k b env) fun ex =>
    pure (some (Exit.success (reifyExitVal ex)))
  | .catchCause b h, env => thenOpt (denoteRowsB table k b env) fun
    | Exit.success v => pure (some (Exit.success v))
    | Exit.failure c => denoteRowsB table k h (env ++ [Val.exitErr c])
  | .catchIf test b h, env => thenOpt (denoteRowsB table k b env) fun
    | Exit.success v => pure (some (Exit.success v))
    | Exit.failure cause =>
      match caughtErrorValue? env test cause with
      | some value => denoteRowsB table k h (env ++ [value])
      | none => pure (some (Exit.failure cause))
  | .matchCause b v c, env => thenOpt (denoteRowsB table k b env) fun
    | Exit.success x => denoteRowsB table k v (env ++ [x])
    | Exit.failure cause => denoteRowsB table k c (env ++ [Val.exitErr cause])
  | .onExit b f, env => thenOpt (denoteRowsB table k b env) fun ex =>
    thenOpt (denoteRowsB table k f (env ++ [reifyExitVal ex])) fun fex =>
      pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))
  | e, env => some <$> denoteRows table e env

/-- **The tree at a budget approximates the tree at every larger budget** (the step of Q2): each
arm is a congruence of `Effects.Program.Approx`, and the loop arm is `approx_iter_loopStep`. -/
theorem denoteRowsB_approx (table : RowTable) {k k' : Nat} (hk : k ≤ k') :
    ∀ (e : NativeEff) (env : List Val),
      Effects.Program.Approx (denoteRowsB table k e env) (denoteRowsB table k' e env)
  | .iterate _ initial test step result body, env => by
    rw [denoteRowsB, denoteRowsB]
    cases evalTerm env initial with
    | none => exact .refl _
    | some c₀ =>
      exact approx_iter_loopStep (fun env' => denoteRowsB_approx table hk body env') env test step
        result hk c₀
  | .suspend b, env => denoteRowsB_approx table hk b env
  | .bind a b, env =>
    approx_thenOpt (denoteRowsB_approx table hk a env) fun
      | .success v => denoteRowsB_approx table hk b (env ++ [v])
      | .failure _ => .refl _
  | .select t d a b, env => by
    rw [denoteRowsB, denoteRowsB]
    rcases (evalTerm env t).bind d.decide with _ | ⟨_ | _, bound⟩
    · exact .refl _
    · exact denoteRowsB_approx table hk b _
    · exact denoteRowsB_approx table hk a _
  | .exit b, env => approx_thenOpt (denoteRowsB_approx table hk b env) fun _ => .refl _
  | .catchCause b h, env =>
    approx_thenOpt (denoteRowsB_approx table hk b env) fun
      | .success _ => .refl _
      | .failure c => denoteRowsB_approx table hk h (env ++ [Val.exitErr c])
  | .catchIf test b h, env =>
    approx_thenOpt (denoteRowsB_approx table hk b env) fun
      | .success _ => .refl _
      | .failure cause => by
        dsimp only
        cases caughtErrorValue? env test cause with
        | none => exact .refl _
        | some value => exact denoteRowsB_approx table hk h _
  | .matchCause b v c, env =>
    approx_thenOpt (denoteRowsB_approx table hk b env) fun
      | .success x => denoteRowsB_approx table hk v (env ++ [x])
      | .failure cause => denoteRowsB_approx table hk c (env ++ [Val.exitErr cause])
  | .onExit b f, env =>
    approx_thenOpt (denoteRowsB_approx table hk b env) fun ex =>
      approx_thenOpt (denoteRowsB_approx table hk f (env ++ [reifyExitVal ex])) fun _ => .refl _
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ | .perform _ _, _ | .gen _, _
  | .uninterruptible _, _ | .interruptible _, _ | .yieldNow _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _ | .restore _ _, _ | .defs _ _ _, _
  | .invoke _ _ _, _ => .refl _

/-- **The budgeted meaning under a host**: the exit or the budget's cut, the stores and the
host's state. The outer `none` is a call the host does not answer; it forgets the stores and the
host state there, which `observeRows` keeps. -/
def meaningUnderB {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (k : Nat) (e : NativeEff) (env : List Val) (s : Stores) (state : σ) :
    Option ((Option ExitV × Stores) × σ) :=
  ((Effects.interpret (rowsHandler host.handler) (denoteRowsB table k e env)).run s).run state

/-- **The run of the budgeted call tree under a host**, as `hostRun` runs `denoteRows`: the exit or
the budget's cut, with the stores and the host's state. `none`: a call got no answer. -/
def hostRunB {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    Option (Option ExitV × (Stores × σ)) :=
  (rowsHost host).run (denoteRowsB table k e env) (s, st)

/-- The meaning under a host is the host's run, regrouped (`interpret_rowsHandler`). -/
theorem meaningUnderB_eq_hostRunB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (k : Nat) (e : NativeEff) (env : List Val)
    (s : Stores) (st : σ) :
    meaningUnderB host k e env s st =
      (hostRunB host k e env s st).map fun r => ((r.1, r.2.1), r.2.2) :=
  interpret_rowsHandler host.handler (denoteRowsB table k e env) s st

/-- **A finished approximant stays finished at every larger budget** (Q2): the same exit, stores
and host state. A step of the loop closing step (`meaning_settledB`,
`Agreement/HostedLoop.lean`), which turns one finishing budget into H8's eventual bound. It says
nothing of an unfinished approximant. The route: the tree at `k` approximates the tree at
`k'` (`Effects.Program.Approx`), and an approximant that finishes against a host finishes the same
way as what it approximates (`Effects.Comodel.run_approx`). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem hostRunB_stable {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    {k k' : Nat} (hk : k ≤ k') (e : NativeEff) (env : List Val) (s : Stores) (st : σ)
    {ex : ExitV} {r : Stores × σ} (h : hostRunB host k e env s st = some (some ex, r)) :
    hostRunB host k' e env s st = some (some ex, r) :=
  Effects.Comodel.run_approx (rowsHost host) (denoteRowsB_approx table hk e env) h

/-- **The coarse observation of H8 on loops**: a finished program's exit, stores and unread
reply tape, and `none` for every unfinished one, budget cut or wait alike. -/
def coarseRowsB (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val) (s : Stores)
    (tape : ReplyTape) : Option ((ExitV × Stores) × ReplyTape) :=
  (meaningUnderB (tapeHost table) k e env s tape).bind fun ((ex, after), rest) =>
    ex.map fun value => ((value, after), rest)

/-! ## The detailed observation -/

/-- How a budgeted tree stops under a host: finished, cut by the budget, or waiting on a row. -/
inductive RowsStop where
  | finished (exit : ExitV)
  | budget
  | waiting (row : Nat) (request : Val)
deriving DecidableEq

/-- A finite observation of a budgeted tree: how it stops, the stores and the host's state. It is
not a resumable configuration: a budget cut keeps no loop cursor and no residual body. -/
structure RowsObservation (σ : Type) where
  stop : RowsStop
  stores : Stores
  host : σ

/-- The host meaning's view of an observation: a wait forgets its stores and host state. -/
def RowsObservation.project {σ : Type} (o : RowsObservation σ) :
    Option ((Option ExitV × Stores) × σ) :=
  match o.stop with
  | .finished ex => some ((some ex, o.stores), o.host)
  | .budget => some ((none, o.stores), o.host)
  | .waiting _ _ => none

/-- **The tree run under a host, keeping the state at a wait**: the store handler on the left,
the host on the right, as `rowsHandler` routes them. -/
def observeRows {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ) :
    Effects.Program (RowsSig table) (Option ExitV) → Stores → σ → RowsObservation σ
  | .pure none, s, state => ⟨.budget, s, state⟩
  | .pure (some ex), s, state => ⟨.finished ex, s, state⟩
  | .vis (.inl op) next, s, state =>
    observeRows host (next (storeHandler.handle op s).1) (storeHandler.handle op s).2 state
  | .vis (.inr op) next, s, state =>
    match host.answer op state with
    | none => ⟨.waiting op.1.val op.2, s, state⟩
    | some (answer, after) => observeRows host (next answer) s after

/-! ## The connectors (Q1, Q3) -/

/-- **On `StraightRows` the budgeted meaning is `denoteRows`, finished** (Q1, the conservative
connector): no budget is read. Each arm is `thenOpt_map_some` and the induction. Claim
`rows-loop-straight`. -/
@[semantics "translation-simulation" (requirement := R2)]
theorem denoteRowsB_straight (table : RowTable) (k : Nat) :
    ∀ (e : NativeEff) (env : List Val), StraightRows table e = true →
      denoteRowsB table k e env = some <$> denoteRows table e env
  | .succeed _, _, _ | .fail _, _, _ | .failCause _, _, _ | .sync _, _, _ | .perform _ _, _, _ => rfl
  | .suspend b, env, h => by
    rw [denoteRowsB, denoteRows]
    exact denoteRowsB_straight table k b env h
  | .bind a b, env, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    rw [denoteRowsB, denoteRows, denoteRowsB_straight table k a env ha, thenOpt_map_some]
    rw [map_programBind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success v => exact denoteRowsB_straight table k b _ hb
    | failure c => rfl
  | .select t d a b, env, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    rw [denoteRowsB, denoteRows]
    rcases (evalTerm env t).bind d.decide with _ | ⟨_ | _, bound⟩
    · rfl
    · exact denoteRowsB_straight table k b _ hb
    · exact denoteRowsB_straight table k a _ ha
  | .exit b, env, h => by
    rw [denoteRowsB, denoteRows, denoteRowsB_straight table k b env h, thenOpt_map_some]
    rw [map_programBind]
    rfl
  | .catchCause b hd, env, h => by
    obtain ⟨hb, hh⟩ : StraightRows table b = true ∧ StraightRows table hd = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    rw [denoteRowsB, denoteRows, denoteRowsB_straight table k b env hb, thenOpt_map_some]
    rw [map_programBind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success v => rfl
    | failure c => exact denoteRowsB_straight table k hd _ hh
  | .catchIf test b hd, env, h => by
    obtain ⟨hb, hh⟩ : StraightRows table b = true ∧ StraightRows table hd = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    rw [denoteRowsB, denoteRows, denoteRowsB_straight table k b env hb, thenOpt_map_some]
    rw [map_programBind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success v => rfl
    | failure cause =>
      dsimp only
      cases caughtErrorValue? env test cause with
      | none => rfl
      | some value => exact denoteRowsB_straight table k hd _ hh
  | .matchCause b v c, env, h => by
    obtain ⟨hb, hv, hc⟩ :
        StraightRows table b = true ∧ StraightRows table v = true ∧ StraightRows table c = true := by
      simpa only [StraightRows, Bool.and_eq_true, and_assoc] using h
    rw [denoteRowsB, denoteRows, denoteRowsB_straight table k b env hb, thenOpt_map_some]
    rw [map_programBind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success x => exact denoteRowsB_straight table k v _ hv
    | failure cause => exact denoteRowsB_straight table k c _ hc
  | .onExit b f, env, h => by
    obtain ⟨hb, hf⟩ : StraightRows table b = true ∧ StraightRows table f = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    rw [denoteRowsB, denoteRows, denoteRowsB_straight table k b env hb, thenOpt_map_some]
    rw [map_programBind]
    refine bind_congr fun ex => ?_
    show thenOpt (denoteRowsB table k f _) _ = some <$> (denoteRows table f _).bind _
    rw [denoteRowsB_straight table k f _ hf, thenOpt_map_some, map_programBind]
    rfl
  | .gen _, _, h | .uninterruptible _, _, h | .interruptible _, _, h | .yieldNow _, _, h
  | .awaitFiber _ _, _, h | .withFiber _, _, h | .scoped _, _, h | .acquireRelease _ _, _, h
  | .provideLayer _ _ _, _, h | .service _, _, h | .provideService _ _ _, _, h
  | .iterate _ _ _ _ _ _, _, h | .restore _ _, _, h | .defs _ _ _, _, h | .invoke _ _ _, _, h => by
    simp only [StraightRows, Bool.false_eq_true] at h

/-! ### The left injection commutes with the sequence and the loop -/

section Inject

variable {S : Effects.Signature.{0, 0}} {T : Effects.Signature.{0, 0}}

theorem inl_map {A B : Type} (f : A → B) (p : Effects.Program S A) :
    Effects.Program.inl (T := T) (f <$> p) = f <$> Effects.Program.inl (T := T) p :=
  Effects.Program.inl_bind p _

theorem inl_thenOpt (p : Effects.Program S (Option ExitV))
    (rest : ExitV → Effects.Program S (Option ExitV)) :
    Effects.Program.inl (T := T) (thenOpt p rest) =
      thenOpt (Effects.Program.inl (T := T) p) fun ex => Effects.Program.inl (T := T) (rest ex) := by
  unfold thenOpt
  show Effects.Program.inl (p.bind _) = _
  rw [Effects.Program.inl_bind]
  refine congrArg (Effects.Program.bind _) (funext fun o => ?_)
  cases o <;> rfl

theorem inl_iter {X Y : Type} (f : X → Effects.Program S (Y ⊕ X)) :
    ∀ (k : Nat) (x : X), Effects.Program.inl (T := T) (iter f k x) =
      iter (fun x => Effects.Program.inl (T := T) (f x)) k x
  | 0, _ => rfl
  | k + 1, x => by
    rw [iter_succ, iter_succ]
    show Effects.Program.inl ((f x).bind _) = _
    rw [Effects.Program.inl_bind]
    refine congrArg (Effects.Program.bind _) (funext fun r => ?_)
    cases r with
    | inl y => rfl
    | inr x' => exact inl_iter f k x'

theorem inl_loopStep (body : List Val → Effects.Program S (Option ExitV)) (env : List Val)
    (test step result : Term) (c : Val) :
    Effects.Program.inl (T := T) (loopStep body env test step result c) =
      loopStep (fun env' => Effects.Program.inl (T := T) (body env')) env test step result c := by
  unfold loopStep
  split
  · show Effects.Program.inl ((body _).bind _) = _
    rw [Effects.Program.inl_bind]
    refine congrArg (Effects.Program.bind _) (funext fun o => ?_)
    rcases o with _ | (a | _)
    · rfl
    · dsimp only
      cases evalTerm (env ++ [c, a]) step <;> rfl
    · rfl
  · rfl
  · rfl

end Inject

/-- A leaf of both fragments: `denoteRows_straight`, read through `leafB`. A step of
`denoteRowsB_looped`. -/
theorem denoteRowsB_looped_leaf (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val)
    (hc : composite e = false) (hs : Straight e = true)
    (hrow : denoteRowsB table k e env = some <$> denoteRows table e env) :
    denoteRowsB table k e env = Effects.Program.inl (T := RowSig table) (denoteB k e env) := by
  rw [hrow, denoteB_leaf k e env hc, leafB, if_pos hs, inl_map, denoteRows_straight table e env hs]

/-- **On `Looped` the budgeted meaning is `denoteB`, injected on the left** (Q1): a host-free
loop calls no row. The left injection commutes with each arm (`inl_thenOpt`, `inl_iter`,
`inl_loopStep`), and a leaf is `denoteRows_straight`. Claim `rows-loop-looped`. -/
@[semantics "translation-simulation" (requirement := R2)]
theorem denoteRowsB_looped (table : RowTable) (k : Nat) :
    ∀ (e : NativeEff) (env : List Val), Looped e = true →
      denoteRowsB table k e env = Effects.Program.inl (T := RowSig table) (denoteB k e env)
  | .iterate _ initial test step result body, env, h => by
    rw [denoteRowsB, denoteB]
    cases evalTerm env initial with
    | none => rfl
    | some c₀ =>
      dsimp only
      rw [inl_map, inl_iter]
      congr 1
      refine iter_congr _ _ (fun c => ?_) k c₀
      rw [iterateStep_eq_loopStep, inl_loopStep]
      congr 1
      funext env'
      exact denoteRowsB_looped table k body env' (Looped.iterate h)
  | .suspend b, env, h => by
    rw [denoteRowsB, denoteB]
    exact denoteRowsB_looped table k b env (Looped.suspend h)
  | .bind a b, env, h => by
    rw [denoteRowsB, denoteB, thenB_eq_thenOpt, inl_thenOpt,
      denoteRowsB_looped table k a env (Looped.bind h).1]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteRowsB_looped table k b _ (Looped.bind h).2
    | failure c => rfl
  | .select t d a b, env, h => by
    rw [denoteRowsB, denoteB]
    rcases (evalTerm env t).bind d.decide with _ | ⟨_ | _, bound⟩
    · rfl
    · exact denoteRowsB_looped table k b _ (Looped.select h).2
    · exact denoteRowsB_looped table k a _ (Looped.select h).1
  | .exit b, env, h => by
    rw [denoteRowsB, denoteB, thenB_eq_thenOpt, inl_thenOpt,
      denoteRowsB_looped table k b env (Looped.exit h)]
    rfl
  | .catchCause b hd, env, h => by
    rw [denoteRowsB, denoteB, thenB_eq_thenOpt, inl_thenOpt,
      denoteRowsB_looped table k b env (Looped.catchCause h).1]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteRowsB_looped table k hd _ (Looped.catchCause h).2
  | .matchCause b v c, env, h => by
    rw [denoteRowsB, denoteB, thenB_eq_thenOpt, inl_thenOpt,
      denoteRowsB_looped table k b env (Looped.matchCause h).1]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteRowsB_looped table k v _ (Looped.matchCause h).2.1
    | failure cause => exact denoteRowsB_looped table k c _ (Looped.matchCause h).2.2
  | .onExit b f, env, h => by
    rw [denoteRowsB, denoteB, thenB_eq_thenOpt, inl_thenOpt,
      denoteRowsB_looped table k b env (Looped.onExit h).1]
    congr 1
    funext ex
    rw [inl_thenOpt, denoteRowsB_looped table k f _ (Looped.onExit h).2]
    rfl
  | .succeed _, env, _ => denoteRowsB_looped_leaf table k _ env rfl rfl rfl
  | .fail _, env, _ => denoteRowsB_looped_leaf table k _ env rfl rfl rfl
  | .failCause _, env, _ => denoteRowsB_looped_leaf table k _ env rfl rfl rfl
  | .sync _, env, _ => denoteRowsB_looped_leaf table k _ env rfl rfl rfl
  | .perform op r, env, h => denoteRowsB_looped_leaf table k (.perform op r) env rfl h rfl
  | .gen _, _, h | .uninterruptible _, _, h | .interruptible _, _, h | .yieldNow _, _, h
  | .awaitFiber _ _, _, h | .withFiber _, _, h | .scoped _, _, h | .acquireRelease _ _, _, h
  | .provideLayer _ _ _, _, h | .service _, _, h | .provideService _ _ _, _, h
  | .catchIf _ _ _, _, h | .restore _ _, _, h | .defs _ _ _, _, h | .invoke _ _ _, _, h => by
    simp only [Looped, Bool.false_eq_true] at h

/-- **The detailed observation projects to the host meaning** (Q3): a finished tree to its exit,
a budget cut to `none` inside with its stores and host state, a wait to the outer `none`. A step
of the frontier claim (`docs/research/2026-10-10-host-meaning-widening/README.md` Q4). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem observeRows_project {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) :
    ∀ (t : Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (state : σ),
      ((Effects.interpret (rowsHandler host.handler) t).run s).run state =
        (observeRows host t s state).project
  | .pure none, _, _ => rfl
  | .pure (some _), _, _ => rfl
  | .vis (.inl o) k, s, state =>
    observeRows_project host (k (storeStep o s).1) (storeStep o s).2 state
  | .vis (.inr o) k, s, state => by
    rcases h : host.answer o state with _ | ⟨a, state'⟩
    · have hL : ((Effects.interpret (rowsHandler host.handler) (.vis (.inr o) k)).run s).run state =
          none := by
        show Option.bind (Option.bind (host.answer o state) _) _ = none
        rw [h]
        rfl
      rw [hL]
      conv => rhs; rw [observeRows.eq_def]
      dsimp only
      rw [h]
      rfl
    · have hL : ((Effects.interpret (rowsHandler host.handler) (.vis (.inr o) k)).run s).run state =
          ((Effects.interpret (rowsHandler host.handler) (k a)).run s).run state' := by
        show Option.bind (Option.bind (host.answer o state) _) _ = _
        rw [h]
        rfl
      rw [hL, observeRows_project host (k a) s state']
      conv => rhs; rw [observeRows.eq_def]
      dsimp only
      rw [h]

end Effect4.Program.Denote
