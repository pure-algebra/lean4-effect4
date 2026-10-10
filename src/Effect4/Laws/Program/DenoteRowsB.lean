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

/-- Over a program that always finishes, `thenOpt` is the plain sequence. -/
theorem thenOpt_map_some (p : Effects.Program S ExitV)
    (rest : ExitV → Effects.Program S (Option ExitV)) :
    thenOpt (some <$> p) rest = p >>= rest := by
  unfold thenOpt
  rw [bind_map_left]

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
proof_goal hostRunB_stable {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    {k k' : Nat} (hk : k ≤ k') (e : NativeEff) (env : List Val) (s : Stores) (st : σ)
    {ex : ExitV} {r : Stores × σ} (h : hostRunB host k e env s st = some (some ex, r)) :
    hostRunB host k' e env s st = some (some ex, r)

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
connector): no budget is read. A step of the loop session claim (`h8_loopedRows`), whose
straight instance is `denoteRows_eq_session`. -/
@[semantics "translation-simulation" (requirement := R2)]
proof_goal denoteRowsB_straight (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val)
    (h : StraightRows table e = true) :
    denoteRowsB table k e env = some <$> denoteRows table e env

/-- **On `Looped` the budgeted meaning is `denoteB`, injected on the left** (Q1): a host-free
loop calls no row, so every budget theorem of `denoteB` is a corollary. A step of the loop
session claim (`h8_loopedRows`). -/
@[semantics "translation-simulation" (requirement := R2)]
proof_goal denoteRowsB_looped (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val)
    (h : Looped e = true) :
    denoteRowsB table k e env = Effects.Program.inl (T := RowSig table) (denoteB k e env)

/-- **The detailed observation projects to the host meaning** (Q3): a finished tree to its exit,
a budget cut to `none` inside with its stores and host state, a wait to the outer `none`. A step
of the frontier claim (`docs/research/2026-10-10-host-meaning-widening/README.md` Q4) and of
`h8_loopedRows`. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal observeRows_project {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (t : Effects.Program (RowsSig table) (Option ExitV))
    (s : Stores) (state : σ) :
    ((Effects.interpret (rowsHandler host.handler) t).run s).run state =
      (observeRows host t s state).project

end Effect4.Program.Denote
