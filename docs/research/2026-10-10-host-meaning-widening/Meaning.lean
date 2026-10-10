import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Folds.DenoteRows
import Effect4.Laws.Program.Agreement.Hosted

/-! Research interpretation only. Placement: README.md, budgeted meaning clauses and frontier
observation. The program remains Eff. No compiler, local run, or machine executes this meaning.
The independent candidate covers loops, existing handlers, onExit, and registered data replies.
It has no scope, acquisition, external allocation, interruption, or fork clause. -/
set_option autoImplicit false
namespace Test.HostMeaningWidening
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The existing row-admitting fold, with only the loop clause widened. -/
def LoopedDataRows (table : RowTable) (e : NativeEff) : Bool :=
  cata_eff { StraightRows.alg table with eff_iterate := fun _ _ _ _ _ body => body } e

abbrev Tree (table : RowTable) := Effects.Program (RowsSig table) (Option ExitV)

/-- Generalize the existing thenB shape to the existing row signature. -/
def thenRowsB {table : RowTable} (p : Tree table) (k : ExitV → Tree table) : Tree table :=
  p >>= fun | none => pure none | some ex => k ex

/-- One loop test, using the same cursor contract as iterateStep and generic iter. -/
def loopStep {table : RowTable} (body : List Val → Tree table) (env : List Val)
    (test step result : Term) (cursor : Val) :
    Effects.Program (RowsSig table) (Option ExitV ⊕ Val) :=
  match evalTerm (env ++ [cursor]) test with
  | some (.bool true) => body (env ++ [cursor]) >>= fun
    | none => pure (.inl none)
    | some (.failure cause) => pure (.inl (some (.failure cause)))
    | some (.success value) =>
      match evalTerm (env ++ [cursor, value]) step with
      | some next => pure (.inr next)
      | none => pure (.inl (some badShapeExit))
  | some (.bool false) =>
    pure (.inl (some (match evalTerm (env ++ [cursor]) result with
      | some value => .success value | none => badShapeExit)))
  | _ => pure (.inl (some badShapeExit))

/-- A budgeted candidate, independent of machine execution. Budget counts loop tests, not
machine commands. Every nested body receives the same k. Unsupported syntax stays outside. -/
def denoteRowsB (table : RowTable) (k : Nat) : NativeEff → List Val → Tree table
  | .iterate _ initial test step result body, env =>
    match evalTerm env initial with
    | some cursor => Option.join <$>
        iter (loopStep (denoteRowsB table k body) env test step result) k cursor
    | none => pure (some badShapeExit)
  | .suspend body, env => denoteRowsB table k body env
  | .bind first rest, env => thenRowsB (denoteRowsB table k first env) fun
    | .success value => denoteRowsB table k rest (env ++ [value])
    | .failure cause => pure (some (.failure cause))
  | .select term decision yes no, env =>
    match (evalTerm env term).bind decision.decide with
    | some (true, bound) => denoteRowsB table k yes (env ++ bound.toList)
    | some (false, bound) => denoteRowsB table k no (env ++ bound.toList)
    | none => pure (some badShapeExit)
  | .exit body, env => thenRowsB (denoteRowsB table k body env) fun ex =>
    pure (some (.success (reifyExitVal ex)))
  | .catchCause body handler, env => thenRowsB (denoteRowsB table k body env) fun
    | .success value => pure (some (.success value))
    | .failure cause => denoteRowsB table k handler (env ++ [.exitErr cause])
  | .catchIf test body handler, env => thenRowsB (denoteRowsB table k body env) fun
    | .success value => pure (some (.success value))
    | .failure cause =>
      match caughtErrorValue? env test cause with
      | some value => denoteRowsB table k handler (env ++ [value])
      | none => pure (some (.failure cause))
  | .matchCause body onValue onCause, env => thenRowsB (denoteRowsB table k body env) fun
    | .success value => denoteRowsB table k onValue (env ++ [value])
    | .failure cause => denoteRowsB table k onCause (env ++ [.exitErr cause])
  | .onExit body finalizer, env => thenRowsB (denoteRowsB table k body env) fun ex =>
    thenRowsB (denoteRowsB table k finalizer (env ++ [reifyExitVal ex])) fun fex =>
      pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))
  | leaf, env => some <$> denoteRows table leaf env

/-- Keep both unfinished classes distinct before any observation forgets them. -/
def meaningUnderB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (k : Nat) (e : NativeEff)
    (env : List Val) (stores : Stores) (state : σ) : Option ((Option ExitV × Stores) × σ) :=
  ((Effects.interpret (rowsHandler host.handler) (denoteRowsB table k e env)).run stores).run state

/-- The coarse projection proposed for H8. It deliberately forgets the kind and state of cuts. -/
def coarseRowsB (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val)
    (stores : Stores) (tape : ReplyTape) : Option ((ExitV × Stores) × ReplyTape) :=
  (meaningUnderB (tapeHost table) k e env stores tape).bind fun ((ex, after), rest) =>
    ex.map fun value => ((value, after), rest)

/-- A finite observation; this is not a resumable source configuration. -/
inductive End where
  | finished (exit : ExitV)
  | budget
  | waiting (row : Nat) (request : Val)
deriving DecidableEq

structure Observation (σ : Type) where
  stop : End
  stores : Stores
  host : σ
deriving DecidableEq

/-- Interpret the same free tree, retaining state even when the host gives no answer.
This source-independent fold shares only the existing store algebra and host interface. -/
def observeTree {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ) :
    Tree table → Stores → σ → Observation σ
  | .pure none, stores, state => ⟨.budget, stores, state⟩
  | .pure (some ex), stores, state => ⟨.finished ex, stores, state⟩
  | .vis (.inl op) next, stores, state =>
    let (answer, after) := storeHandler.handle op stores
    observeTree host (next answer) after state
  | .vis (.inr op) next, stores, state =>
    match host.answer op state with
    | none => ⟨.waiting op.1.val op.2, stores, state⟩
    | some (answer, after) => observeTree host (next answer) stores after

end Test.HostMeaningWidening
