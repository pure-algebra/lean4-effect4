import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Auto.Obligations
import Effect4.Program.Fold

/-!
# Recorded calls and the admitted call tree

Concept: translation-simulation, R6. Proposed claim: recorded-call-tree-prefix, role soundness.
Consumer: `Routing.unauthorized_calls_nothing`, through its proved token check in the call tree.
Reach: `StraightRows`, no cause handlers, every recorded script and every command budget.
The claim extends `rows_loop_frontier` to calls observed before a run settles.
It establishes no progress, fairness, fork behavior, scope behavior, or outside-host agreement.
The host boundary remains `docs/core/host-boundary.md`.
-/

set_option autoImplicit false

namespace Effect4.Run.CallTree

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.Api.HostSession (Call)
open Effect4.Api.Runner (Command)

/-- The generated fold rejects each source form that can observe an interruption. -/
def NoCauseHandler (program : NativeEff) : Bool :=
  foldMap_eff true (· && ·) program fun
    | .catchCause _ _ | .matchCause _ _ _ | .onExit _ _ | .exit _ => false
    | _ => true

/-- The reply host that answers a call with the tape's next exit only where the row's own
columns admit it (`externalAdmits`). It is the reply tape as the session reads it. -/
def admittedTapeHost (table : RowTable) : Effects.Comodel (RowSig table) ReplyTape where
  answer op tape :=
    match tape with
    | [] => none
    | ex :: rest => if externalAdmits table op.1.val (.ofExit ex) then some (ex, rest) else none

/-- Where a tree waits under a tape: the row and the request of the call that found the tape
empty, or no wait. -/
def treeWaits (table : RowTable) (program : NativeEff) (T : ReplyTape) : RowsStop :=
  (observeRows (admittedTapeHost table) (some <$> denoteRows table program []) Stores.empty T).stop

/-- Every accepted call binding names a wait in the admitted call tree.
The tape contains only exits carried by submitted replies in this run.
This is the command-prefix connection consumed by the original routing clause. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal bound_in_tree (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (call : Call) (token : Nat)
    (bound : ((Command.bind call token), .bound) ∈ s.journal.zip s.phases) :
    ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i call.request

/-- A sequence's run waits where its first part waits, or where its rest waits after the first
part ended. -/
theorem andThen_eq_waiting {A B σ : Type} {r : RowsEnd A σ} {k : A → Stores → σ → RowsEnd B σ}
    {i : Nat} {v : Val} {s : Stores} {st : σ} (h : r.andThen k = .waiting i v s st) :
    r = .waiting i v s st ∨ ∃ a s' st', r = .done a s' st' ∧ k a s' st' = .waiting i v s st := by
  cases r with
  | done a s' st' => exact Or.inr ⟨a, s', st', rfl, h⟩
  | waiting i' v' s' st' =>
    cases h
    exact Or.inl rfl

/-- The detailed run of the tree's own bind. -/
theorem runRowsO_pbind {table : RowTable} {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    {A B : Type} (p : Effects.Program (RowsSig table) A)
    (k : A → Effects.Program (RowsSig table) B) (s : Stores) (st : σ) :
    runRowsO host (Effects.Program.bind p k) s st =
      (runRowsO host p s st).andThen fun a s st => runRowsO host (k a) s st :=
  runRowsO_bind host k p s st

/-- Where a tree waits, read off its detailed run. -/
theorem treeWaits_eq (table : RowTable) (program : NativeEff) (T : ReplyTape) :
    treeWaits table program T =
      (match runRowsO (admittedTapeHost table) (denoteRows table program []) Stores.empty T with
        | .done a _ _ => RowsStop.finished a
        | .waiting i v _ _ => RowsStop.waiting i v) := by
  unfold treeWaits
  rw [observeRows_eq_runRowsO]
  show (RowsEnd.observe (runRowsO (admittedTapeHost table)
    (Effects.Program.bind (denoteRows table program []) fun a => Effects.Program.pure (some a))
    Stores.empty T)).stop = _
  rw [runRowsO_pbind]
  cases runRowsO (admittedTapeHost table) (denoteRows table program []) Stores.empty T <;> rfl

/-- The admitted reply host at a call: the tape's next exit where the row admits it, else a
wait. -/
theorem runRowsO_admitted_vis {table : RowTable} (op : (RowSig table).Op)
    (k : ExitV → Effects.Program (RowsSig table) ExitV) (s : Stores) (ex : ExitV)
    (rest : ReplyTape) :
    runRowsO (admittedTapeHost table) (.vis (.inr op) k) s (ex :: rest) =
      if externalAdmits table op.1.val (.ofExit ex) then
        runRowsO (admittedTapeHost table) (k ex) s rest
      else .waiting op.1.val op.2 s (ex :: rest) := by
  rw [runRowsO.eq_def]
  dsimp only
  unfold admittedTapeHost
  dsimp only
  cases externalAdmits table op.1.val (.ofExit ex) with
  | true => rfl
  | false => rfl

/-- A handler's continuation, as `denoteRows` writes it for `catchIf`. -/
def catchK (table : RowTable) (env : List Val) (test : Term) (h : NativeEff) :
    ExitV → Effects.Program (RowsSig table) ExitV
  | Exit.success v => pure (Exit.success v)
  | Exit.failure cause =>
    match caughtErrorValue? env test cause with
    | some value => denoteRows table h (env ++ [value])
    | none => pure (Exit.failure cause)

/-- A handler that answers a term never waits. -/
theorem catchK_done (table : RowTable) (env : List Val) (test response : Term) (a : ExitV)
    (s : Stores) (st : ReplyTape) :
    ∃ x s' st', runRowsO (admittedTapeHost table)
      (catchK table env test (.succeed response) a) s st = .done x s' st' := by
  cases a with
  | success v => exact ⟨_, _, _, rfl⟩
  | failure cause =>
    simp only [catchK]
    cases caughtErrorValue? env test cause with
    | some value => exact ⟨_, _, _, rfl⟩
    | none => exact ⟨_, _, _, rfl⟩

/-- A response after a sequence never waits. -/
theorem seqSucceed_done (table : RowTable) (term : Term) (a : ExitV) (s : Stores)
    (st : ReplyTape) :
    ∃ x s' st', runRowsO (admittedTapeHost table)
      (seqRows (fun v => denoteRows table (.succeed term) ([] ++ [v])) a) s st =
        .done x s' st' := by
  cases a with
  | success v => exact ⟨_, _, _, rfl⟩
  | failure cause => exact ⟨_, _, _, rfl⟩

end Effect4.Run.CallTree
