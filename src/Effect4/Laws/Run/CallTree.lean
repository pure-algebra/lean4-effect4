import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Agreement.HostedLoop
import Effect4.Laws.Run.JournalPrefix
import Effect4.Laws.Auto.Obligations
import Effect4.Program.Fold

/-!
# Recorded calls and the admitted call tree

Concept: translation-simulation, R6. Claim: recorded-call-tree-prefix, role inversion.
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

/-- An empty admitted reply tape answers no call.
Consumer: `tree_wait_of_leads`. -/
theorem admitted_tape_empty (table : RowTable) (code : NCode) :
    hostAnswer (admittedTapeHost table) code [] = none := by
  unfold hostAnswer
  split
  · show (if _ : _ < table.length then (none : Option (ExitV × ReplyTape)) else none) = none
    split <;> rfl
  · rfl

/-- Existing local agreement fixes the row and request of a straight call-tree wait.
Consumer: `request_in_tree`; no settled-machine or sufficient-budget premise enters this reader. -/
theorem tree_wait_of_leads (table : RowTable) (program : NativeEff)
    (fragment : StraightRows table program = true) (compileFuel : Nat) (tape : ReplyTape)
    (frame : NFiber) (stores : Stores) (row : Nat) (request : Val)
    (leads : Leads (admittedTapeHost table) program
      (.live (fiberOf (compile program compileFuel) []) Stores.empty) tape
      (.live frame stores) [])
    (call : IsCall frame.current = true)
    (atCall : callOf frame.current = some (row, request)) :
    treeWaits table program tape = .waiting row request := by
  obtain ⟨lower, waiting⟩ := localWaitC_to_rowsB (admittedTapeHost table) program
    (loopedDataRows_of_straightRows program fragment) compileFuel tape [] leads call
    (admitted_tape_empty table frame.current) atCall
  have actual := waiting lower (Nat.le_refl lower)
  rw [denoteRowsB_straight table lower program [] fragment] at actual
  unfold treeWaits
  rw [observeRows_eq_runRowsO, actual]
  rfl

/-- A live native request retains a local call position reached under submitted exits.
Consumer: `request_in_tree`, then the original routing clause.
The unresolved obligation includes arbitrary budget cuts and every permitted control decision.
The existing local agreement theorem supplies the subsequent call-tree observation. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal request_leads (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (call : Call) (token : Nat)
    (request : Program.requestOf s.machine call.fiber token = some (call.op, call.request)) :
    ∃ (i : Nat) (row : Program.Row) (tape : ReplyTape) (frame : NFiber) (stores : Stores),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      Leads (admittedTapeHost s.built.table) s.built.program
        (.live (fiberOf (compile s.built.program s.budget.compileFuel) []) Stores.empty) tape
        (.live frame stores) [] ∧
      IsCall frame.current = true ∧ callOf frame.current = some (i, call.request)

/-- A live native request lies at a wait of the admitted call tree.
The operational prefix obligation remains explicit in `request_leads`. -/
theorem request_in_tree (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (call : Call) (token : Nat)
    (request : Program.requestOf s.machine call.fiber token = some (call.op, call.request)) :
    ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i call.request := by
  obtain ⟨i, row, tape, frame, stores, op, declared, submitted, leads, callAt, requestAt⟩ :=
    request_leads s reached fragment noCause call token request
  exact ⟨i, row, tape, op, declared, submitted,
    tree_wait_of_leads s.built.table s.built.program fragment s.budget.compileFuel tape
      frame stores i call.request leads callAt requestAt⟩

/-- Every accepted call binding names a wait in the admitted call tree.
The tape contains only exits carried by submitted replies in this run.
This is the command-prefix connection consumed by the original routing clause. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem bound_in_tree (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (call : Call) (token : Nat)
    (bound : ((Command.bind call token), .bound) ∈ s.journal.zip s.phases) :
    ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i call.request := by
  obtain ⟨before, actual, built, recordedBefore, request⟩ :=
    bound_request_prefix s reached call token bound
  have admitted : StraightRows before.built.table before.built.program = true := by
    rw [built]
    exact fragment
  have handlers : NoCauseHandler before.built.program = true := by
    rw [built]
    exact noCause
  obtain ⟨i, row, tape, op, declared, submitted, waiting⟩ :=
    request_in_tree before actual admitted handlers call token request
  rw [built] at declared waiting
  refine ⟨i, row, tape, op, declared, ?_, waiting⟩
  intro ex member
  obtain ⟨reply, recorded, completion⟩ := submitted ex member
  exact ⟨reply, recordedBefore _ recorded, completion⟩

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
