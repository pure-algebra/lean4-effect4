import Effect4.Machine.Scope

/-!
# Scope-close request/response execution

Owner: the residual execution of existing `Scope.closeExitsM`.
Frozen packet: `test/contracts/scope-machine.contract.md` at `e5a2bdb`.
Assurance: `docs/SCOPE-DAG.md`, Scope close stepping, contributing to the
Scope side of `docs/TRACE-DAG.md`'s still-open frame-simulation edge.

A machine stores operation names, the original closing exit, pending work and
actual captured replies. It closes the retained Scope before exposing a
request. An external caller may drive `advance`/`request?`/`respond`; the
explicit-state convenience interpreter answers one request at a time.
No callback, whole-run oracle, source graph or host object is stored.

The ten local theorems retain the complete machine and service state, including
failure, at every prefix and at the existing sequential fold's completion.
Both Scope strategy labels are retained; this driver does not implement
parallel finalizer scheduling. General region compilation, arbitrary-program
finalizer evaluation, frame/host agreement and interruption remain separate
obligations. Existing Scope, Exit and Cause are consumed without alteration.
-/

namespace Effect4.ScopeMachine

universe u v
/-- Administrative phase of one close; a waiting operation has no reply yet. -/
inductive Phase (φ : Type u) where
  | ready
  | waiting (finalizer : φ)
  | complete
deriving DecidableEq

/-- First-order close residual. The captured pairs are the canonical ordered journal. -/
structure State (κ φ : Type u) (β : Type v) (ε δ ι α : Type u) where
  scope : Scope κ φ β ε δ ι α
  original : Exit β ε δ ι α
  pending : List φ
  captured : List (φ × Exit Unit ε δ ι α)
  phase : Phase φ
deriving DecidableEq

variable {κ φ : Type u} {β : Type v} {ε δ ι α σ : Type u}
/-- Retain the original close order and mark the scope closed before any request. -/
def start (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) : State κ φ β ε δ ι α :=
  ⟨scope.closeState original, original, scope.closeOrder, [], .ready⟩
/-- Expose one pending request, or mark an empty ready state complete; execute nothing. -/
def advance (machine : State κ φ β ε δ ι α) : State κ φ β ε δ ι α :=
  match machine.phase with
  | .ready => match machine.pending with
    | [] => { machine with phase := .complete }
    | operation :: rest => { machine with pending := rest, phase := .waiting operation }
  | _ => machine
/-- The waiting request, its current ordinal and the fixed original exit. -/
def request? (machine : State κ φ β ε δ ι α) : Option (Nat × φ × Exit β ε δ ι α) :=
  match machine.phase with
  | .waiting operation => some (machine.captured.length, operation, machine.original)
  | _ => none
private def accept (machine : State κ φ β ε δ ι α) (operation : φ)
    (reply : Exit Unit ε δ ι α) : State κ φ β ε δ ι α :=
  { machine with captured := machine.captured ++ [(operation, reply)], phase := .ready }
/-- Accept only the current waiting ordinal and capture its actual operation and reply. -/
def respond (machine : State κ φ β ε δ ι α) (ordinal : Nat) (reply : Exit Unit ε δ ι α) :
    Option (State κ φ β ε δ ι α) :=
  match machine.phase with
  | .waiting operation =>
      if ordinal = machine.captured.length then some (accept machine operation reply) else none
  | _ => none
private def finish : List (Exit Unit ε δ ι α) → Exit Unit ε δ ι α
  | [] => Exit.void
  | [only] => only
  | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)
/-- Completed cleanup result with the existing zero/one/many exit policy. -/
def result? (machine : State κ φ β ε δ ι α) : Option (Exit Unit ε δ ι α) :=
  match machine.phase with
  | .complete => some (finish (machine.captured.map Prod.snd))
  | _ => none
/-- All captured reasons in order, retaining duplicate reasons and their annotations. -/
def journal (machine : State κ φ β ε δ ι α) : List (Reason ε δ ι α) :=
  machine.captured.flatMap fun entry => entry.2.causeReasons
/-- The completed cleanup result restored against the fixed original exit. -/
def restore? [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (machine : State κ φ β ε δ ι α) : Option (Exit β ε δ ι α) :=
  (result? machine).map (Exit.restoreAfterFinalizer machine.original)
/-- Two microsteps per finalizer followed by one completion step; independent of source fuel. -/
def bound (scope : Scope κ φ β ε δ ι α) : Nat := 2 * scope.closeOrder.length + 1
/-- Answer one request per waiting step and keep both residual and service state at every pause. -/
def runState (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α)) :
    Nat → State κ φ β ε δ ι α → σ → State κ φ β ε δ ι α × σ
  | 0, machine, world => (machine, world)
  | fuel + 1, machine, world =>
      match machine.phase with
      | .ready => runState handler fuel (advance machine) world
      | .waiting operation =>
          let (reply, next) := handler operation machine.original world
          runState handler fuel (accept machine operation reply) next
      | .complete => (machine, world)
/-- Every exposed request uses the stored closing exit. census: scope.close-sequential -/
theorem request_uses_original (machine : State κ φ β ε δ ι α) (ordinal : Nat)
    (operation : φ) (offered : Exit β ε δ ι α)
    (request : request? machine = some (ordinal, operation, offered)) : offered = machine.original := by
  unfold request? at request
  split at request <;> simp_all

/-- Stale and future response ordinals cannot consume a waiting request. -/
theorem respond_rejects_wrong_id (machine : State κ φ β ε δ ι α) (ordinal : Nat)
    (reply : Exit Unit ε δ ι α) (different : ordinal ≠ machine.captured.length) :
    respond machine ordinal reply = none := by
  unfold respond
  cases machine.phase <;> simp [different]

/-- Ready and completed states do not accept a callback response. -/
theorem respond_rejects_wrong_phase (machine : State κ φ β ε δ ι α) (ordinal : Nat)
    (reply : Exit Unit ε δ ι α) (wrong : ∀ operation, machine.phase ≠ Phase.waiting operation) :
    respond machine ordinal reply = none := by
  unfold respond
  cases phase : machine.phase with
  | ready | complete => rfl
  | waiting operation => exact False.elim (wrong operation phase)

/-- A zero-step pause retains the entire machine and service state. -/
theorem runState_zero (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (machine : State κ φ β ε δ ι α) (world : σ) : runState handler 0 machine world = (machine, world) := rfl
private theorem run_complete (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (fuel : Nat) (machine : State κ φ β ε δ ι α) (world : σ) (complete : machine.phase = .complete) :
    runState handler fuel machine world = (machine, world) := by
  cases fuel <;> simp [runState, complete]

/-- Resuming from both returned components equals one run with the combined microstep budget. -/
theorem runState_add (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (first later : Nat) (machine : State κ φ β ε δ ι α) (world : σ) :
    runState handler (first + later) machine world =
      let resumed := runState handler first machine world
      runState handler later resumed.1 resumed.2 := by
  induction first generalizing machine world with
  | zero => simp only [Nat.zero_add, runState]
  | succ first ih =>
      rw [Nat.succ_add]
      cases phase : machine.phase <;> simp only [runState, phase]
      · exact ih _ _
      · exact ih _ _
      · exact (run_complete handler later machine world phase).symm

/-- Every prefix retains the scope closed before the first request. census: scope.close-state-first -/
theorem runState_scope (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (budget : Nat) (machine : State κ φ β ε δ ι α) (world : σ) :
    (runState handler budget machine world).1.scope = machine.scope := by
  induction budget generalizing machine world with
  | zero => rfl
  | succ budget ih =>
      cases phase : machine.phase <;> simp only [runState, phase]
      · rw [ih]
        unfold advance
        simp only [phase]
        cases machine.pending <;> rfl
      · rename_i operation
        cases handler operation machine.original world
        rw [ih]
        rfl
private theorem run_ready_complete
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) :
    ∀ pending captured world,
      runState handler (2 * pending.length + 1)
        ⟨scope, original, pending, captured, .ready⟩ world =
      let result := (pending.mapM (fun operation => handler operation original)).run world
      (⟨scope, original, [], captured ++ pending.zip result.1, .complete⟩, result.2) := by
  intro pending
  induction pending with
  | nil =>
      intro captured world
      simp only [List.length_nil, Nat.mul_zero, runState, advance,
        List.mapM_nil, List.zip_nil_left, List.append_nil, StateT.run_pure]
      rfl
  | cons operation pending ih =>
      intro captured world
      have fuel : 2 * (operation :: pending).length + 1 = (2 * pending.length + 1) + 2 := by simp; omega
      rw [fuel, runState]
      dsimp only [advance]
      rw [runState]
      dsimp only
      cases reply : handler operation original world with
      | mk value next =>
          dsimp only [accept]
          rw [ih]
          simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
          simp only [StateT.run, bind, pure, reply]
          simp [List.zip_cons_cons, List.append_assoc]

theorem runState_complete
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ) :
    runState handler (bound scope) (start scope original) world =
      let result := (Scope.closeExitsM handler scope original).run world
      ({ scope := scope.closeState original, original := original, pending := [],
         captured := scope.closeOrder.zip result.1, phase := .complete }, result.2) := by
  exact run_ready_complete handler (scope.closeState original) original scope.closeOrder [] world
private theorem mapM_length {A B W : Type u} (f : A → StateT W Id B) :
    ∀ (xs : List A) (world : W), ((xs.mapM f).run world).1.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro world; rfl
  | cons x xs ih =>
      intro world
      simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
      change ((xs.mapM f).run (f x world).2).1.length + 1 = xs.length + 1
      rw [ih]

private theorem finish_zip (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ) :
    (scope.closeOrder.zip ((Scope.closeExitsM handler scope original).run world).1).map Prod.snd =
      ((Scope.closeExitsM handler scope original).run world).1 :=
  List.map_snd_zip (Nat.le_of_eq (mapM_length _ _ _))

/-- Completion agrees with the exact cleanup fold and existing exit restoration, retaining service state. census: scope.close-merge -/
theorem runState_restore [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ) :
    (let result := runState handler (bound scope) (start scope original) world
     (restore? result.1, result.2)) =
    (let result := (Scope.closeExitsM handler scope original).run world
     let cleanup := match result.1 with
       | [] => Exit.void
       | [only] => only
       | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)
     (some (Exit.restoreAfterFinalizer original cleanup), result.2)) := by
  rw [runState_complete]
  simp only [restore?, result?, finish_zip, Option.map_some]
  rfl

/-- For every pure callback, completion returns exactly existing Scope.closeResult. census: scope.close-merge -/
theorem runState_result (callback : φ → Exit β ε δ ι α → Exit Unit ε δ ι α)
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ) :
    result? (runState
      (fun operation exit world => (callback operation exit, world))
      (bound scope) (start scope original) world).1 =
        some (scope.closeResult callback original) := by
  rw [runState_complete]
  simp only [result?, finish_zip]
  have pureRun : (Scope.closeExitsM (M := StateT σ Id)
      (fun operation exit world => (callback operation exit, world)) scope original).run world =
      (scope.closeExits callback original, world) := by
    unfold Scope.closeExitsM Scope.closeExits
    change ((scope.closeOrder.mapM (fun operation =>
      (pure (callback operation original) : StateT σ Id (Exit Unit ε δ ι α)))).run world) = _
    rw [List.mapM_pure]
    rfl
  rw [pureRun]
  unfold Scope.closeResult
  split
  · rename_i closed
    have order : scope.closeOrder = [] := by
      cases scope with
      | mk strategy state =>
          cases state <;> simp_all [Scope.isClosed, Scope.closeOrder, Scope.finalizers, ScopeState.isClosed, ScopeState.entries]
    simp [Scope.closeExits, order, finish]
  · cases scope.closeExits callback original with
    | nil => rfl
    | cons first rest => cases rest <;> rfl
private def Prefix
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (initial : σ)
    (machine : State κ φ β ε δ ι α) (world : σ) : Prop :=
  machine.scope = scope.closeState original ∧
  machine.original = original ∧
  machine.captured.map Prod.fst ++
    (match machine.phase with | .waiting operation => [operation] | _ => []) ++
    machine.pending = scope.closeOrder ∧
  (machine.phase = .complete → machine.pending = []) ∧
  (((machine.captured.map Prod.fst).mapM
    (fun operation => handler operation original)).run initial) =
    (machine.captured.map Prod.snd, world)

private theorem run_prefix
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (initial : σ)
    (budget : Nat) (machine : State κ φ β ε δ ι α) (world : σ)
    (consistent : Prefix handler scope original initial machine world) :
    Prefix handler scope original initial
      (runState handler budget machine world).1 (runState handler budget machine world).2 := by
  induction budget generalizing machine world with
  | zero => exact consistent
  | succ budget ih =>
      rcases machine with ⟨saved, offered, pending, captured, phase⟩
      rcases consistent with ⟨savedEq, offeredEq, partition, finished, receipt⟩
      dsimp only at savedEq offeredEq
      subst saved
      subst offered
      cases phase with
      | ready =>
          rw [runState]
          dsimp only
          apply ih
          cases pending with
          | nil =>
              exact ⟨rfl, rfl, partition, fun _ => rfl, receipt⟩
          | cons operation rest =>
              refine ⟨rfl, rfl, ?_, ?_, receipt⟩
              · simpa [advance, List.append_assoc] using partition
              · intro impossible
                cases impossible
      | waiting operation =>
          rw [runState]
          dsimp only
          cases reply : handler operation original world with
          | mk exit next =>
              dsimp only
              apply ih
              refine ⟨rfl, rfl, ?_, ?_, ?_⟩
              · simpa [accept, List.map_append, List.append_assoc] using partition
              · intro impossible
                cases impossible
              · dsimp only [accept]
                simp only [List.map_append, List.map_cons, List.map_nil]
                rw [List.mapM_append]
                simp only [StateT.run_bind, StateT.run_pure, receipt]
                simp [List.mapM_cons, StateT.run, bind, pure, StateT.bind, StateT.pure, reply]
      | complete =>
          exact ⟨rfl, rfl, partition, finished, receipt⟩

theorem runState_prefix
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (budget : Nat) (scope : Scope κ φ β ε δ ι α)
    (original : Exit β ε δ ι α) (world : σ) :
    let result := runState handler budget (start scope original) world
    result.1.scope = scope.closeState original ∧
    result.1.original = original ∧
    result.1.captured.map Prod.fst ++
      (match result.1.phase with | .waiting operation => [operation] | _ => []) ++
      result.1.pending = scope.closeOrder ∧
    (result.1.phase = .complete → result.1.pending = []) ∧
    (((result.1.captured.map Prod.fst).mapM
      (fun operation => handler operation original)).run world) =
      (result.1.captured.map Prod.snd, result.2) := by
  apply run_prefix
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  intro impossible
  cases impossible

end Effect4.ScopeMachine
