import Effect4.Laws.Machine.Approximation

/-!
# Probe: the driver's helpers as words of primitive machine edits

A finite probe for `../machine-edits.md`. It defines the machine's primitive edits as data, states
three helpers' machine results as words of edits (each by `rfl`), and derives two invariants for
every word from one fact per edit: the trace only grows (`Approximation.Extends`), and a projection
that every edit of the word keeps is kept.

It is not a library module. It compiles with `lake env lean` against the built
`Effect4.Laws.Machine.Approximation`.
-/

set_option autoImplicit false
-- The `DecidableEq` section variables are what the machine's helpers take, as in `Clauses.lean`.
set_option linter.unusedSectionVars false

namespace Effect4.Machine.EditsProbe

open Effect4 Effect4.Machine

universe u v

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- The machine's primitive edits, as first-order data with their payloads. -/
inductive Edit (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v)) :
    Type (max u v) where
  | update (f : RunFiber ν σ β ε δ ι α χ)
  | emit (events : List (RunEvent ν σ β ε δ ι α χ))
  | arm (owner : FiberId)
  | disarm (owner : FiberId)
  | halt (why : Stuck)
  | updateRace (r : Race ν σ β ε δ ι α)
  | appendFiber (f : RunFiber ν σ β ε δ ι α χ)
  | bumpId
  | addFork (record : ForkRecord)
  | setState (s : St)

namespace Edit

/-- What an edit does to a machine. -/
def apply : Edit ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St
  | .update f, m => m.update f
  | .emit events, m => m.emit events
  | .arm owner, m => m.arm owner
  | .disarm owner, m => m.disarm owner
  | .halt why, m => m.halt why
  | .updateRace r, m => m.updateRace r
  | .appendFiber f, m => { m with fibers := m.fibers ++ [f] }
  | .bumpId, m => { m with nextId := m.nextId + 1 }
  | .addFork record, m => { m with forks := m.forks ++ [record] }
  | .setState s, m => { m with state := s }

/-- The events an edit appends to the trace. -/
def events : Edit ν σ β ε δ ι α χ St → List (RunEvent ν σ β ε δ ι α χ)
  | .emit events => events
  | _ => []

/-- **The trace's small axiom.** An edit appends its own events and nothing else. -/
theorem apply_trace (e : Edit ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St) :
    (e.apply m).trace = m.trace ++ e.events := by
  cases e with
  | emit events => exact RunMachine.emit_trace m events
  | _ => exact (List.append_nil _).symm

end Edit

/-- A word of edits, applied left to right. -/
def run (word : List (Edit ν σ β ε δ ι α χ St)) (m : RunMachine ν σ β ε δ ι α χ St) :
    RunMachine ν σ β ε δ ι α χ St :=
  word.foldl (fun m e => e.apply m) m

/-- **Every word extends the trace.** One induction, for every helper with a word. -/
theorem run_extends (word : List (Edit ν σ β ε δ ι α χ St)) (m : RunMachine ν σ β ε δ ι α χ St) :
    RunMachine.Extends m (run word m) := by
  induction word generalizing m with
  | nil => exact RunMachine.Extends.refl m
  | cons e rest ih =>
    have step : RunMachine.Extends m (e.apply m) := ⟨e.events, (e.apply_trace m).symm⟩
    exact RunMachine.Extends.trans step (ih (e.apply m))

/-- **The frame rule of a word.** A projection that every edit of the word keeps is kept. -/
theorem run_keeps {P : Type (max u v)} (proj : RunMachine ν σ β ε δ ι α χ St → P)
    (word : List (Edit ν σ β ε δ ι α χ St))
    (keeps : ∀ e ∈ word, ∀ m, proj (e.apply m) = proj m) (m : RunMachine ν σ β ε δ ι α χ St) :
    proj (run word m) = proj m := by
  induction word generalizing m with
  | nil => rfl
  | cons e rest ih =>
    change proj (run rest (e.apply m)) = proj m
    rw [ih (fun e' member => keeps e' (List.mem_cons_of_mem e member)) (e.apply m),
      keeps e List.mem_cons_self m]

/-! ## Three helpers as words -/

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- `spawn`'s word: append the child, advance the id, record the fork, emit `forked`. -/
def spawnWord (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) : List (Edit ν σ β ε δ ι α χ St) :=
  let childId : FiberId := ⟨m.nextId⟩
  let childInterruptible :=
    match options.maskMode with
    | Supervision.MaskMode.interruptible => true
    | Supervision.MaskMode.uninterruptible => false
    | Supervision.MaskMode.inherit => parent.frame.interruptible
  [.appendFiber (RunFiber.make childId program childInterruptible (interp.budgetOf parent.context)
      parent.context),
   .bumpId,
   .addFork ⟨childId, parent.id, options.daemon, site⟩,
   .emit [RunEvent.forked parent.id childId options.daemon]]

theorem spawn_word (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) :
    (spawn interp m parent program options site).1 = run (spawnWord interp m parent program options site) m :=
  rfl

/-- `start`'s word: nothing when immediate; otherwise arm the parent and emit the scheduled task. -/
def startWord (parent : RunFiber ν σ β ε δ ι α χ) (child : FiberId) (immediately : Bool) :
    List (Edit ν σ β ε δ ι α χ St) :=
  if immediately then []
  else [.arm parent.id, .emit [RunEvent.scheduledTask parent.id 0 (Task.start child)]]

theorem start_word (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (child : FiberId) (immediately : Bool) :
    (start m parent child immediately).1 = run (startWord parent child immediately) m := by
  cases immediately <;> rfl

/-- `postTask`'s word: halt at an unknown owner; otherwise enqueue, arm and emit. -/
def postTaskWord (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (priority : Nat)
    (task : Task ν σ β ε δ ι α) : List (Edit ν σ β ε δ ι α χ St) :=
  match m.fiber? owner with
  | none => [.halt (Stuck.unknownFiber owner)]
  | some o =>
    [.update { o with dispatcher := o.dispatcher.enqueue priority task }, .arm owner,
     .emit [RunEvent.scheduledTask owner priority task]]

theorem postTask_word (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (priority : Nat)
    (task : Task ν σ β ε δ ι α) :
    m.postTask owner priority task = run (postTaskWord m owner priority task) m := by
  unfold RunMachine.postTask postTaskWord
  cases m.fiber? owner <;> rfl

/-! ## Two invariants, for every helper at once -/

/-- The trace grows through each helper, read off its word. -/
example (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) :
    RunMachine.Extends m (spawn interp m parent program options site).1 := by
  rw [spawn_word]
  exact run_extends _ m

example (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (priority : Nat)
    (task : Task ν σ β ε δ ι α) : RunMachine.Extends m (m.postTask owner priority task) := by
  rw [postTask_word]
  exact run_extends _ m

/-- The races are kept by every edit but `updateRace`; so by every helper whose word has none. -/
theorem races_kept (e : Edit ν σ β ε δ ι α χ St) (no : ∀ r, e ≠ .updateRace r)
    (m : RunMachine ν σ β ε δ ι α χ St) : (e.apply m).races = m.races := by
  cases e with
  | updateRace r => exact absurd rfl (no r)
  | _ => rfl

example (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) :
    (spawn interp m parent program options site).1.races = m.races := by
  rw [spawn_word]
  refine run_keeps RunMachine.races _ (fun e member => races_kept e ?_) m
  intro r same
  subst same
  simp only [spawnWord, List.mem_cons, reduceCtorEq, List.mem_nil_iff, or_false] at member

end Effect4.Machine.EditsProbe
