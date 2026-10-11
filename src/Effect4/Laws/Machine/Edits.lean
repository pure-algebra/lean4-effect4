import Effect4.Laws.Machine.Keeps
import Effect4.Laws.Contracts.FramePath

/-!
# Machine edits and their words

Concept: reactive-scheduling, R11. This is the machine part of evaluation-moves.
Consumers: Approximation trace growth, Ledger bookkeeping, and the machine invariants.
A word states the writes of a helper. Payload validity remains an instance obligation.
The words establish no progress and change no reply admission boundary.
-/

set_option autoImplicit false

namespace Effect4.Machine

universe u v w

namespace Edit

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-- Only an emit edit contributes trace events. -/
def events : Edit ν σ β ε δ ι α χ St κ φ η → List (RunEvent ν σ β ε δ ι α χ κ η)
  | .emit events => events
  | _ => []

/-- A state payload occurs exactly at a store write. -/
def stateWrite : Edit ν σ β ε δ ι α χ St κ φ η → Option St
  | .setState state => some state
  | _ => none

/-- Whether a primitive write misses the stored fiber table. -/
def missesFibers (edit : Edit ν σ β ε δ ι α χ St κ φ η) : Prop :=
  edit.writes ≠ .fibers

/-- The primitive writes allowed by settlement, including resolved addressed messages. -/
def settlementWrite : Edit ν σ β ε δ ι α χ St κ φ η → Prop
  | .update _ | .halt _ | .observe _ _ | .dropToken _ => True
  | _ => False

/-- The stored-fiber frame rule for a primitive write. Canonical plan adapters consume it. -/
theorem keeps_fibers (edit : Edit ν σ β ε δ ι α χ St κ φ η) (miss : edit.missesFibers) :
    Keeps (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => m.fibers) edit.apply := by
  intro m
  exact edit.frame .fibers m (Ne.symm miss)

/-- The primitive store frame rule. StatePreservation consumes this projection. -/
theorem apply_state (edit : Edit ν σ β ε δ ι α χ St κ φ η)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (edit.apply m).state = edit.stateWrite.getD m.state := by
  cases edit with
  | setState state => rfl
  | _ =>
    exact frame _ .state m (by intro impossible; cases impossible)

/-- The trace equation of a primitive write. Approximation consumes it through run_trace. -/
theorem apply_trace (edit : Edit ν σ β ε δ ι α χ St κ φ η)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (edit.apply m).trace = m.trace ++ edit.events := by
  cases edit with
  | emit events =>
    cases events with
    | nil => exact (List.append_nil _).symm
    | cons event rest => rfl
  | _ =>
    exact (frame _ .trace m (by intro impossible; cases impossible)).trans (List.append_nil _).symm

end Edit

namespace Edits

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-- Interpret a word from left to right. -/
def run (word : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : RunMachine ν σ β ε δ ι α χ St κ φ η :=
  word.foldl (fun held edit => edit.apply held) m

theorem run_nil (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : run [] m = m := rfl

theorem run_cons (edit : Edit ν σ β ε δ ι α χ St κ φ η)
    (rest : List (Edit ν σ β ε δ ι α χ St κ φ η)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    run (edit :: rest) m = run rest (edit.apply m) := rfl

theorem run_append (left right : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    run (left ++ right) m = run right (run left m) := List.foldl_append

/-- Prefix-independent edge facts build the existing path for a word. -/
theorem run_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (word : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (edge : ∀ edit ∈ word, ∀ held, Edge held (edit.apply held) edit)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    Effect4.Contracts.Path Edge m (run word m) word := by
  induction word generalizing m with
  | nil => exact .nil m
  | cons edit rest ih =>
    exact .cons (edge edit List.mem_cons_self m)
      (ih (fun next member => edge next (List.mem_cons_of_mem edit member)) _)

/-- Every word appends exactly its edit events, in word order. -/
theorem run_trace (word : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (run word m).trace = m.trace ++ word.flatMap Edit.events := by
  induction word generalizing m with
  | nil => exact (List.append_nil _).symm
  | cons edit rest ih =>
    rw [show run (edit :: rest) m = run rest (edit.apply m) from rfl,
      ih, edit.apply_trace]
    exact List.append_assoc _ _ _

/-- The trace of a word contains the original trace as a prefix. -/
theorem run_extends (word : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : m.trace <+: (run word m).trace :=
  ⟨word.flatMap Edit.events, (run_trace word m).symm⟩

/-- A word keeps any projection kept by each edit in that word. -/
theorem run_keeps {P : Sort w} (projection : RunMachine ν σ β ε δ ι α χ St κ φ η → P)
    (word : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (kept : ∀ edit ∈ word, Keeps projection edit.apply) : Keeps projection (run word) := by
  exact Keeps.foldl projection Edit.apply word kept

/-- A predicate is retained by the whole word from its per-edit preservation laws. -/
theorem run_preserves (invariant : RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (word : List (Edit ν σ β ε δ ι α χ St κ φ η))
    (kept : ∀ edit ∈ word, ∀ held, invariant held → invariant (edit.apply held))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (initial : invariant m) :
    invariant (run word m) := by
  induction word generalizing m with
  | nil => exact initial
  | cons edit rest ih =>
    exact ih (fun next member => kept next (List.mem_cons_of_mem edit member)) _
      (kept edit List.mem_cons_self m initial)

/-- An existing path whose edges are actual edits has the word's exact endpoint.
Payload premises can remain part of Edge and retain their actual prefix state. -/
theorem run_of_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (actual : ∀ before after edit, Edge before after edit → after = edit.apply before)
    {before after : RunMachine ν σ β ε δ ι α χ St κ φ η}
    {word : List (Edit ν σ β ε δ ι α χ St κ φ η)}
    (path : Effect4.Contracts.Path Edge before after word) : run word before = after := by
  induction path with
  | nil held => rfl
  | cons head tail ih =>
    change run _ (Edit.apply _ _) = _
    rw [← actual _ _ _ head]
    exact ih

/-- Local payload laws need hold only at each actual prefix recorded by Path.
Guard and Ledger use this rule for replacements resolved from a current lookup. -/
theorem run_preserves_at
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (actual : ∀ before after edit, Edge before after edit → after = edit.apply before)
    (invariant : RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (kept : ∀ before after edit, Edge before after edit → invariant before → invariant after)
    {before after : RunMachine ν σ β ε δ ι α χ St κ φ η}
    {word : List (Edit ν σ β ε δ ι α χ St κ φ η)}
    (path : Effect4.Contracts.Path Edge before after word) (initial : invariant before) :
    invariant (run word before) := by
  rw [run_of_path actual path]
  induction path with
  | nil held => exact initial
  | cons head tail ih => exact ih (kept _ _ _ head initial)

section messages
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  [FiberCore ν β ε δ ι α κ φ]

/-- Resolve an addressed runtime message at its actual current lookup.
An interrupt payload is computed here, rather than taken from a producer's old record.
Generated commands remain the separate second component of applyFiberEdit. -/
def fiberWord (edit : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match edit with
  | .observe target observer => [.observe target observer]
  | .dropToken token => [.dropToken token]
  | .interrupt target cause =>
    match m.fiber? target with
    | none => []
    | some fiber => [.update (interruptWithCause cause fiber).1]

/-- The machine result of a runtime message is its resolved edit word. -/
theorem fiber_word (edit : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (applyFiberEdit edit m).1 = run (fiberWord edit m) m := by
  cases edit with
  | observe target observer => rfl
  | dropToken token => rfl
  | interrupt target cause =>
    cases found : m.fiber? target <;> simp only [applyFiberEdit, fiberWord, found] <;> rfl

/-- A message resolves to at most one primitive edge, or the identity path.
The edge premise retains its originating message and its actual lookup state. -/
theorem fiberWord_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (message : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (edge : ∀ edit, fiberWord message m = [edit] → Edge m (applyFiberEdit message m).1 edit) :
    Effect4.Contracts.Path Edge m (applyFiberEdit message m).1 (fiberWord message m) := by
  cases message with
  | observe target observer => exact .cons (edge _ rfl) (.nil _)
  | dropToken token => exact .cons (edge _ rfl) (.nil _)
  | interrupt target cause =>
    cases found : m.fiber? target with
    | none => simp only [applyFiberEdit, fiberWord, found]; exact .nil m
    | some fiber =>
      have one := edge (.update (interruptWithCause cause fiber).1)
        (by simp only [fiberWord, found])
      simpa only [applyFiberEdit, fiberWord, found] using Effect4.Contracts.Path.cons one (.nil _)

/-- Resolve a message word at each successive machine, retaining runtime order. -/
def fiberWords : List (FiberEdit ε δ ι α) → RunMachine ν σ β ε δ ι α χ St κ φ η →
    List (Edit ν σ β ε δ ι α χ St κ φ η)
  | [], _ => []
  | edit :: rest, m => fiberWord edit m ++ fiberWords rest (applyFiberEdit edit m).1

theorem fiber_words_acc (edits : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (commands : List (Cmd ν σ β ε δ ι α κ)) :
    (edits.foldl (fun held edit =>
      let next := applyFiberEdit edit held.1
      (next.1, held.2 ++ next.2)) (m, commands)).1 = run (fiberWords edits m) m := by
  induction edits generalizing m commands with
  | nil => rfl
  | cons edit rest ih =>
    simp only [List.foldl_cons, fiberWords, run_append]
    rw [← fiber_word]
    exact ih _ _

/-- The actual runtime fold interprets the resolved machine word.
Its command prefix remains the runtime fold's second component, in the same order. -/
theorem fiber_words (edits : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (applyFiberEdits edits m).1 = run (fiberWords edits m) m := fiber_words_acc edits m []

/-- Message-local paths compose at their actual successive lookup states.
Guard and Ledger instantiate Edge with the resolved message payload's local premises. -/
theorem fiberWords_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (edits : List (FiberEdit ε δ ι α))
    (localPath : ∀ message ∈ edits, ∀ held : RunMachine ν σ β ε δ ι α χ St κ φ η,
      Effect4.Contracts.Path Edge held (applyFiberEdit message held).1 (fiberWord message held))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    Effect4.Contracts.Path Edge m (applyFiberEdits edits m).1 (fiberWords edits m) := by
  rw [fiber_words]
  induction edits generalizing m with
  | nil => exact .nil m
  | cons message rest ih =>
    rw [fiberWords, run_append, ← fiber_word]
    exact (localPath message List.mem_cons_self m).append
      (ih (fun next member => localPath next (List.mem_cons_of_mem message member)) _)

theorem fiberWord_events (edit : FiberEdit ε δ ι α)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : (fiberWord edit m).flatMap Edit.events = [] := by
  cases edit with
  | observe target observer => rfl
  | dropToken token => rfl
  | interrupt target cause => cases found : m.fiber? target <;> simp only [fiberWord, found] <;> rfl

theorem fiberWords_events (edits : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : (fiberWords edits m).flatMap Edit.events = [] := by
  induction edits generalizing m with
  | nil => rfl
  | cons edit rest ih =>
    rw [fiberWords, List.flatMap_append, fiberWord_events, ih, List.nil_append]

end messages
end Edits
end Effect4.Machine
