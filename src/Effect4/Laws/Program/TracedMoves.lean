import Effect4.Laws.Program.FrameMoves
import Effect4.Laws.Machine.Approximation

/-!
Concept: reactive-scheduling and scope-lifetime-finalization, R11.
Claim: the labelled refinement of evaluation-moves, consumed by the shared iteration debit.
The word records frame edits and their emitted events on every native frame.
Each weight still owes its local inequality, including source premises.
The classifier in Footprint consumes this structure.
These laws establish no progress, source admission, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

abbrev REvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- Administrative events contain neither a frame event nor a finalizer start. -/
def administrative : REvent → Bool
  | .frame .. | .finalizerProgram .. => false
  | _ => true

/-- An administrative list cannot invent a frame debit or registration. -/
def Administrative (events : List REvent) : Prop := events.all administrative = true

/-- The exact pop selected by a completed exit. -/
abbrev popExit (f : NFrame) (exit : ExitV) :=
  f.getCont (match exit with | .success _ => .contA | .failure _ => .contE)
    (match exit with | .success _ => false | .failure _ => true)
    (match exit with | .success _ => none | .failure cause => some cause)

/-- A finalizer start follows its real pop in the same evaluation. -/
abbrev exitEvents (id : FiberId) (f : NFrame) (exit : ExitV) (started : Option EffName) : List REvent :=
  (popExit f exit).events.map (.frame id) ++
    (match started with
     | none => []
     | some name => [.finalizerProgram id name ((popExit f exit).deliveredExit exit)])

/-- The operation retains the code source and the actual pop result. -/
inductive MoveKind where
  | answer (input output : NCode)
  | push (name : EffName)
  | step (input : NCode)
  | finish (input : NCode) (exit : ExitV)
  | pop (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV)
      (popped : List NCode) (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
  | popAnswer (exit : ExitV) (popped : List NCode)
      (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
      (output : NCode) (started : Option EffName)
  | mask
  | unmask
  | pendingFailure
  | idle

/-- One operation and the actual run events it emits. -/
structure MoveLabel where
  kind : MoveKind
  events : List REvent

/-- The labelled refinement of the existing frame shapes. -/
inductive LabelledMove : MoveLabel → NFrame → NFrame → Prop
  | answer (f : NFrame) (code : NCode) (events : List REvent) :
      Administrative events →
      LabelledMove ⟨.answer f.current code, events⟩ f {f with current := code}
  | push (f : NFrame) (name : EffName) (events : List REvent) :
      Administrative events →
      LabelledMove ⟨.push name, events⟩ f {f with stack := Prim.asyncFinalizer name :: f.stack}
  | step (id : FiberId) (interp : NPrim) (f g : NFrame) (events : List NEvent) :
      f.step interp = (.running g, events) →
      LabelledMove ⟨.step f.current, events.map (.frame id)⟩ f g
  | finish (id : FiberId) (interp : NPrim) (f : NFrame) (exit : ExitV) (events : List NEvent) :
      f.step interp = (.finished exit, events) →
      LabelledMove ⟨.finish f.current exit, events.map (.frame id)⟩ f (frameExitState f)
  | pop (id : FiberId) (f : NFrame) (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
      LabelledMove
        ⟨.pop demand skip cause (f.getCont demand skip cause).popped
          (f.getCont demand skip cause).answer,
          (f.getCont demand skip cause).events.map (.frame id)⟩
        f (f.getCont demand skip cause).fiber
  | popAnswer (id : FiberId) (f : NFrame) (exit : ExitV) (code : NCode) (started : Option EffName) :
      (∀ name, started = some name → ∃ body flag,
        (popExit f exit).answer = .frame (.onExit body name flag)) →
      LabelledMove
        ⟨.popAnswer exit (popExit f exit).popped (popExit f exit).answer code started,
          exitEvents id f exit started⟩
        f {(popExit f exit).fiber with current := code}
  | mask (f : NFrame) : LabelledMove ⟨.mask, []⟩ f f.uninterruptible
  | unmask (f : NFrame) : LabelledMove ⟨.unmask, []⟩ f f.interruptibleRegion.1
  | pendingFailure (f : NFrame) : LabelledMove ⟨.pendingFailure, []⟩ f
      {f with deferredInterrupt := false, current := Prim.failure f.pendingCause}
  | idle (f : NFrame) (events : List REvent) : Administrative events → LabelledMove ⟨.idle, events⟩ f f

/-- Erasing labels recovers the existing frame shape. -/
theorem LabelledMove.shape {label : MoveLabel} {f g : NFrame}
    (move : LabelledMove label f g) : Moves f g := by
  cases move with
  | answer => exact .single (.answer _ _)
  | push => exact .single (.push _ _)
  | step _ interp f g events found => exact .single (.step interp f g events found)
  | finish _ interp f exit events found => exact .single (.finish interp f exit events found)
  | pop => exact .single (.pop _ _ _ _)
  | popAnswer => exact .two (.pop _ _ _ _) (.answer _ _)
  | mask => exact .single (.mask _)
  | unmask => exact .single (.unmask _)
  | pendingFailure => exact .single (.pendingFailure _)
  | idle f => exact .single (.answer f f.current)

/-- A labelled word is built at its end. -/
inductive LabelledMoves : List MoveLabel → NFrame → NFrame → Prop
  | refl (f : NFrame) : LabelledMoves [] f f
  | tail {labels : List MoveLabel} {label : MoveLabel} {f g h : NFrame} :
      LabelledMoves labels f g → LabelledMove label g h →
      LabelledMoves (labels ++ [label]) f h

/-- One labelled move forms a word. -/
theorem LabelledMoves.single {label : MoveLabel} {f g : NFrame}
    (move : LabelledMove label f g) : LabelledMoves [label] f g :=
  .tail (.refl f) move

/-- Labelled words compose in trace order. -/
theorem LabelledMoves.trans {left right : List MoveLabel} {f g h : NFrame}
    (first : LabelledMoves left f g) (second : LabelledMoves right g h) :
    LabelledMoves (left ++ right) f h := by
  induction second with
  | refl => simpa only [List.append_nil] using first
  | tail _ move ih => simpa only [List.append_assoc] using LabelledMoves.tail (ih first) move

/-- The labelled word projects to the existing shape word. -/
theorem LabelledMoves.shape {labels : List MoveLabel} {f g : NFrame}
    (word : LabelledMoves labels f g) : Moves f g := by
  induction word with
  | refl => exact .refl _
  | tail _ move ih => exact ih.trans move.shape

/-- Actual events concatenate in the word's order. -/
def events (labels : List MoveLabel) : List REvent := labels.flatMap MoveLabel.events

theorem events_append (left right : List MoveLabel) :
    events (left ++ right) = events left ++ events right := by
  simp only [events, List.flatMap_append]

/-- A local bound sums along a word; no subtraction discards a debt.
Consumer: a ledger's local iteration debit after classification. -/
theorem Moves.balance (weight : NFrame → Nat) (gain cost : MoveLabel → Nat)
    (each : ∀ label f g, LabelledMove label f g → weight g + cost label ≤ weight f + gain label)
    {labels : List MoveLabel} {f g : NFrame} (word : LabelledMoves labels f g) :
    weight g + (labels.map cost).sum ≤ weight f + (labels.map gain).sum := by
  induction word with
  | refl => exact Nat.le_refl _
  | tail preceding move ih =>
    have bounded := each _ _ _ move
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega


/-- Two labelled operations compose in their actual order. -/
theorem LabelledMoves.two {left right : MoveLabel} {f g h : NFrame}
    (a : LabelledMove left f g) (b : LabelledMove right g h) :
    LabelledMoves [left, right] f h := .tail (.single a) b

/-- A word accounts for the exact extension of the machine's trace. -/
def TracedMoves (m : NativeMachine) (f : NFrame) (n : NativeMachine) (g : NFrame) : Prop :=
  ∃ labels, LabelledMoves labels f g ∧ n.trace = m.trace ++ events labels

/-- One operation accounts for its emitted events. -/
theorem TracedMoves.single {m n : NativeMachine} {f g : NFrame} {label : MoveLabel}
    (move : LabelledMove label f g) (trace : n.trace = m.trace ++ label.events) :
    TracedMoves m f n g := by
  refine ⟨[label], .single move, ?_⟩
  simpa only [events, List.flatMap_cons, List.flatMap_nil, List.append_nil] using trace

/-- The empty word emits nothing. -/
theorem TracedMoves.refl (m : NativeMachine) (f : NFrame) : TracedMoves m f m f :=
  ⟨[], .refl f, (List.append_nil _).symm⟩

/-- Composition retains the exact event order. -/
theorem TracedMoves.trans {m n o : NativeMachine} {f g h : NFrame}
    (a : TracedMoves m f n g) (b : TracedMoves n g o h) : TracedMoves m f o h := by
  obtain ⟨left, stepsLeft, traceLeft⟩ := a
  obtain ⟨right, stepsRight, traceRight⟩ := b
  refine ⟨left ++ right, stepsLeft.trans stepsRight, ?_⟩
  rw [traceRight, traceLeft, events_append, List.append_assoc]

/-- Erasure retains the existing unlabelled word. -/
theorem TracedMoves.shape {m n : NativeMachine} {f g : NFrame}
    (word : TracedMoves m f n g) : Moves f g := by
  obtain ⟨_, steps, _⟩ := word
  exact steps.shape

/-- Trace-only edits introduce no frame event or finalizer start. -/
def AdministrativeTrace (m n : NativeMachine) : Prop :=
  ∃ emitted, Administrative emitted ∧ n.trace = m.trace ++ emitted

/-- A trace equality is an empty administrative extension. -/
theorem AdministrativeTrace.of_eq {m n : NativeMachine} (same : n.trace = m.trace) :
    AdministrativeTrace m n := ⟨[], rfl, same.trans (List.append_nil _).symm⟩

/-- Two administrative extensions compose. -/
theorem AdministrativeTrace.trans {m n o : NativeMachine}
    (a : AdministrativeTrace m n) (b : AdministrativeTrace n o) : AdministrativeTrace m o := by
  obtain ⟨left, quietLeft, traceLeft⟩ := a
  obtain ⟨right, quietRight, traceRight⟩ := b
  refine ⟨left ++ right, ?_, ?_⟩
  · change left.all administrative = true at quietLeft
    change right.all administrative = true at quietRight
    simp only [Administrative, List.all_append, quietLeft, quietRight, Bool.and_self]
  · rw [traceRight, traceLeft, List.append_assoc]

/-- A trace extension with an administrative list supplies the exact suffix. -/
theorem AdministrativeTrace.emit (m : NativeMachine) (emitted : List REvent)
    (quiet : Administrative emitted) : AdministrativeTrace m (m.emit emitted) :=
  ⟨emitted, quiet, RunMachine.emit_trace _ _⟩

/-- Administrative events accompany a code replacement without a hidden debit. -/
theorem AdministrativeTrace.answer {m n : NativeMachine} (quiet : AdministrativeTrace m n)
    (f : NFrame) (code : NCode) : TracedMoves m f n {f with current := code} := by
  obtain ⟨emitted, quiet, trace⟩ := quiet
  exact .single (.answer _ _ emitted quiet) trace

/-- An administrative park may push its asynchronous cancel frame. -/
theorem AdministrativeTrace.push {m n : NativeMachine} (quiet : AdministrativeTrace m n)
    (f : NFrame) (name : EffName) :
    TracedMoves m f n {f with stack := .asyncFinalizer name :: f.stack} := by
  obtain ⟨emitted, quiet, trace⟩ := quiet
  exact .single (.push _ _ emitted quiet) trace

/-- Administrative events can leave the selected frame unchanged. -/
theorem AdministrativeTrace.idle {m n : NativeMachine} (quiet : AdministrativeTrace m n)
    (f : NFrame) : TracedMoves m f n f := by
  obtain ⟨emitted, quiet, trace⟩ := quiet
  exact .single (.idle _ emitted quiet) trace

/-- Spawning records a birth and leaves frame accounting events absent. -/
theorem spawn_administrative (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (code : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    AdministrativeTrace m (spawn interp m f code options site).1 := by
  unfold spawn
  exact ⟨[.forked f.id ⟨m.nextId⟩ options.daemon], rfl, RunMachine.emit_trace _ _⟩

/-- Starting records at most an administrative scheduling event. -/
theorem start_administrative (m : NativeMachine) (f : NFiber) (child : FiberId) (now : Bool) :
    AdministrativeTrace m (start m f child now).1 := by
  unfold start
  split
  · exact .of_eq rfl
  · exact ⟨[.scheduledTask f.id 0 (.start child)], rfl, RunMachine.emit_trace _ _⟩

/-- Parallel finalizer spawning composes only administrative birth events. -/
theorem forkFinalizers_administrative (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (codes : List NCode) : AdministrativeTrace m (forkFinalizers interp m f codes).1 := by
  induction codes generalizing m with
  | nil => exact .of_eq rfl
  | cons code rest ih =>
    exact (spawn_administrative interp m f code _ []).trans (ih _)

/-- Scope links record linkage or interruption, without a frame event or program start. -/
theorem linkScopeEdits_administrative (interp : NInterp) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    AdministrativeTrace m (linkScopeEdits interp m mode scope target interruptor extra).1 := by
  unfold linkScopeEdits
  split
  · exact .of_eq rfl
  · split
    · exact .of_eq rfl
    · refine ⟨[.scopeClosedOnLink scope target, .interruptRecorded interruptor target], rfl, ?_⟩
      simp only [RunMachine.emit_trace]
  · split
    · exact .of_eq rfl
    · split
      · exact .of_eq rfl
      · split
        · exact .of_eq rfl
        · rename_i state key _
          refine ⟨[.scopeLinked mode scope key target], rfl, ?_⟩
          simp only [RunMachine.emit_trace]

/-- The eager adapter has the plan's trace because message interpretation emits no events. -/
theorem linkScope_administrative (interp : NInterp) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    AdministrativeTrace m (linkScope interp m mode scope target interruptor extra).1 := by
  obtain ⟨events, allowed, trace⟩ := linkScopeEdits_administrative interp m mode scope target interruptor extra
  exact ⟨events, allowed, (RunMachine.applyFiberEdits_trace _ _).trans trace⟩

end Effect4.Program.Moves
