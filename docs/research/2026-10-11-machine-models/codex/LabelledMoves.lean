import Effect4.Laws.Program.FrameMoves

/-!
Concept: reactive-scheduling and scope-lifetime-finalization, R11.
Claim: the labelled refinement of evaluation-moves, consumed by the shared iteration debit.
The word records frame edits and their emitted events on every native frame.
Each weight still owes its local inequality, including source premises.
This probe establishes no evaluator classification, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

abbrev REvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- The operation retains the code source and the actual pop result. -/
inductive MoveKind where
  | answer (input output : NCode)
  | push (name : EffName)
  | step (input : NCode)
  | finish (input : NCode) (exit : ExitV)
  | pop (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV)
      (popped : List NCode) (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
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
      LabelledMove ⟨.answer f.current code, events⟩ f {f with current := code}
  | push (f : NFrame) (name : EffName) (events : List REvent) :
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
  | mask (f : NFrame) : LabelledMove ⟨.mask, []⟩ f f.uninterruptible
  | unmask (f : NFrame) : LabelledMove ⟨.unmask, []⟩ f f.interruptibleRegion.1
  | pendingFailure (f : NFrame) : LabelledMove ⟨.pendingFailure, []⟩ f
      {f with deferredInterrupt := false, current := Prim.failure f.pendingCause}
  | idle (f : NFrame) (events : List REvent) : LabelledMove ⟨.idle, events⟩ f f

/-- Erasing labels recovers the existing frame shape. -/
theorem LabelledMove.shape {label : MoveLabel} {f g : NFrame}
    (move : LabelledMove label f g) : FrameMove f g := by
  cases move with
  | answer => exact .answer _ _
  | push => exact .push _ _
  | step _ interp f g events found => exact .step interp f g events found
  | finish _ interp f exit events found => exact .finish interp f exit events found
  | pop => exact .pop _ _ _ _
  | mask => exact .mask _
  | unmask => exact .unmask _
  | pendingFailure => exact .pendingFailure _
  | idle f => exact .answer f f.current

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
  | tail _ move ih => exact .tail ih move.shape

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

end Effect4.Program.Moves
