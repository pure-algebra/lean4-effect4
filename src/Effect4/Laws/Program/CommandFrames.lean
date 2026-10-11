import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.Footprint
import Effect4.Laws.Program.StackLocal
import Effect4.Laws.Program.MovesConnect

/-!
# Laws.Program.CommandFrames — what one command can do to every fiber's frame

`Laws/Program/Moves.lean` classifies one evaluation's edits of the evaluated fiber's frame, and
`Laws/Program/Interference.lean` what it does to the other fibers. A command of the loop
(`driveStep`) does more: it publishes an exit, clears an exited fiber, records interrupts, resumes a
parked fiber, and pushes the parallel close's iterator. This module states the frame half of every
command once:

* **The frame edits of a command** (`FrameEdit`, `FrameEdits`): the evaluation's moves, an interrupt
  recorded (`interruptRecord`), the deferred bit set, the stack cleared (an exited fiber), and the
  parallel close's iterator pushed.
* **The machine's frames follow** (`FramesFollow m m'`): the id counter does not go back, and every
  fiber of `m'` is a fiber of `m` with the same id whose frame moved by a word of edits, or a new one.
* **The classification** (`driveStep_transports`): one census for raw and guarded commands.
* **The live word** (`driveStep_liveTransports`): an exited target is required for `exitDone`.
  A live successor retains a live predecessor and a word without `clearStack`.
* **The old interface** (`driveStep_framesFollow`): the raw projection of the same census.
* **The mask instance** (`Transport.maskLater`): induction over the live word.

So a frame invariant that each edit keeps, and that holds of a new fiber's frame, holds after every
command. `MaskRuns`'s command half is such an invariant, and so is the shape stack locality asks
for, between the edits that reach the entry's stack.

Placement (AGENTS.md, Trust):

- concept `reactive-scheduling` (`docs/core/semantics.md` §2.4), serving requirement R11;
- registry question `saved-mask-region-bracket`, role preservation, at `compiled_region_bracket`.
  These helpers supply its command transport; the run stack premise remains open;
- `Transport.maskLater` also serves `saved-mask-chain-runs`, at `compiled_mask_chain_runs`;
- reach: every command of the native loop (`driveStep` at `evaluatorFor root table`), every
  interpreter, machine and pending list;
- it retains frames, ids, live predecessors and initialized fresh fibers.
  Stores, queues, races, source ownership and the choice of command remain outside it;
- the initialized frame retains its program and context, without a parent-context or source-point witness;
- consumers: `MaskRuns`'s command half (decisions row 350's cleanup), stack locality along a run,
  and the goals packet's fiber positions (G2).
-/

set_option autoImplicit false

namespace Effect4.Program.Moves

open Effect4 Effect4.Machine Effect4.Program

/-- A command of the native loop. -/
abbrev NCommand := Cmd EffName EffThunk Val Err Defect FiberId Ann

/-- The frame edits one command can make to any fiber. -/
inductive FrameEdit : NFrame → NFrame → Prop
  /-- A move of an evaluation. -/
  | move {f g : NFrame} : FrameMove f g → FrameEdit f g
  /-- An interrupt is recorded: the cause, then the deferred bit or a failure as the code. -/
  | interrupted (interp : NInterp) (g : NFiber) (who : Option FiberId)
      (extra : ReasonAnnotations Ann) : FrameEdit g.frame (interruptRecord interp who extra g).1.frame
  /-- The deferred bit is set: the exit path clears it. -/
  | setDeferred (f : NFrame) (deferred : Bool) : FrameEdit f { f with deferredInterrupt := deferred }
  /-- The stack is cleared: an exited fiber after its observers. -/
  | clearStack (f : NFrame) : FrameEdit f { f with stack := [] }
  /-- The parallel close pushes its iterator under the await. -/
  | pushIterator (f : NFrame) (name : EffName) (cursor : Val) :
      FrameEdit f { f with stack := Prim.iterator name cursor :: f.stack }

/-- Words of frame edits. -/
inductive FrameEdits : NFrame → NFrame → Prop
  /-- No edit. -/
  | refl (f : NFrame) : FrameEdits f f
  /-- One more edit at the end. -/
  | tail {f g h : NFrame} : FrameEdits f g → FrameEdit g h → FrameEdits f h

/-- Words of frame edits compose. -/
theorem FrameEdits.trans {f g h : NFrame} (a : FrameEdits f g) (b : FrameEdits g h) :
    FrameEdits f h := by
  induction b with
  | refl => exact a
  | tail _ e ih => exact .tail ih e

/-- An evaluation's word of moves is a word of edits. -/
theorem FrameEdits.ofMoves {f g : NFrame} (w : Moves f g) : FrameEdits f g := by
  induction w with
  | refl => exact .refl _
  | tail _ m ih => exact .tail ih (.move m)

/-- One edit is a word. -/
theorem FrameEdits.single {f g : NFrame} (e : FrameEdit f g) : FrameEdits f g :=
  .tail (.refl f) e

/-- An edit of another fiber edits its frame by a word of frame edits. -/
theorem OtherEdits.frames {g h : NFiber} (w : OtherEdits g h) : FrameEdits g.frame h.frame := by
  induction w with
  | refl => exact .refl _
  | tail _ e ih =>
    cases e with
    | observe => exact ih
    | filterObservers => exact ih
    | interrupted interp _ who extra => exact .tail ih (.interrupted interp _ who extra)

/-- **The machine's frames follow**: the id counter does not go back, and every fiber of `m'` is a
fiber of `m` with the same id whose frame moved by a word of edits, or a new one. -/
structure FramesFollow (m m' : NativeMachine) : Prop where
  /-- The id counter does not go back. -/
  nextId : m.nextId ≤ m'.nextId
  /-- Every fiber's frame followed from an old one, or the fiber is new. -/
  fibers : ∀ g' ∈ m'.fibers,
    (∃ g ∈ m.fibers, g.id = g'.id ∧ FrameEdits g.frame g'.frame) ∨ m.nextId ≤ g'.id.value

/-- No command. -/
theorem FramesFollow.refl (m : NativeMachine) : FramesFollow m m :=
  ⟨Nat.le_refl _, fun g' mem => .inl ⟨g', mem, rfl, .refl _⟩⟩

/-- Commands compose. -/
theorem FramesFollow.trans {m m' m'' : NativeMachine} (a : FramesFollow m m')
    (b : FramesFollow m' m'') : FramesFollow m m'' := by
  refine ⟨Nat.le_trans a.nextId b.nextId, fun g'' mem => ?_⟩
  rcases b.fibers g'' mem with ⟨g', mem', id', w'⟩ | fresh
  · rcases a.fibers g' mem' with ⟨g, memOld, id, w⟩ | fresh'
    · exact .inl ⟨g, memOld, id.trans id', w.trans w'⟩
    · exact .inr (id' ▸ fresh')
  · exact .inr (Nat.le_trans a.nextId fresh)

/-- The command edits that do not clear a stack.
Consumer: live fibers in `Transport`; the frame machine's own finishing move remains explicit. -/
inductive LiveEdit : NFrame → NFrame → Prop
  | move {f g : NFrame} : FrameMove f g → LiveEdit f g
  | interrupted (interp : NInterp) (g : NFiber) (who : Option FiberId)
      (extra : ReasonAnnotations Ann) : LiveEdit g.frame (interruptRecord interp who extra g).1.frame
  | setDeferred (f : NFrame) (deferred : Bool) : LiveEdit f { f with deferredInterrupt := deferred }
  | pushIterator (f : NFrame) (name : EffName) (cursor : Val) :
      LiveEdit f { f with stack := Prim.iterator name cursor :: f.stack }

/-- A word without stack clearing; the command census retains this word for every live fiber. -/
inductive LiveEdits : NFrame → NFrame → Prop
  | refl (f : NFrame) : LiveEdits f f
  | tail {f g h : NFrame} : LiveEdits f g → LiveEdit g h → LiveEdits f h

/-- Clearing-free words compose. -/
theorem LiveEdits.trans {f g h : NFrame} (a : LiveEdits f g) (b : LiveEdits g h) :
    LiveEdits f h := by
  induction b with
  | refl => exact a
  | tail _ e ih => exact .tail ih e

/-- One clearing-free edit is a word. -/
theorem LiveEdits.single {f g : NFrame} (e : LiveEdit f g) : LiveEdits f g :=
  .tail (.refl f) e

/-- An evaluation's moves clear no stack outside the finishing frame step. -/
theorem LiveEdits.ofMoves {f g : NFrame} (w : Moves f g) : LiveEdits f g := by
  induction w with
  | refl => exact .refl _
  | tail _ m ih => exact .tail ih (.move m)

/-- Forget the live restriction; consumer: the original raw command interface. -/
theorem LiveEdits.frames {f g : NFrame} (w : LiveEdits f g) : FrameEdits f g := by
  induction w with
  | refl => exact .refl _
  | tail _ e ih =>
    cases e with
    | move m => exact .tail ih (.move m)
    | interrupted interp fiber who extra => exact .tail ih (.interrupted interp fiber who extra)
    | setDeferred _ flag => exact .tail ih (.setDeferred _ flag)
    | pushIterator _ name cursor => exact .tail ih (.pushIterator _ name cursor)

/-- Every clearing-free command edit keeps the saved mask chain.
Consumer: `Transport.maskLater`, the mask instance of the command classification. -/
theorem LiveEdit.maskChain (base : Bool) {f g : NFrame} (edit : LiveEdit f g)
    (held : FrameFiber.MaskChain base f.interruptible f.stack) :
    FrameFiber.MaskChain base g.interruptible g.stack := by
  cases edit with
  | move step => exact move_maskChain base step held
  | interrupted interp fiber who extra =>
    unfold interruptRecord
    dsimp only
    (repeat' split) <;> exact held
  | setDeferred => exact held
  | pushIterator => exact held

/-- The mask instance follows the word, without another command case analysis. -/
theorem LiveEdits.maskChain (base : Bool) {f g : NFrame} (word : LiveEdits f g)
    (held : FrameFiber.MaskChain base f.interruptible f.stack) :
    FrameFiber.MaskChain base g.interruptible g.stack := by
  induction word with
  | refl => exact held
  | tail _ edit ih => exact edit.maskChain base ih

/-- The same transport serves raw and guarded commands.
Only raw commands may use the `allowClear` escape; guarded commands instantiate it with `False`. -/
def Transport (allowClear : Prop) (f g : NFiber) : Prop :=
  g.id = f.id ∧ FrameEdits f.frame g.frame ∧
    (g.exit = none → f.exit = none ∧ (allowClear ∨ LiveEdits f.frame g.frame))

/-- Transport retains the fiber id. -/
theorem Transport.id {allowClear : Prop} {f g : NFiber} (h : Transport allowClear f g) :
    g.id = f.id := h.1

/-- Transport retains the unrestricted frame word. -/
theorem Transport.frame {allowClear : Prop} {f g : NFiber} (h : Transport allowClear f g) :
    FrameEdits f.frame g.frame := h.2.1

/-- The live projection reads the predecessor and the clearing restriction together. -/
theorem Transport.live {allowClear : Prop} {f g : NFiber} (h : Transport allowClear f g)
    (live : g.exit = none) : f.exit = none ∧ (allowClear ∨ LiveEdits f.frame g.frame) := h.2.2 live

/-- Unchanged frame, id and exit give reflexive transport. -/
theorem Transport.refl (allowClear : Prop) (f : NFiber) : Transport allowClear f f :=
  ⟨rfl, .refl _, fun live => ⟨live, .inr (.refl _)⟩⟩

/-- A clearing-free edit that retains the exit transports a fiber. -/
theorem Transport.edit {allowClear : Prop} {f g : NFiber} (id : g.id = f.id)
    (exit : g.exit = f.exit) (frame : LiveEdits f.frame g.frame) : Transport allowClear f g :=
  ⟨id, frame.frames, fun live => ⟨exit.symm.trans live, .inr frame⟩⟩

/-- A published exit admits clearing, but never establishes a live successor. -/
theorem Transport.exited {allowClear : Prop} {f g : NFiber} (id : g.id = f.id)
    (frame : FrameEdits f.frame g.frame) (exited : g.exit.isSome = true) : Transport allowClear f g := by
  refine ⟨id, frame, ?_⟩
  intro live
  rw [live] at exited
  cases exited

/-- A raw clear needs explicit permission when its target remains live. -/
theorem Transport.clear {allowClear : Prop} {f g : NFiber} (id : g.id = f.id)
    (exit : g.exit = f.exit) (frame : g.frame = { f.frame with stack := [] })
    (allowed : f.exit = none → allowClear) : Transport allowClear f g := by
  refine ⟨id, frame ▸ .single (.clearStack _), ?_⟩
  intro live
  have before := exit.symm.trans live
  exact ⟨before, .inl (allowed before)⟩

/-- Transport composes; a live successor has a live predecessor at every intermediate cut. -/
theorem Transport.trans {allowClear : Prop} {f g h : NFiber}
    (a : Transport allowClear f g) (b : Transport allowClear g h) : Transport allowClear f h := by
  refine ⟨b.id.trans a.id, a.frame.trans b.frame, ?_⟩
  intro live
  obtain ⟨middle, bword⟩ := b.live live
  obtain ⟨before, aword⟩ := a.live middle
  refine ⟨before, ?_⟩
  rcases aword with allowed | aword
  · exact .inl allowed
  rcases bword with allowed | bword
  · exact .inl allowed
  · exact .inr (aword.trans bword)

/-- A guarded command transport is the existing mask relation's native instance. -/
theorem Transport.maskLater {f g : NFiber} (transport : Transport False f g) :
    MaskLater f g := by
  refine ⟨transport.id, fun live => (transport.live live).1, ?_⟩
  intro live base held
  rcases (transport.live live).2 with impossible | word
  · exact False.elim impossible
  · exact word.maskChain base held

/-- Observer and interrupt edits retain live transport. -/
theorem OtherEdits.transport {allowClear : Prop} {f g : NFiber} (w : OtherEdits f g) :
    Transport allowClear f g := by
  induction w with
  | refl => exact .refl _ _
  | tail _ e ih =>
    apply ih.trans
    cases e with
    | observe => exact .edit rfl rfl (.refl _)
    | filterObservers => exact .edit rfl rfl (.refl _)
    | interrupted interp _ who extra =>
      exact .edit (OtherEdit.id (.interrupted interp _ who extra))
        (OtherEdit.exit (.interrupted interp _ who extra))
        (.single (.interrupted interp _ who extra))

/-- Joint command classification retains one initialization for each allocated id.
The parameter distinguishes raw clearing from the guarded live word. -/
structure Transports (allowClear : Prop) (m m' : NativeMachine) : Prop where
  nextId : m.nextId ≤ m'.nextId
  births : ∃ born : Nat → Birth, ∀ g' ∈ m'.fibers,
    (∃ g ∈ m.fibers, Transport allowClear g g') ∨
    (m.nextId ≤ g'.id.value ∧ g'.id.value < m'.nextId ∧
      Transport allowClear ((born g'.id.value).fiber g'.id) g')

/-- The existing per-fiber interface projects the coherent birth table. -/
theorem Transports.fibers {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (g' : NFiber) (member : g' ∈ m'.fibers) :
    (∃ g ∈ m.fibers, Transport allowClear g g') ∨
    (m.nextId ≤ g'.id.value ∧ ∃ program flag budget context,
      Transport allowClear (RunFiber.make g'.id program flag budget context) g') := by
  obtain ⟨born, rows⟩ := h.births
  rcases rows g' member with old | ⟨lower, _, word⟩
  · exact .inl old
  · exact .inr ⟨lower, (born g'.id.value).program, (born g'.id.value).flag,
      (born g'.id.value).budget, (born g'.id.value).context, word⟩

/-- No command transports every existing fiber to itself. -/
theorem Transports.refl (allowClear : Prop) (m : NativeMachine) : Transports allowClear m m :=
  ⟨Nat.le_refl _, fun _ => Birth.empty, fun g mem => .inl ⟨g, mem, .refl _ _⟩⟩

/-- Command transport composes through the two adjacent allocation intervals. -/
theorem Transports.trans {allowClear : Prop} {m m' m'' : NativeMachine}
    (a : Transports allowClear m m') (b : Transports allowClear m' m'') :
    Transports allowClear m m'' := by
  obtain ⟨first, rows⟩ := a.births
  obtain ⟨second, rows'⟩ := b.births
  refine ⟨Nat.le_trans a.nextId b.nextId, fun n => if n < m'.nextId then first n else second n,
    fun last member => ?_⟩
  rcases rows' last member with ⟨middle, member', word'⟩ | ⟨lower, upper, word⟩
  · rcases rows middle member' with ⟨initial, before, word⟩ | ⟨lower, upper, word⟩
    · exact .inl ⟨initial, before, word.trans word'⟩
    · refine .inr ⟨word'.id ▸ lower, ?_, ?_⟩
      · rw [word'.id]
        exact Nat.lt_of_lt_of_le upper b.nextId
      · dsimp only
        rw [word'.id, if_pos upper]
        exact word.trans word'
  · refine .inr ⟨Nat.le_trans a.nextId lower, upper, ?_⟩
    dsimp only
    rw [if_neg (Nat.not_lt.mpr lower)]
    exact word

/-- An already allocated live fiber has a live predecessor and a clearing-free frame word.
Consumer: the goals packet's fiber positions and the region bracket's run relation. -/
theorem Transports.liveOld {m m' : NativeMachine} (h : Transports False m m')
    {g : NFiber} (member : g ∈ m'.fibers) (live : g.exit = none) (old : g.id.value < m.nextId) :
    ∃ f ∈ m.fibers, f.id = g.id ∧ f.exit = none ∧ LiveEdits f.frame g.frame := by
  rcases h.fibers g member with ⟨f, before, word⟩ | born
  · obtain ⟨wasLive, noClear⟩ := word.live live
    rcases noClear with impossible | edits
    · exact False.elim impossible
    · exact ⟨f, before, word.id.symm, wasLive, edits⟩
  · exact False.elim (Nat.not_le_of_lt old born.1)

/-- Evaluation interference has no clearing edit and retains the same birth table. -/
theorem Transports.ofInterferes {allowClear : Prop} {m m' : NativeMachine} (h : Interferes m m') :
    Transports allowClear m m' := by
  obtain ⟨born, rows⟩ := h.births
  refine ⟨h.nextId, born, fun g mem => ?_⟩
  rcases rows g mem with ⟨f, before, edits⟩ | ⟨lower, upper, edits⟩
  · exact .inl ⟨f, before, edits.transport⟩
  · exact .inr ⟨lower, upper, edits.transport⟩

/-- The shared birth table supplies the whole-machine mask instance without choice.
Consumer: the native evaluator and guarded command halves of the saved-mask chain. -/
theorem Transports.maskAged {m m' : NativeMachine} (h : Transports False m m') :
    MaskAged m m' := by
  obtain ⟨born, rows⟩ := h.births
  refine ⟨h.nextId, fun n => (born n).flag, fun g member => ?_⟩
  rcases rows g member with ⟨f, before, word⟩ | ⟨lower, upper, word⟩
  · exact .inl ⟨f, before, word.maskLater⟩
  · exact .inr ⟨lower, upper, fun live => word.maskLater.2.2 live _ rfl⟩

/-- Evaluation interference specializes through the same mask instance. -/
theorem Interferes.maskAged {m m' : NativeMachine} (h : Interferes m m') : MaskAged m m' :=
  (Transports.ofInterferes (allowClear := False) h).maskAged

/-- Forget the live and initialized-frame witnesses. -/
theorem Transports.frames {allowClear : Prop} {m m' : NativeMachine} (h : Transports allowClear m m') :
    FramesFollow m m' := by
  refine ⟨h.nextId, fun g mem => ?_⟩
  rcases h.fibers g mem with ⟨f, before, edits⟩ | fresh
  · exact .inl ⟨f, before, edits.id.symm, edits.frame⟩
  · exact .inr fresh.1

/-- Changes outside the fiber table retain its transport and allocation interval. -/
theorem Transports.thenSame {allowClear : Prop} {m m' m'' : NativeMachine}
    (h : Transports allowClear m m') (fibers : m''.fibers = m'.fibers)
    (nextId : m'.nextId ≤ m''.nextId) : Transports allowClear m m'' := by
  obtain ⟨born, rows⟩ := h.births
  refine ⟨Nat.le_trans h.nextId nextId, born, fun g member => ?_⟩
  rcases rows g (fibers ▸ member) with old | ⟨lower, upper, word⟩
  · exact .inl old
  · exact .inr ⟨lower, Nat.lt_of_lt_of_le upper nextId, word⟩

/-- Write a transported fiber from the original machine; no birth witness changes. -/
theorem Transports.thenWrite {allowClear : Prop} {m m' : NativeMachine} {t : NFiber}
    (h : Transports allowClear m m') (source : ∃ g ∈ m.fibers, Transport allowClear g t) :
    Transports allowClear m (m'.update t) := by
  obtain ⟨born, rows⟩ := h.births
  refine ⟨h.nextId, born, fun g' mem => ?_⟩
  unfold RunMachine.update at mem
  obtain ⟨g, memMid, eq⟩ := List.mem_map.mp mem
  split at eq
  · exact eq ▸ .inl source
  · exact eq ▸ rows g memMid

/-- A table member's next edit uses its existing birth entry when the fiber is fresh. -/
theorem Transports.thenUpdate {allowClear : Prop} {m m' : NativeMachine} {t t' : NFiber}
    (h : Transports allowClear m m') (mem : t ∈ m'.fibers) (edit : Transport allowClear t t') :
    Transports allowClear m (m'.update t') := by
  obtain ⟨born, rows⟩ := h.births
  refine ⟨h.nextId, born, fun g' member => ?_⟩
  unfold RunMachine.update at member
  obtain ⟨g, before, same⟩ := List.mem_map.mp member
  split at same
  · subst g'
    rcases rows t mem with ⟨initial, present, word⟩ | ⟨lower, upper, word⟩
    · exact .inl ⟨initial, present, word.trans edit⟩
    · refine .inr ⟨edit.id ▸ lower, edit.id ▸ upper, ?_⟩
      rw [edit.id]
      exact word.trans edit
  · exact same ▸ rows g before

/-- An edit outside a fiber's frame and exit retains its transport. -/
theorem Transports.thenModify {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (id : FiberId) (k : NFiber → NFiber)
    (frame : ∀ g, (k g).frame = g.frame) (keepsId : ∀ g, (k g).id = g.id)
    (exit : ∀ g, (k g).exit = g.exit) : Transports allowClear m (m'.modify id k) := by
  unfold RunMachine.modify
  split
  · exact h
  · rename_i g found
    exact h.thenUpdate (List.mem_of_find?_eq_some found)
      (.edit (keepsId g) (exit g) (frame g ▸ .refl _))

/-- Trace append retains transport. -/
theorem Transports.thenEmit {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (events : List NRunEvent) : Transports allowClear m (m'.emit events) :=
  h.thenSame rfl (Nat.le_refl _)

/-- Halting retains transport. -/
theorem Transports.thenHalt {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (why : Stuck) : Transports allowClear m (m'.halt why) :=
  h.thenSame rfl (Nat.le_refl _)

/-- A store write retains transport. -/
theorem Transports.thenState {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (state : Stores) : Transports allowClear m { m' with state := state } :=
  h.thenSame rfl (Nat.le_refl _)

/-- A race write retains transport. -/
theorem Transports.thenUpdateRace {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (race : Race EffName EffThunk Val Err Defect FiberId Ann) :
    Transports allowClear m (m'.updateRace race) := h.thenSame rfl (Nat.le_refl _)

/-- Arming retains transport. -/
theorem Transports.thenArm {allowClear : Prop} {m m' : NativeMachine}
    (h : Transports allowClear m m') (owner : FiberId) : Transports allowClear m (m'.arm owner) :=
  h.thenSame rfl (Nat.le_refl _)

/-- A race's entrant is a spawn. -/
theorem Interferes.launchEntrant (interp : NInterp) (raceId : Nat) (m : NativeMachine)
    (host : NFiber) (program : NCode) (site : List Nat) :
    Interferes m (Machine.launchEntrant interp raceId m host program site).1 := by
  unfold Machine.launchEntrant
  have spawned := Interferes.spawn interp m host program
    ⟨true, true, Supervision.MaskMode.interruptible⟩ site
  rcases split : Machine.spawn interp m host program
      ⟨true, true, Supervision.MaskMode.interruptible⟩ site with ⟨m1, parent, child⟩
  rw [split] at spawned
  exact spawned

/-- Settle writes the evaluated fiber, retaining its joint frame transport. -/
theorem settle_transports {allowClear : Prop} {m : NativeMachine} {f : NFiber}
    (mem : f ∈ m.fibers) (id : FiberId) (rest : List NCommand) (it : NIter)
    (machine : Transports allowClear m it.machine) (fiber : Transport allowClear f it.fiber) :
    Transports allowClear m (settle id rest it).1 := by
  have source : ∃ g ∈ m.fibers, Transport allowClear g it.fiber := ⟨f, mem, fiber⟩
  unfold settle
  split
  · exact machine.thenWrite source
  · exact machine.thenWrite source
  · split
    · exact machine.thenWrite source
    · exact machine.thenWrite source
  · exact machine.thenWrite source
  · exact machine.thenWrite source
  · apply Transports.thenHalt
    exact machine.thenWrite source

/-- A native loop iteration supplies both its other-fiber edits and its evaluated-fiber word. -/
theorem loop_transports {allowClear : Prop} (root : NativeEff) (table : RowTable) (interp : NInterp)
    {m : NativeMachine} {f : NFiber} (mem : f ∈ m.fibers) (id : FiberId)
    (yielding : Bool) (rest : List NCommand) :
    Transports allowClear m
      (settle id rest (iteration (evaluator := evaluatorFor root table) interp m f yielding)).1 := by
  have footprint := iteration_footprint root table interp m f yielding
  exact settle_transports mem id rest _
    (.ofInterferes (iteration_interferes root table interp m f yielding))
    (.edit footprint.id footprint.exit (.ofMoves footprint.frame))

/-- A native delivery supplies the same joint transport. -/
theorem deliver_transports {allowClear : Prop} (root : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (mem : f ∈ m.fibers) (id : FiberId)
    (yielding : Bool) (rest : List NCommand) :
    Transports allowClear m (settle id rest (evaluateNative root m f yielding table)).1 := by
  have footprint := evaluateNative_footprint root table m f yielding
  exact settle_transports mem id rest _
    (.ofInterferes (evaluateNative_interferes root table m f yielding))
    (.edit footprint.id footprint.exit (.ofMoves footprint.frame))

/-- Interrupt each target through the same clearing-free record edit. -/
theorem interruptEach_transports {allowClear : Prop} (interp : NInterp) (who : FiberId)
    (extra : ReasonAnnotations Ann) :
    ∀ (targets : List FiberId) {m : NativeMachine} (acc : NativeMachine × List NCommand),
      Transports allowClear m acc.1 → Transports allowClear m (interruptEach interp who extra targets acc).1
  | [], _, acc, h => h
  | t :: rest, m, acc, h => by
    unfold interruptEach
    simp only [List.foldl_cons]
    apply interruptEach_transports interp who extra rest
    split
    · exact h
    · rename_i g found
      apply Transports.thenEmit
      exact h.thenUpdate (List.mem_of_find?_eq_some found)
        (.edit (OtherEdit.id (.interrupted interp g (some who) extra))
          (OtherEdit.exit (.interrupted interp g (some who) extra))
          (.single (.interrupted interp g (some who) extra)))

/-- Store wakeups preserve frame transport while posting their commands. -/
theorem drainOwed_transports {allowClear : Prop} {m : NativeMachine} :
    ∀ (m' : NativeMachine) (owed : List (Owed NCode)), Transports allowClear m m' →
      Transports allowClear m (drainOwed m' owed).1
  | m', [], h => h
  | m', d :: rest, h => by
    unfold drainOwed
    split
    · exact drainOwed_transports m' rest h
    · apply drainOwed_transports
      unfold RunMachine.postTask
      split
      · exact h.thenHalt _
      · rename_i o found
        apply Transports.thenEmit
        apply Transports.thenArm
        exact h.thenUpdate (List.mem_of_find?_eq_some found) (.edit rfl rfl (.refl _))

/-- An observer changes bookkeeping or records an interrupt; it clears no live frame. -/
theorem fireObserver_transports {allowClear : Prop} (interp : NInterp) {m : NativeMachine}
    (id : FiberId) (exit : ExitV) (acc : NativeMachine × List NCommand)
    (h : Transports allowClear m acc.1) (observer : Observer) :
    Transports allowClear m (fireObserver interp id exit acc observer).1 := by
  apply h.trans
  have base : Transports allowClear acc.1 acc.1 := .refl _ _
  unfold fireObserver
  dsimp only
  split
  · exact base.thenEmit _
  · exact (base.thenEmit _).thenModify _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · split
    · exact (base.thenEmit _).thenHalt _
    · exact (base.thenEmit _).thenState _
  · split
    · exact base.thenEmit _
    · rename_i w found
      split
      · exact base.thenEmit _
      · rename_i p pending
        have source : ∃ g ∈ acc.1.fibers, Transport allowClear g w :=
          ⟨w, List.mem_of_find?_eq_some found, .refl _ _⟩
        split
        · refine Transports.thenWrite ?_ source
          split
          · exact interruptEach_transports interp _ _ _ _ (base.thenEmit _)
          · exact base.thenEmit _
        · refine Transports.thenWrite ?_ source
          refine Transports.thenModify ?_ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          split
          · exact interruptEach_transports interp _ _ _ _ (base.thenEmit _)
          · exact base.thenEmit _
  · split
    · exact base.thenEmit _
    · split
      · exact (((base.thenEmit _).thenUpdateRace _).thenUpdateRace _).thenEmit _
      · exact (base.thenEmit _).thenUpdateRace _
  · exact (base.thenEmit _).thenEmit _

/-- Publication permits clearing only after the exit is present; the children branch retains a live word. -/
theorem exitFiber_transports {allowClear : Prop} (interp : NInterp) {m : NativeMachine}
    {f : NFiber} (mem : f ∈ m.fibers) (exit : ExitV) :
    Transports allowClear m (exitFiber interp m { f with running := false } exit).1 := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    apply Transports.thenEmit
    exact (Transports.refl _ m).thenUpdate mem
      (.edit rfl rfl (.tail (.single (.setDeferred _ false)) (.move (.answer _ _))))
  · unfold exitFiber.exitStore
    dsimp only
    split
    · refine Transports.thenWrite ?_
        ⟨f, mem, .exited rfl
          (.tail (.single (.setDeferred f.frame false)) (.clearStack _)) rfl⟩
      apply Transports.thenEmit
      exact (Transports.refl _ m).thenUpdate mem
        (.exited rfl (.single (.setDeferred _ false)) rfl)
    · apply Transports.thenEmit
      exact (Transports.refl _ m).thenUpdate mem
        (.exited rfl (.single (.setDeferred _ false)) rfl)

/-- One census serves raw commands and commands whose clear target has exited.
The guarded instance supplies a live word with no `clearStack` edit.
It retains actual initialized fibers without asserting ownership of their source program. -/
@[semantics "reactive-scheduling"]
theorem driveStep_transports {allowClear : Prop} (root : NativeEff) (table : RowTable)
    (interp : NInterp) (m : NativeMachine) (c : NCommand) (rest : List NCommand)
    (clear : ∀ id, c = .exitDone id → ∀ f, m.fiber? id = some f → f.exit = none → allowClear) :
    Transports allowClear m (driveStep (evaluator := evaluatorFor root table) interp m c rest).1 := by
  cases c with
  | evaluate id =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      split
      · exact .refl _ _
      · apply Transports.thenEmit
        exact (Transports.refl _ m).thenUpdate (List.mem_of_find?_eq_some found)
          (.edit rfl rfl (.refl _))
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      exact loop_transports root table interp (List.mem_of_find?_eq_some found) id yielding rest
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      exact deliver_transports root table (List.mem_of_find?_eq_some found) id yielding rest
  | finish id exit =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      exact exitFiber_transports interp (List.mem_of_find?_eq_some found) exit
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i t found
      split
      · split
        · apply Transports.thenEmit
          exact (Transports.refl _ m).thenUpdate (List.mem_of_find?_eq_some found)
            (.edit rfl rfl (.single (.move (.answer _ _))))
        · exact .refl _ _
      · exact .refl _ _
  | launch raceId =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · split
      · exact .refl _ _
      · split
        · exact .refl _ _
        · split
          · exact .refl _ _
          · exact ((Transports.ofInterferes (Interferes.launchEntrant _ _ _ _ _ _)).thenUpdateRace _).thenEmit _
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · split
      · exact fireObserver_transports interp _ _ _ ((Transports.refl _ m).thenUpdateRace _) _
      · exact ((Transports.refl _ m).thenUpdateRace _).thenModify _ _
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    · exact .refl _ _
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · split
      · exact (Transports.refl _ m).thenUpdateRace _
      · rename_i f foundHost
        split
        · exact settle_transports (m := m) (List.mem_of_find?_eq_some foundHost) _ rest _
            ((Transports.refl _ m).thenUpdateRace _) (.edit rfl rfl (.single (.move (.answer _ _))))
        · exact settle_transports (m := m) (List.mem_of_find?_eq_some foundHost) _ rest _
            (((Transports.refl _ m).thenUpdateRace _).thenEmit _) (.edit rfl rfl (.single (.move (.push _ _))))
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i g found
      exact ((Transports.refl _ m).thenUpdate (List.mem_of_find?_eq_some found)
        (.edit (OtherEdit.id (.interrupted interp g who extra))
          (OtherEdit.exit (.interrupted interp g who extra))
          (.single (.interrupted interp g who extra)))).thenEmit _
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      exact settle_transports (List.mem_of_find?_eq_some found) _ rest _ (.refl _ m)
        (.edit rfl rfl (.single (.move (.answer _ _))))
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · split
      · exact .refl _ _
      · split <;> exact .refl _ _
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · split
      · exact .refl _ _
      · refine Transports.thenModify ?_ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        exact (Transports.refl _ m).thenModify _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | observe id exit observer =>
    simp only [driveStep]
    exact fireObserver_transports interp id exit (m, []) (.refl _ m) observer
  | exitDone id =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      exact (Transports.refl _ m).thenUpdate (List.mem_of_find?_eq_some found)
        (.clear rfl rfl rfl (clear id rfl f found))
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact .refl _ _
    · rename_i f found
      exact settle_transports (List.mem_of_find?_eq_some found) _ rest _ (.refl _ m)
        (.edit rfl rfl (.tail (.single (.pushIterator _ _ _)) (.move (.answer _ _))))
  | link mode scope target interruptor extra =>
    simp only [driveStep]
    exact .ofInterferes (Interferes.linkScope _ _ _ _ _ _ _)
  | drainDue =>
    simp only [driveStep]
    exact drainOwed_transports _ _ ((Transports.refl _ m).thenState _)
  | wake list phase =>
    simp only [driveStep]
    exact (Transports.refl _ m).thenState _

/-- The original raw frame classification is a projection of the joint command census. -/
@[semantics "reactive-scheduling"]
theorem driveStep_framesFollow (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (c : NCommand) (rest : List NCommand) :
    FramesFollow m (driveStep (evaluator := evaluatorFor root table) interp m c rest).1 :=
  (driveStep_transports (allowClear := True) root table interp m c rest
    (fun _ _ _ _ _ => True.intro)).frames

/-- An admitted clear command targets an exited fiber; every live successor retains a clearing-free word. -/
@[semantics "reactive-scheduling"]
theorem driveStep_liveTransports (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (c : NCommand) (rest : List NCommand)
    (clear : ∀ id, c = .exitDone id → ∀ f, m.fiber? id = some f → f.exit.isSome = true) :
    Transports False m (driveStep (evaluator := evaluatorFor root table) interp m c rest).1 := by
  apply driveStep_transports
  intro id command f found live
  have exited := clear id command f found
  rw [live] at exited
  cases exited

end Effect4.Program.Moves
