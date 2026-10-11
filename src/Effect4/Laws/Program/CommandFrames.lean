import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.Footprint
import Effect4.Laws.Program.StackLocal

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
* **The classification** (`driveStep_framesFollow`): every command of the native loop.

So a frame invariant that each edit keeps, and that holds of a new fiber's frame, holds after every
command. `MaskRuns`'s command half is such an invariant, and so is the shape stack locality asks
for, between the edits that reach the entry's stack.

Placement (AGENTS.md, Trust):

- concept `reactive-scheduling` (`docs/core/semantics.md` §2.4); the proposed registry claim
  `command-moves`, role structure, of which this is the frame half;
- reach: every command of the native loop (`driveStep` at `evaluatorFor root table`), every
  interpreter, machine and pending list;
- it states frames and ids alone: the stores, the queues, the races, the scheduling fields and a new
  fiber's frame are outside it, and so is which command runs;
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

/-- An evaluation's interference: other fibers' frames follow. -/
theorem FramesFollow.ofInterferes {m m' : NativeMachine} (h : Interferes m m') :
    FramesFollow m m' := by
  refine ⟨h.nextId, fun g' mem => ?_⟩
  rcases h.fibers g' mem with ⟨g, memOld, w⟩ | fresh
  · exact .inl ⟨g, memOld, w.id.symm, w.frames⟩
  · exact .inr fresh

/-- A machine edit that keeps the fiber list, after frames that follow. -/
theorem FramesFollow.thenSame {m m' m'' : NativeMachine} (h : FramesFollow m m')
    (fibers : m''.fibers = m'.fibers) (nextId : m'.nextId ≤ m''.nextId) : FramesFollow m m'' :=
  ⟨Nat.le_trans h.nextId nextId, fun g mem => h.fibers g (fibers ▸ mem)⟩

/-- Writing one fiber whose frame follows from an old fiber of the same id, or which is new. -/
theorem FramesFollow.thenWrite {m m' : NativeMachine} {t : NFiber} (h : FramesFollow m m')
    (source : (∃ g ∈ m.fibers, g.id = t.id ∧ FrameEdits g.frame t.frame) ∨ m.nextId ≤ t.id.value) :
    FramesFollow m (m'.update t) := by
  refine ⟨h.nextId, fun g' mem => ?_⟩
  unfold RunMachine.update at mem
  obtain ⟨g, memMid, eq⟩ := List.mem_map.mp mem
  split at eq
  · exact eq ▸ source
  · exact eq ▸ h.fibers g memMid

/-- Writing a fiber of `m'` back after editing its frame and keeping its id. -/
theorem FramesFollow.thenUpdate {m m' : NativeMachine} {t t' : NFiber} (h : FramesFollow m m')
    (mem : t ∈ m'.fibers) (id : t'.id = t.id) (edits : FrameEdits t.frame t'.frame) :
    FramesFollow m (m'.update t') := by
  refine h.thenWrite ?_
  rcases h.fibers t mem with ⟨g, memOld, idOld, w⟩ | fresh
  · exact .inl ⟨g, memOld, idOld.trans id.symm, w.trans edits⟩
  · exact .inr (id ▸ fresh)

/-- Editing the fiber an id names, keeping its frame and its id. -/
theorem FramesFollow.thenModify {m m' : NativeMachine} (h : FramesFollow m m') (id : FiberId)
    (k : NFiber → NFiber) (frame : ∀ g, (k g).frame = g.frame) (keepsId : ∀ g, (k g).id = g.id) :
    FramesFollow m (m'.modify id k) := by
  unfold RunMachine.modify
  split
  · exact h
  · rename_i g found
    exact h.thenUpdate (List.mem_of_find?_eq_some found) (keepsId g) (frame g ▸ .refl _)

/-- Appending to the trace, after frames that follow. -/
theorem FramesFollow.thenEmit {m m' : NativeMachine} (h : FramesFollow m m') (events : List NRunEvent) :
    FramesFollow m (m'.emit events) :=
  h.thenSame rfl (Nat.le_refl _)

/-- Halting, after frames that follow. -/
theorem FramesFollow.thenHalt {m m' : NativeMachine} (h : FramesFollow m m') (why : Stuck) :
    FramesFollow m (m'.halt why) :=
  h.thenSame rfl (Nat.le_refl _)

/-- Writing the stores, after frames that follow. -/
theorem FramesFollow.thenState {m m' : NativeMachine} (h : FramesFollow m m') (state : Stores) :
    FramesFollow m { m' with state := state } :=
  h.thenSame rfl (Nat.le_refl _)

/-- Writing a race, after frames that follow. -/
theorem FramesFollow.thenUpdateRace {m m' : NativeMachine} (h : FramesFollow m m')
    (race : Race EffName EffThunk Val Err Defect FiberId Ann) :
    FramesFollow m (m'.updateRace race) :=
  h.thenSame rfl (Nat.le_refl _)

/-- Arming a dispatcher, after frames that follow. -/
theorem FramesFollow.thenArm {m m' : NativeMachine} (h : FramesFollow m m') (owner : FiberId) :
    FramesFollow m (m'.arm owner) :=
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

/-- **Where the loop leaves an evaluated fiber**: it writes the evaluation's fiber back, whose frame
followed from the old one. -/
theorem settle_follows {m : NativeMachine} {f : NFiber} (mem : f ∈ m.fibers) (id : FiberId)
    (rest : List NCommand) (it : NIter) (machine : FramesFollow m it.machine)
    (frame : FrameEdits f.frame it.fiber.frame) (sameId : it.fiber.id = f.id) :
    FramesFollow m (settle id rest it).1 := by
  have source : (∃ g ∈ m.fibers, g.id = it.fiber.id ∧ FrameEdits g.frame it.fiber.frame) ∨
      m.nextId ≤ it.fiber.id.value := .inl ⟨f, mem, sameId.symm, frame⟩
  unfold settle
  split
  · exact machine.thenWrite source
  · exact machine.thenWrite source
  · split
    · exact machine.thenWrite source
    · exact machine.thenWrite source
  · exact machine.thenWrite source
  · exact machine.thenWrite source
  · apply FramesFollow.thenHalt
    exact machine.thenWrite source

/-- A loop command: one iteration of the native loop, settled. -/
theorem loop_follows (root : NativeEff) (table : RowTable) (interp : NInterp) {m : NativeMachine}
    {f : NFiber} (mem : f ∈ m.fibers) (id : FiberId) (yielding : Bool) (rest : List NCommand) :
    FramesFollow m
      (settle id rest (iteration (evaluator := evaluatorFor root table) interp m f yielding)).1 :=
  settle_follows mem id rest _ (.ofInterferes (iteration_interferes root table interp m f yielding))
    (.ofMoves (iteration_moves root table interp m f yielding))
    (iteration_footprint root table interp m f yielding).id

/-- A delivery: one native evaluation, settled. -/
theorem deliver_follows (root : NativeEff) (table : RowTable) {m : NativeMachine}
    {f : NFiber} (mem : f ∈ m.fibers) (id : FiberId) (yielding : Bool) (rest : List NCommand) :
    FramesFollow m (settle id rest (evaluateNative root m f yielding table)).1 :=
  settle_follows mem id rest _ (.ofInterferes (evaluateNative_interferes root table m f yielding))
    (.ofMoves (evaluateNative_moves root table m f yielding))
    (evaluateNative_footprint root table m f yielding).id

/-- Interrupts recorded on each target in turn. -/
theorem interruptEach_follows (interp : NInterp) (who : FiberId) (extra : ReasonAnnotations Ann) :
    ∀ (targets : List FiberId) {m : NativeMachine} (acc : NativeMachine × List NCommand),
      FramesFollow m acc.1 → FramesFollow m (interruptEach interp who extra targets acc).1
  | [], _, acc, h => h
  | t :: rest, m, acc, h => by
    unfold interruptEach
    simp only [List.foldl_cons]
    apply interruptEach_follows interp who extra rest
    split
    · exact h
    · rename_i g found
      apply FramesFollow.thenEmit
      exact h.thenUpdate (List.mem_of_find?_eq_some found) (OtherEdit.interrupted interp g (some who) extra).id
        (.single (.interrupted interp g (some who) extra))

/-- The resumes a store owes, posted or run. -/
theorem drainOwed_follows {m : NativeMachine} :
    ∀ (m' : NativeMachine) (owed : List (Owed NCode)), FramesFollow m m' →
      FramesFollow m (drainOwed m' owed).1
  | m', [], h => h
  | m', d :: rest, h => by
    unfold drainOwed
    split
    · exact drainOwed_follows m' rest h
    · apply drainOwed_follows
      unfold RunMachine.postTask
      split
      · exact h.thenHalt _
      · rename_i o found
        apply FramesFollow.thenEmit
        apply FramesFollow.thenArm
        exact h.thenUpdate (List.mem_of_find?_eq_some found) rfl (.refl _)

/-- One observer of an exited fiber runs. -/
theorem fireObserver_follows (interp : NInterp) {m : NativeMachine} (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List NCommand) (h : FramesFollow m acc.1) (observer : Observer) :
    FramesFollow m (fireObserver interp id exit acc observer).1 := by
  unfold fireObserver
  dsimp only
  split
  · exact h.thenEmit _
  · refine FramesFollow.thenModify ?_ _ _ (fun _ => rfl) (fun _ => rfl)
    exact h.thenEmit _
  · split
    · exact (h.thenEmit _).thenHalt _
    · apply FramesFollow.thenState
      exact h.thenEmit _
  · split
    · exact h.thenEmit _
    · rename_i w found
      split
      · exact h.thenEmit _
      · rename_i p pending
        have source : (∃ g ∈ m.fibers, g.id = w.id ∧ FrameEdits g.frame w.frame) ∨
            m.nextId ≤ w.id.value := by
          rcases (h.thenEmit _).fibers w (List.mem_of_find?_eq_some found) with
            ⟨g, mem, idEq, edits⟩ | fresh
          · exact .inl ⟨g, mem, idEq, edits⟩
          · exact .inr fresh
        split
        · refine FramesFollow.thenWrite ?_ source
          split
          · exact interruptEach_follows interp _ _ _ _ (h.thenEmit _)
          · exact h.thenEmit _
        · refine FramesFollow.thenWrite ?_ source
          refine FramesFollow.thenModify ?_ _ _ (fun _ => rfl) (fun _ => rfl)
          split
          · exact interruptEach_follows interp _ _ _ _ (h.thenEmit _)
          · exact h.thenEmit _
  · split
    · exact h.thenEmit _
    · split
      · apply FramesFollow.thenEmit
        apply FramesFollow.thenUpdateRace
        apply FramesFollow.thenUpdateRace
        exact h.thenEmit _
      · apply FramesFollow.thenUpdateRace
        exact h.thenEmit _
  · exact (h.thenEmit _).thenEmit _

/-- The exit path of a fiber whose frame follows from an old one: publish (the deferred bit
cleared), clear when no observer waits, or re-enter with the children's interrupt. -/
theorem exitFiber_follows (interp : NInterp) {m : NativeMachine} {f : NFiber} (mem : f ∈ m.fibers)
    (exit : ExitV) : FramesFollow m (exitFiber interp m { f with running := false } exit).1 := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    apply FramesFollow.thenEmit
    exact (FramesFollow.refl m).thenUpdate mem rfl
      (.tail (.single (.setDeferred _ false)) (.move (.answer _ _)))
  · unfold exitFiber.exitStore
    dsimp only
    split
    · refine FramesFollow.thenWrite ?_
        (.inl ⟨f, mem, rfl, .tail (.single (.setDeferred f.frame false)) (.clearStack _)⟩)
      apply FramesFollow.thenEmit
      exact (FramesFollow.refl m).thenUpdate mem rfl (.single (.setDeferred _ false))
    · apply FramesFollow.thenEmit
      exact (FramesFollow.refl m).thenUpdate mem rfl (.single (.setDeferred _ false))

/-- **Every command of the native loop**: the frames of the machine after it follow from the frames
before it, by a word of frame edits per fiber, or the fiber is new. The pointer of the frame half of
the proposed claim `command-moves`. -/
@[semantics "reactive-scheduling"]
theorem driveStep_framesFollow (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (c : NCommand) (rest : List NCommand) :
    FramesFollow m (driveStep (evaluator := evaluatorFor root table) interp m c rest).1 := by
  cases c with
  | evaluate id =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      split
      · exact .refl _
      · apply FramesFollow.thenEmit
        exact (FramesFollow.refl m).thenUpdate (List.mem_of_find?_eq_some found) rfl (.refl _)
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      exact loop_follows root table interp (List.mem_of_find?_eq_some found) id yielding rest
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      exact deliver_follows root table (List.mem_of_find?_eq_some found) id yielding rest
  | finish id exit =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      exact exitFiber_follows interp (List.mem_of_find?_eq_some found) exit
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i t found
      split
      · split
        · apply FramesFollow.thenEmit
          exact (FramesFollow.refl m).thenUpdate (List.mem_of_find?_eq_some found) rfl
            (.single (.move (.answer _ _)))
        · exact .refl _
      · exact .refl _
  | launch raceId =>
    simp only [driveStep]
    split
    · exact .refl _
    · split
      · exact .refl _
      · split
        · exact .refl _
        · split
          · exact .refl _
          · apply FramesFollow.thenEmit
            apply FramesFollow.thenUpdateRace
            exact .ofInterferes (Interferes.launchEntrant _ _ _ _ _ _)
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · split
      · exact fireObserver_follows interp _ _ _ ((FramesFollow.refl m).thenUpdateRace _) _
      · exact ((FramesFollow.refl m).thenUpdateRace _).thenModify _ _ (fun _ => rfl) (fun _ => rfl)
    · exact .refl _
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact .refl _
    · split
      · exact (FramesFollow.refl m).thenUpdateRace _
      · rename_i f foundHost
        split
        · exact settle_follows (m := m) (List.mem_of_find?_eq_some foundHost) _ rest _
            ((FramesFollow.refl m).thenUpdateRace _) (.single (.move (.answer _ _))) rfl
        · exact settle_follows (m := m) (List.mem_of_find?_eq_some foundHost) _ rest _
            (((FramesFollow.refl m).thenUpdateRace _).thenEmit _) (.single (.move (.push _ _))) rfl
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i g found
      apply FramesFollow.thenEmit
      exact (FramesFollow.refl m).thenUpdate (List.mem_of_find?_eq_some found)
        (OtherEdit.interrupted interp g who extra).id (.single (.interrupted interp g who extra))
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      exact settle_follows (List.mem_of_find?_eq_some found) _ rest _ (.refl m)
        (.single (.move (.answer _ _))) rfl
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    split
    · exact .refl _
    · split
      · exact .refl _
      · split <;> exact .refl _
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact .refl _
    · split
      · exact .refl _
      · refine FramesFollow.thenModify ?_ _ _ (fun _ => rfl) (fun _ => rfl)
        exact (FramesFollow.refl m).thenModify _ _ (fun _ => rfl) (fun _ => rfl)
  | observe id exit observer =>
    simp only [driveStep]
    exact fireObserver_follows interp id exit (m, []) (.refl m) observer
  | exitDone id =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      exact (FramesFollow.refl m).thenUpdate (List.mem_of_find?_eq_some found) rfl
        (.single (.clearStack _))
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact .refl _
    · rename_i f found
      exact settle_follows (List.mem_of_find?_eq_some found) _ rest _ (.refl m)
        (.tail (.single (.pushIterator _ _ _)) (.move (.answer _ _))) rfl
  | link mode scope target interruptor extra =>
    simp only [driveStep]
    exact .ofInterferes (Interferes.linkScope _ _ _ _ _ _ _)
  | drainDue =>
    simp only [driveStep]
    exact drainOwed_follows _ _ ((FramesFollow.refl m).thenState _)
  | wake list phase =>
    simp only [driveStep]
    exact (FramesFollow.refl m).thenState _

end Effect4.Program.Moves
