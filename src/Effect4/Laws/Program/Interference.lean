import Effect4.Laws.Program.Moves
import Effect4.Laws.Machine.Keeps

/-!
# Laws.Program.Interference — what one evaluation does to the machine's other fibers

One native evaluation runs one fiber. It reads and writes the machine too: it spawns children, adds
an observer to a fiber it waits on, records an interrupt on a target, and filters every fiber's
observers by a cancelled token. This module states that list once:

* **The edits of another fiber** (`OtherEdit`, `OtherEdits`): an observer appended, observers
  filtered, an interrupt recorded (`interruptRecord`). Nothing else of another fiber changes.
* **The machine's interference** (`Interferes m m'`): the id counter does not go back, and every
  fiber of `m'` is a fiber of `m` with the same id under a word of edits, or is new: its id is at
  least `m`'s counter, with its initial program, flags, budget and context retained through edits.
* **The classification** (`evaluatePrim_interferes`, `exitScoped_interferes`,
  `evaluateNative_interferes`, `iteration_interferes`).

This is Owicki and Gries's non-interference made one theorem for an evaluation: an assertion about
another fiber that each listed edit keeps, and that holds of a spawned fiber, is kept by every
evaluation. `MaskAged` (`Laws/Machine/MaskRuns.lean`) is its instance at the mask's fields.

Placement (AGENTS.md, Trust):

- concept `reactive-scheduling` (`docs/core/semantics.md` §2.4, invariants over execution traces,
  Owicki and Gries); the proposed registry claim is `command-moves`, role structure, of which this
  is the evaluation's half;
- reach: every native evaluation and iteration, at every machine, fiber, interpreter, row table and
  latch. It states the machine's fiber list and id counter; the stores, the races, the queues and
  the trace are outside it, and so is the evaluated fiber's own new state (`Footprint`);
- it does not establish which edits happen, any invariant, or anything of the commands around an
  evaluation (`driveStep`, `settle`);
- consumers: the goals packet's fiber positions (G2) and its per-program assertions at every
  command boundary, then the command-level classification (the research note
  `docs/research/2026-10-11-machine-from-the-base/README.md`, §5.2).
-/

set_option autoImplicit false

namespace Effect4.Program.Moves

open Effect4 Effect4.Machine Effect4.Program

/-- The machine's events at the native alphabets. -/
abbrev NRunEvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx NCode NEvent

/-- The edits one evaluation makes to a fiber other than the one it runs. An interrupt carries the
interpreter it was recorded with. -/
inductive OtherEdit : NFiber → NFiber → Prop
  /-- An observer is appended: a join or a countdown waits on this fiber, or a scope link. -/
  | observe (g : NFiber) (o : Observer) : OtherEdit g { g with observers := g.observers ++ [o] }
  /-- The observers are filtered: a park's cleanup drops a token. -/
  | filterObservers (g : NFiber) (keep : Observer → Bool) :
      OtherEdit g { g with observers := g.observers.filter keep }
  /-- An interrupt is recorded on this fiber. -/
  | interrupted (interp : NInterp) (g : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
      OtherEdit g (interruptRecord interp who extra g).1

/-- Words of edits of another fiber. -/
inductive OtherEdits : NFiber → NFiber → Prop
  /-- No edit. -/
  | refl (g : NFiber) : OtherEdits g g
  /-- One more edit at the end. -/
  | tail {g h k : NFiber} : OtherEdits g h → OtherEdit h k → OtherEdits g k

/-- Words of edits compose. -/
theorem OtherEdits.trans {g h k : NFiber} (a : OtherEdits g h) (b : OtherEdits h k) :
    OtherEdits g k := by
  induction b with
  | refl => exact a
  | tail _ e ih => exact .tail ih e

/-- An edit keeps the id. -/
theorem OtherEdit.id {g h : NFiber} (e : OtherEdit g h) : h.id = g.id := by
  cases e with
  | observe => rfl
  | filterObservers => rfl
  | interrupted interp g who extra =>
    unfold interruptRecord
    dsimp only
    repeat' split
    all_goals rfl

/-- A word of edits keeps the id. -/
theorem OtherEdits.id {g h : NFiber} (w : OtherEdits g h) : h.id = g.id := by
  induction w with
  | refl => rfl
  | tail _ e ih => exact e.id.trans ih

/-- An edit keeps the exit: an exited fiber records no interrupt. -/
theorem OtherEdit.exit {g h : NFiber} (e : OtherEdit g h) : h.exit = g.exit := by
  cases e with
  | observe => rfl
  | filterObservers => rfl
  | interrupted interp g who extra =>
    unfold interruptRecord
    dsimp only
    repeat' split
    all_goals rfl

/-- A word of edits keeps the exit. -/
theorem OtherEdits.exit {g h : NFiber} (w : OtherEdits g h) : h.exit = g.exit := by
  induction w with
  | refl => rfl
  | tail _ e ih => exact e.exit.trans ih

/-- The initial fields of an allocated fiber, retained as proof data.
This witness reuses the machine's code and context; it adds no stored program syntax. -/
structure Birth where
  program : NCode
  flag : Bool
  budget : Nat × Bool
  context : Ctx

/-- A birth names the machine's existing initialization. -/
def Birth.fiber (birth : Birth) (id : FiberId) : NFiber :=
  RunFiber.make id birth.program birth.flag birth.budget birth.context

/-- A total witness table has an irrelevant entry outside the allocated interval. -/
def Birth.empty : Birth := ⟨.success .unit, true, (0, false), emptyCtx⟩

/-- The shared table identifies every fresh fiber's initialization by its allocated id.
The interval and the table survive composition; they serve the whole-machine mask instance. -/
structure Interferes (m m' : NativeMachine) : Prop where
  nextId : m.nextId ≤ m'.nextId
  births : ∃ born : Nat → Birth, ∀ g' ∈ m'.fibers,
    (∃ g ∈ m.fibers, OtherEdits g g') ∨
    (m.nextId ≤ g'.id.value ∧ g'.id.value < m'.nextId ∧
      OtherEdits ((born g'.id.value).fiber g'.id) g')

/-- The existing per-fiber initialization interface forgets the shared table and upper bound. -/
theorem Interferes.fibers {m m' : NativeMachine} (h : Interferes m m') (g' : NFiber)
    (member : g' ∈ m'.fibers) : (∃ g ∈ m.fibers, OtherEdits g g') ∨
    (m.nextId ≤ g'.id.value ∧ ∃ program flag budget context,
      OtherEdits (RunFiber.make g'.id program flag budget context) g') := by
  obtain ⟨born, rows⟩ := h.births
  rcases rows g' member with old | ⟨lower, _, word⟩
  · exact .inl old
  · exact .inr ⟨lower, (born g'.id.value).program, (born g'.id.value).flag,
      (born g'.id.value).budget, (born g'.id.value).context, word⟩

/-- No interference allocates no new fiber. -/
theorem Interferes.refl (m : NativeMachine) : Interferes m m :=
  ⟨Nat.le_refl _, fun _ => Birth.empty, fun g' mem => .inl ⟨g', mem, .refl _⟩⟩

/-- Composition concatenates the allocation intervals and retains each interval's birth table. -/
theorem Interferes.trans {m m' m'' : NativeMachine} (a : Interferes m m') (b : Interferes m' m'') :
    Interferes m m'' := by
  obtain ⟨first, rows⟩ := a.births
  obtain ⟨second, rows'⟩ := b.births
  refine ⟨Nat.le_trans a.nextId b.nextId, fun n => if n < m'.nextId then first n else second n,
    fun g'' mem => ?_⟩
  rcases rows' g'' mem with ⟨g', mem', w'⟩ | ⟨lower, upper, born⟩
  · rcases rows g' mem' with ⟨g, memOld, w⟩ | ⟨lower, upper, born⟩
    · exact .inl ⟨g, memOld, w.trans w'⟩
    · refine .inr ⟨w'.id ▸ lower, ?_, ?_⟩
      · rw [w'.id]
        exact Nat.lt_of_lt_of_le upper b.nextId
      · dsimp only
        rw [w'.id, if_pos upper]
        exact born.trans w'
  · refine .inr ⟨Nat.le_trans a.nextId lower, upper, ?_⟩
    dsimp only
    rw [if_neg (Nat.not_lt.mpr lower)]
    exact born

/-- A machine edit that keeps the fiber list and does not lower the counter. -/
theorem Interferes.ofFibers {m m' : NativeMachine} (fibers : m'.fibers = m.fibers)
    (nextId : m.nextId ≤ m'.nextId) : Interferes m m' :=
  ⟨nextId, fun _ => Birth.empty, fun g' mem => .inl ⟨g', fibers ▸ mem, .refl _⟩⟩

/-- Replacing a fiber of the machine by an edit of it allocates no birth. -/
theorem Interferes.update {m : NativeMachine} {t t' : NFiber} (mem : t ∈ m.fibers)
    (edit : OtherEdits t t') : Interferes m (m.update t') := by
  refine ⟨Nat.le_refl _, fun _ => Birth.empty, fun g' memNew => ?_⟩
  unfold RunMachine.update at memNew
  obtain ⟨g, memOld, eq⟩ := List.mem_map.mp memNew
  split at eq
  · exact .inl ⟨t, mem, eq ▸ edit⟩
  · exact .inl ⟨g, memOld, eq ▸ .refl _⟩

/-- Appending to the trace after an interference. -/
theorem Interferes.thenEmit {m m' : NativeMachine} (h : Interferes m m') (events : List NRunEvent) :
    Interferes m (m'.emit events) :=
  ⟨h.nextId, h.births⟩

/-- A machine edit that keeps the fiber list and does not lower the counter. -/
theorem Interferes.thenSame {m m' m'' : NativeMachine} (h : Interferes m m')
    (fibers : m''.fibers = m'.fibers) (nextId : m'.nextId ≤ m''.nextId) : Interferes m m'' := by
  obtain ⟨born, rows⟩ := h.births
  refine ⟨Nat.le_trans h.nextId nextId, born, fun g mem => ?_⟩
  rcases rows g (fibers ▸ mem) with old | ⟨lower, upper, word⟩
  · exact .inl old
  · exact .inr ⟨lower, Nat.lt_of_lt_of_le upper nextId, word⟩

/-- Appending to the trace keeps the fibers. -/
theorem Interferes.emit (m : NativeMachine) (events : List NRunEvent) : Interferes m (m.emit events) :=
  .ofFibers rfl (Nat.le_refl _)

/-- A spawn records the actual program, start flag, budget and parent's context at the new id. -/
theorem Interferes.spawn (interp : NInterp) (m : NativeMachine) (parent : NFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) :
    Interferes m (spawn interp m parent program options site).1 := by
  let flag := match options.maskMode with
    | .interruptible => true
    | .uninterruptible => false
    | .inherit => parent.frame.interruptible
  refine ⟨Nat.le_succ _, fun _ => ⟨program, flag, interp.budgetOf parent.context, parent.context⟩,
    fun g' mem => ?_⟩
  unfold Machine.spawn at mem
  rcases List.mem_append.mp mem with old | child
  · exact .inl ⟨g', old, .refl _⟩
  · rw [List.mem_singleton.mp child]
    exact .inr ⟨Nat.le_refl _, Nat.lt_succ_self _, .refl _⟩

/-- A park's cleanup filters every fiber's observers. -/
theorem Interferes.filterObservers (m : NativeMachine) (keep : Observer → Bool) :
    Interferes m { m with fibers := m.fibers.map fun g => { g with observers := g.observers.filter keep } } := by
  refine ⟨Nat.le_refl _, fun _ => Birth.empty, fun g' mem => ?_⟩
  obtain ⟨g, memOld, eq⟩ := List.mem_map.mp mem
  exact .inl ⟨g, memOld, eq ▸ .tail (.refl g) (.filterObservers g keep)⟩

/-! ## Applied from the outside in -/

/-- A spawn after an interference. -/
theorem Interferes.thenSpawn {m m' : NativeMachine} (h : Interferes m m') (interp : NInterp)
    (parent : NFiber) (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    Interferes m (Machine.spawn interp m' parent program options site).1 :=
  h.trans (.spawn interp m' parent program options site)

/-- Replacing a fiber by an edit of it, after an interference. -/
theorem Interferes.thenUpdate {m m' : NativeMachine} {t t' : NFiber} (h : Interferes m m')
    (mem : t ∈ m'.fibers) (edit : OtherEdits t t') : Interferes m (m'.update t') :=
  h.trans (.update mem edit)

/-! ## The classification -/

/-- Every old first lookup survives under the existing word of other-fiber edits.
Consumer: exact stored-stack transport, including machines with duplicate ids. -/
def LookupEdits (before after : NativeMachine) : Prop :=
  ∀ id fiber, before.fiber? id = some fiber →
    ∃ next, after.fiber? id = some next ∧ OtherEdits fiber next

theorem LookupEdits.refl (m : NativeMachine) : LookupEdits m m :=
  fun _ fiber found => ⟨fiber, found, .refl _⟩

theorem LookupEdits.trans {m n o : NativeMachine} (first : LookupEdits m n)
    (second : LookupEdits n o) : LookupEdits m o := by
  intro id fiber found
  obtain ⟨middle, seen, edits⟩ := first id fiber found
  obtain ⟨last, final, more⟩ := second id middle seen
  exact ⟨last, final, edits.trans more⟩

theorem LookupEdits.ofFibers {m n : NativeMachine} (same : n.fibers = m.fibers) :
    LookupEdits m n := by
  intro id fiber found
  exact ⟨fiber, by simpa only [RunMachine.fiber?, same] using found, .refl _⟩

/-- A first-lookup update transports exactly the selected record's word of edits. -/
theorem LookupEdits.update {m : NativeMachine} {target : FiberId} {fiber next : NFiber}
    (found : m.fiber? target = some fiber) (edits : OtherEdits fiber next) :
    LookupEdits m (m.update next) := by
  have key : fiber.id = target := of_decide_eq_true
    (List.find?_some (p := fun g : NFiber => decide (g.id = target)) found)
  intro id old seen
  by_cases same : id = next.id
  · have before : old = fiber := Option.some.inj (by
      rw [same, edits.id, key] at seen
      exact seen.symm.trans found)
    subst old
    refine ⟨next, ?_, edits⟩
    rw [same]
    exact RunMachine.fiber?_update_self next m
      ⟨fiber, List.mem_of_find?_eq_some found, edits.id.symm⟩
  · exact ⟨old, (RunMachine.fiber?_update_other next m id same).trans seen, .refl _⟩

theorem LookupEdits.append (m : NativeMachine) (rows : List NFiber) :
    LookupEdits m {m with fibers := m.fibers ++ rows} := by
  intro id fiber found
  refine ⟨fiber, ?_, .refl _⟩
  unfold RunMachine.fiber? at found
  simp only [RunMachine.fiber?, List.find?_append, found, Option.some_or]

theorem LookupEdits.map (m : NativeMachine) (edit : NFiber → NFiber)
    (word : ∀ fiber, OtherEdits fiber (edit fiber)) :
    LookupEdits m {m with fibers := m.fibers.map edit} := by
  intro id fiber found
  refine ⟨edit fiber, ?_, word fiber⟩
  unfold RunMachine.fiber? at found ⊢
  rw [List.find?_map]
  have predicate : ((fun g : NFiber => decide (g.id = id)) ∘ edit) =
      (fun g : NFiber => decide (g.id = id)) := by
    funext g
    simp only [Function.comp_def, (word g).id]
  rw [predicate, found]
  rfl

/-- The one native census retains births and forward first lookups.
Consumer: NativeStacks projects stack equality without a uniqueness premise. -/
structure InterferesWithLookup (before after : NativeMachine) : Prop where
  backward : Interferes before after
  lookup : LookupEdits before after

theorem InterferesWithLookup.refl (m : NativeMachine) : InterferesWithLookup m m :=
  ⟨.refl _, .refl _⟩

theorem InterferesWithLookup.ofFibers {m n : NativeMachine} (same : n.fibers = m.fibers)
    (nextId : m.nextId ≤ n.nextId) : InterferesWithLookup m n :=
  ⟨.ofFibers same nextId, .ofFibers same⟩

theorem InterferesWithLookup.trans {m n o : NativeMachine}
    (first : InterferesWithLookup m n) (second : InterferesWithLookup n o) :
    InterferesWithLookup m o := ⟨first.backward.trans second.backward, first.lookup.trans second.lookup⟩

theorem InterferesWithLookup.update {m : NativeMachine} {target : FiberId} {fiber next : NFiber}
    (found : m.fiber? target = some fiber) (edits : OtherEdits fiber next) :
    InterferesWithLookup m (m.update next) :=
  ⟨.update (List.mem_of_find?_eq_some found) edits, .update found edits⟩

theorem InterferesWithLookup.modify (m : NativeMachine) (target : FiberId) (edit : NFiber → NFiber)
    (word : ∀ fiber, OtherEdits fiber (edit fiber)) :
    InterferesWithLookup m (m.modify target edit) := by
  unfold RunMachine.modify
  split
  · exact .refl _
  · rename_i fiber found
    exact .update found (word fiber)

theorem InterferesWithLookup.emit (m : NativeMachine) (events : List NRunEvent) :
    InterferesWithLookup m (m.emit events) := ⟨.emit _ _, .ofFibers rfl⟩

theorem InterferesWithLookup.thenEmit {m n : NativeMachine} (held : InterferesWithLookup m n)
    (events : List NRunEvent) : InterferesWithLookup m (n.emit events) := held.trans (.emit _ _)

theorem InterferesWithLookup.thenObserve {m n : NativeMachine} (held : InterferesWithLookup m n)
    (target : FiberId) (observer : Observer) :
    InterferesWithLookup m (n.modify target fun fiber => {fiber with observers := fiber.observers ++ [observer]}) :=
  held.trans (.modify n target _ (fun fiber => .tail (.refl _) (.observe fiber observer)))

theorem InterferesWithLookup.spawn (interp : NInterp) (m : NativeMachine) (parent : NFiber)
    (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    InterferesWithLookup m (spawn interp m parent program options site).1 := by
  refine ⟨.spawn _ _ _ _ _ _, ?_⟩
  exact LookupEdits.append m _

theorem InterferesWithLookup.start (m : NativeMachine) (parent : NFiber)
    (child : FiberId) (immediate : Bool) : InterferesWithLookup m (start m parent child immediate).1 := by
  unfold Machine.start
  split
  · exact .refl _
  · exact .ofFibers rfl (Nat.le_refl _)

theorem InterferesWithLookup.forkFinalizers (interp : NInterp) (host : NFiber) :
    ∀ (m : NativeMachine) (programs : List NCode),
      InterferesWithLookup m (forkFinalizers interp m host programs).1
  | m, [] => .refl m
  | m, program :: rest => by
    unfold Machine.forkFinalizers
    exact (InterferesWithLookup.spawn interp m host program _ []).trans
      (InterferesWithLookup.forkFinalizers interp host _ rest)

theorem InterferesWithLookup.countdownPark (interp : NInterp) (m : NativeMachine) (fiber : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    InterferesWithLookup m (countdownPark interp m fiber targets resume failFast).1 := by
  unfold Machine.countdownPark
  dsimp only
  split
  · exact .ofFibers rfl (Nat.le_refl _)
  · apply InterferesWithLookup.thenEmit
    apply InterferesWithLookup.thenObserve
    exact .ofFibers rfl (Nat.le_refl _)

theorem InterferesWithLookup.linkScope (interp : NInterp) (m : NativeMachine) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    InterferesWithLookup m (linkScope interp m mode scope target who extra).1 := by
  unfold Machine.linkScope
  split
  · exact .ofFibers rfl (Nat.le_refl _)
  · split
    · exact .ofFibers rfl (Nat.le_refl _)
    · rename_i fiber found
      apply InterferesWithLookup.thenEmit
      exact .update found (.tail (.refl fiber) (.interrupted interp fiber who extra))
  · split
    · exact .ofFibers rfl (Nat.le_refl _)
    · split
      · exact .refl _
      · split
        · exact .ofFibers rfl (Nat.le_refl _)
        · apply InterferesWithLookup.thenEmit
          apply InterferesWithLookup.thenObserve
          exact .ofFibers rfl (Nat.le_refl _)

theorem InterferesWithLookup.filterObservers (m : NativeMachine) (keep : Observer → Bool) :
    InterferesWithLookup m {m with fibers := m.fibers.map fun fiber =>
      {fiber with observers := fiber.observers.filter keep}} :=
  ⟨.filterObservers m keep, LookupEdits.map m _ (fun fiber => .tail (.refl _) (.filterObservers fiber keep))⟩

theorem InterferesWithLookup.thenSpawn {m n : NativeMachine} (held : InterferesWithLookup m n)
    (interp : NInterp) (parent : NFiber) (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    InterferesWithLookup m (Machine.spawn interp n parent program options site).1 := held.trans (.spawn _ _ _ _ _ _)

theorem InterferesWithLookup.thenStart {m n : NativeMachine} (held : InterferesWithLookup m n)
    (parent : NFiber) (child : FiberId) (immediate : Bool) :
    InterferesWithLookup m (Machine.start n parent child immediate).1 := held.trans (.start _ _ _ _)

theorem InterferesWithLookup.thenUpdate {m n : NativeMachine} {target : FiberId} {fiber next : NFiber}
    (held : InterferesWithLookup m n) (found : n.fiber? target = some fiber)
    (edits : OtherEdits fiber next) : InterferesWithLookup m (n.update next) := held.trans (.update found edits)

/-- Editing a first lookup projects the single stronger modification law. -/
theorem Interferes.modify {m : NativeMachine} (id : FiberId) (k : NFiber → NFiber)
    (edit : ∀ g, OtherEdits g (k g)) : Interferes m (m.modify id k) :=
  (InterferesWithLookup.modify m id k edit).backward

/-- Appending one observer to the fiber an id names, after an interference. -/
theorem Interferes.thenObserve {m m' : NativeMachine} (h : Interferes m m') (id : FiberId)
    (o : Observer) :
    Interferes m (m'.modify id fun g => { g with observers := g.observers ++ [o] }) :=
  h.trans (.modify id _ fun g => .tail (.refl g) (.observe g o))

/-- Appending one observer to the fiber an id names. -/
theorem Interferes.observe (m : NativeMachine) (id : FiberId) (o : Observer) :
    Interferes m (m.modify id fun g => { g with observers := g.observers ++ [o] }) :=
  .modify id _ fun g => .tail (.refl g) (.observe g o)

/-- Starting a spawned child keeps the fibers, by the shared stronger classification. -/
theorem Interferes.start (m : NativeMachine) (parent : NFiber) (child : FiberId) (immediately : Bool) :
    Interferes m (start m parent child immediately).1 :=
  (InterferesWithLookup.start m parent child immediately).backward

/-- The parallel close inherits the shared allocation and forward lookup classification. -/
theorem Interferes.forkFinalizers (interp : NInterp) (host : NFiber) :
    ∀ (m : NativeMachine) (programs : List NCode),
      Interferes m (forkFinalizers interp m host programs).1 :=
  fun m programs => (InterferesWithLookup.forkFinalizers interp host m programs).backward

/-- The countdown park projects the shared observer classification. -/
theorem Interferes.countdownPark (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Interferes m (countdownPark interp m f targets resumeWith failFast).1 :=
  (InterferesWithLookup.countdownPark interp m f targets resumeWith failFast).backward

/-- A scope link projects the actual first-lookup edit classification. -/
theorem Interferes.linkScope (interp : NInterp) (m : NativeMachine) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    Interferes m (linkScope interp m mode scope target interruptor extra).1 :=
  (InterferesWithLookup.linkScope interp m mode scope target interruptor extra).backward

/-- A start after an interference. -/
theorem Interferes.thenStart {m m' : NativeMachine} (h : Interferes m m') (parent : NFiber)
    (child : FiberId) (immediately : Bool) : Interferes m (Machine.start m' parent child immediately).1 :=
  h.trans (.start m' parent child immediately)

/-- The countdown park after an interference. -/
theorem Interferes.thenCountdown {m m' : NativeMachine} (h : Interferes m m') (interp : NInterp)
    (f : NFiber) (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Interferes m (Machine.countdownPark interp m' f targets resumeWith failFast).1 :=
  h.trans (.countdownPark interp m' f targets resumeWith failFast)

/-- The parallel close's forks after an interference. -/
theorem Interferes.thenForkFinalizers {m m' : NativeMachine} (h : Interferes m m')
    (interp : NInterp) (host : NFiber) (programs : List NCode) :
    Interferes m (Machine.forkFinalizers interp m' host programs).1 :=
  h.trans (Interferes.forkFinalizers interp host m' programs)

/-- A scope link after an interference. -/
theorem Interferes.thenLink {m m' : NativeMachine} (h : Interferes m m') (interp : NInterp)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (interruptor : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    Interferes m (Machine.linkScope interp m' mode scope target interruptor extra).1 :=
  h.trans (.linkScope interp m' mode scope target interruptor extra)

/-- The frame machine's step, delegated, appends to the trace alone. -/
theorem stepFrame_interference (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    InterferesWithLookup m (evaluatePrim.stepFrame interp m f yielding).machine := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact .emit _ _

/-- An exit meeting the stack appends to the trace alone. -/
theorem finalizerOr_interference (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    InterferesWithLookup m (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact .emit _ _
      · exact stepFrame_interference _ _ _ _
    · exact stepFrame_interference _ _ _ _

/-- Every `withFiber` action, on the machine. -/
theorem withFiber_interference (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    InterferesWithLookup m (evaluatePrim.withFiber interp m f yielding action).machine := by
  cases action with
  | fork program options site =>
    simp only [evaluatePrim.withFiber]
    apply InterferesWithLookup.thenStart
    apply InterferesWithLookup.thenSpawn
    split
    · exact .refl _
    · exact .ofFibers rfl (Nat.le_refl _)
  | forkIn program options scope site =>
    simp only [evaluatePrim.withFiber]
    apply InterferesWithLookup.thenStart
    exact InterferesWithLookup.spawn _ _ _ _ _ _
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber]
    split
    · apply InterferesWithLookup.thenStart
      exact InterferesWithLookup.spawn _ _ _ _ _ _
    · exact .refl _
  | ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .refl _
  | runIn target scope => exact InterferesWithLookup.linkScope _ _ _ _ _ _ _
  | interrupt target => exact .refl _
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split
    · exact .refl _
    · rename_i t found
      apply InterferesWithLookup.thenEmit
      exact InterferesWithLookup.update found
        (.tail (.refl t) (.interrupted interp t (some who) _))
  | interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .refl _
  | interruptAll targets interruptor => exact .refl _
  | awaitAll targets => exact InterferesWithLookup.countdownPark _ _ _ _ _ _
  | awaitAllFailFast targets => exact InterferesWithLookup.countdownPark _ _ _ _ _ _
  | snapshotChildren => exact .refl _
  | awaitNewChildren snapshot => exact InterferesWithLookup.countdownPark _ _ _ _ _ _
  | raceAll entrants site =>
    simp only [evaluatePrim.withFiber, beginRace]
    exact .ofFibers rfl (Nat.le_refl _)
  | raceAllFirst entrants site =>
    simp only [evaluatePrim.withFiber, beginRace]
    exact .ofFibers rfl (Nat.le_refl _)
  | setInterruptible body flag =>
    cases flag <;> exact .refl _
  | setContext context => exact .emit _ _
  | getContext => exact .refl _
  | getId => exact .refl _
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact .refl _
    · exact .ofFibers rfl (Nat.le_refl _)
  | closePar finalizers => exact InterferesWithLookup.forkFinalizers _ _ _ _
  | refuse cause => exact .refl _
  | dropObservers token => exact InterferesWithLookup.filterObservers _ _
  | cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .refl _
  | getInterruptible => exact .refl _

/-- **One primitive evaluation**'s interference on the machine's fibers. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_interference (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    InterferesWithLookup m (evaluatePrim interp m f yielding).machine := by
  unfold evaluatePrim
  split
  · exact .ofFibers rfl (Nat.le_refl _)
  · dsimp only
    split
    · exact .ofFibers rfl (Nat.le_refl _)
    · exact .ofFibers rfl (Nat.le_refl _)
  · split
    · exact .refl _
    · unfold registerRace
      split
      · exact .refl _
      · exact .ofFibers rfl (Nat.le_refl _)
    · exact InterferesWithLookup.countdownPark _ _ _ _ _ _
    · split
      · exact .refl _
      · split
        · exact .refl _
        · rename_i t found _ _
          apply InterferesWithLookup.thenEmit
          exact InterferesWithLookup.thenUpdate (.ofFibers rfl (Nat.le_refl _))
            found (.tail (.refl t) (.observe t _))
    · split
      · split
        · exact withFiber_interference _ _ _ _ _
        · exact stepFrame_interference _ _ _ _
      · split
        · exact .ofFibers rfl (Nat.le_refl _)
        · exact .refl _
      · exact finalizerOr_interference _ _ _ _ _
      · exact finalizerOr_interference _ _ _ _ _
      · exact stepFrame_interference _ _ _ _

/-- The scoped exit writes the stores and the trace alone. -/
theorem exitScoped_interference (root : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    InterferesWithLookup m (exitScoped root m f yielding exit).machine := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact .ofFibers rfl (Nat.le_refl _)
    · split <;> exact .ofFibers rfl (Nat.le_refl _)
  · exact evaluatePrim_interference _ _ _ _

/-- **One native evaluation**'s interference on the machine's fibers. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_interference (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    InterferesWithLookup m (evaluateNative root m f yielding table).machine := by
  unfold evaluateNative
  split
  · split
    · unfold enterScoped
      exact .ofFibers rfl (Nat.le_refl _)
    · exact evaluatePrim_interference _ _ _ _
  · exact exitScoped_interference _ _ _ _ _
  · exact exitScoped_interference _ _ _ _ _
  · exact evaluatePrim_interference _ _ _ _

/-- **One iteration of the native loop**'s interference on the machine's fibers. The pointer of
the evaluation's half of the proposed claim `command-moves`. -/
@[semantics "reactive-scheduling"]
theorem iteration_interference (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    InterferesWithLookup m (iteration (evaluator := evaluatorFor root table) interp m f yielding).machine := by
  unfold iteration
  dsimp only
  split
  · rename_i it h
    have injected : InterferesWithLookup m it.machine := by
      unfold injectYield at h
      split at h
      · cases h
        exact .emit _ _
      · cases h
    exact injected.trans (evaluateNative_interference _ _ _ _ _)
  · exact evaluateNative_interference _ _ _ _ _

/-! Existing interfaces project the single strengthened evaluator census. -/

theorem stepFrame_interferes (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Interferes m (evaluatePrim.stepFrame interp m f yielding).machine :=
  (stepFrame_interference interp m f yielding).backward

theorem finalizerOr_interferes (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Interferes m (evaluatePrim.finalizerOr interp m f yielding exit).machine :=
  (finalizerOr_interference interp m f yielding exit).backward

theorem withFiber_interferes (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) : Interferes m (evaluatePrim.withFiber interp m f yielding action).machine :=
  (withFiber_interference interp m f yielding action).backward

@[semantics "reactive-scheduling"]
theorem evaluatePrim_interferes (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) : Interferes m (evaluatePrim interp m f yielding).machine :=
  (evaluatePrim_interference interp m f yielding).backward

theorem exitScoped_interferes (root : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) : Interferes m (exitScoped root m f yielding exit).machine :=
  (exitScoped_interference root m f yielding exit).backward

@[semantics "reactive-scheduling"]
theorem evaluateNative_interferes (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) : Interferes m (evaluateNative root m f yielding table).machine :=
  (evaluateNative_interference root table m f yielding).backward

@[semantics "reactive-scheduling"]
theorem iteration_interferes (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Interferes m (iteration (evaluator := evaluatorFor root table) interp m f yielding).machine :=
  (iteration_interference root table interp m f yielding).backward

end Effect4.Program.Moves
