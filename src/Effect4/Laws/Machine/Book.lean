import Effect4.Laws.Machine.Behaviour

/-!
# The book: two instances of the shared loop, related field by field (P3, step 1)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). Scouted as
`docs/research/probes/wave2-book/p01_bookmeans.lean` and `p03_two_instance.lean` at
`a1fb467` (`docs/research/2026-09-06-wave2-book.md`); ported here against the current
command alphabet (D6a's `enrollRace`/`registrationDone`, D6b's ordered interruption and
exit observers, §20's `closeParAwait`).

Nothing here is about the frame machine or the term machine. Two *arbitrary* instances of
the shared machine (`κ φ η` free on each side) are related by `BookMeans C S`: every
code-free field by equality, the code-carrying carriers pairwise through the code relation
`C`, the saved state through `S` while the fiber is live, and the trace not at all (D3).
Under one hypothesis about a single `driveStep` (`StepAgrees`), the whole fuel-bounded loop,
every decision and every tape preserve the book (`book_replayEval`); the finite battery's
control lists, exits and observation are consequences (`bookMeans_obs`).

The loop also carries a one-sided invariant of the left instance, `MachineOk StOk`: a
predicate on the shared store the concrete instance chooses (the frame instance says which
programs the deferred cells may hold, so that the term instance can read them back), and
the absence of `Resume.continueWith` parks, which no arm of the machine produces and the
term instance has no reading of. The step obligation preserves it beside the book.

Core v4.33.1 has no `List.Forall₂`; `ListRel` is the pairwise relation at one universe.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Effect4.Machine

open Effect4

universe u v w w'

/-! ## Pairwise relations -/

/-- What `List.Forall₂` would be. -/
inductive ListRel {α β : Type w} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b l l'} : R a b → ListRel R l l' → ListRel R (a :: l) (b :: l')

theorem cons_eq_of {α : Type w} {a b : α} {l l' : List α} (h : a = b) (h' : l = l') :
    a :: l = b :: l' := by rw [h, h']

theorem ListRel.append {α β : Type w} {R : α → β → Prop} {l₁ l₂ r₁ r₂}
    (h : ListRel R l₁ l₂) (h' : ListRel R r₁ r₂) : ListRel R (l₁ ++ r₁) (l₂ ++ r₂) := by
  induction h with
  | nil => exact h'
  | cons hd _ ih => exact ListRel.cons hd ih

theorem ListRel.isEmpty {α β : Type w} {R : α → β → Prop} {l₁ l₂}
    (h : ListRel R l₁ l₂) : l₁.isEmpty = l₂.isEmpty := by
  cases h <;> rfl

theorem ListRel.length {α β : Type w} {R : α → β → Prop} {l₁ l₂}
    (h : ListRel R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ListRel.map {α β : Type w} {R : α → β → Prop} {l₁ l₂}
    (h : ListRel R l₁ l₂) {γ : Type w'} {g₁ : α → γ} {g₂ : β → γ}
    (hg : ∀ a b, R a b → g₁ a = g₂ b) : l₁.map g₁ = l₂.map g₂ := by
  induction h with
  | nil => rfl
  | cons hd _ ih => exact cons_eq_of (hg _ _ hd) ih

theorem ListRel.of_map {α β : Type w} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    {γ : Type w'} {g₁ : α → γ} {g₂ : β → γ} (h : ListRel R l₁ l₂)
    {P : γ → γ → Prop} (hg : ∀ a b, R a b → P (g₁ a) (g₂ b)) :
    ListRel P (l₁.map g₁) (l₂.map g₂) := by
  induction h with
  | nil => exact ListRel.nil
  | cons hd _ ih => exact ListRel.cons (hg _ _ hd) ih

theorem ListRel.refl {α : Type w} {R : α → α → Prop} (hr : ∀ a, R a a) :
    ∀ l : List α, ListRel R l l
  | [] => ListRel.nil
  | a :: l => ListRel.cons (hr a) (ListRel.refl hr l)

theorem ListRel.of_eq {α : Type w} {R : α → α → Prop} (hr : ∀ a, R a a) {l l' : List α}
    (h : l = l') : ListRel R l l' := by
  subst h; exact ListRel.refl hr l

/-- The fold law every `List.foldl` in the loop needs (`fireStep`, `interruptEach`,
`fireObserver`): one lemma, used everywhere. -/
theorem foldl_rel {α₁ α₂ : Type w} {γ₁ γ₂ : Type w'}
    {R : α₁ → α₂ → Prop} {P : γ₁ → γ₂ → Prop}
    {f₁ : γ₁ → α₁ → γ₁} {f₂ : γ₂ → α₂ → γ₂}
    (hf : ∀ a₁ a₂ x₁ x₂, P a₁ a₂ → R x₁ x₂ → P (f₁ a₁ x₁) (f₂ a₂ x₂))
    {l₁ l₂} (h : ListRel R l₁ l₂) : ∀ {a₁ a₂}, P a₁ a₂ → P (l₁.foldl f₁ a₁) (l₂.foldl f₂ a₂) := by
  induction h with
  | nil => intro a₁ a₂ ha; exact ha
  | cons hd _ ih => intro a₁ a₂ ha; exact ih (hf _ _ _ _ ha hd)

/-- Two `Option`s related, or both absent. -/
def OptRel {α β : Type w} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem OptRel.isSome {α β : Type w} {R : α → β → Prop} {o₁ : Option α} {o₂ : Option β}
    (h : OptRel R o₁ o₂) : o₁.isSome = o₂.isSome := by
  cases o₁ <;> cases o₂ <;> first | rfl | exact absurd h not_false

/-- `Owed`: the waiter, token and mode agree; the code is related. One universe, so a use at
`κ₁ κ₂ : Type (max u v)` unifies. -/
def OwedMeans {κ₁ κ₂ : Type w} (C : κ₁ → κ₂ → Prop) (d₁ : Owed κ₁) (d₂ : Owed κ₂) : Prop :=
  d₁.waiter = d₂.waiter ∧ d₁.token = d₂.token ∧ C d₁.code d₂.code ∧ d₁.mode = d₂.mode

section Generic

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ₁ φ₁ η₁ κ₂ φ₂ η₂ : Type (max u v)}
variable [core₁ : FiberCore ν β ε δ ι α κ₁ φ₁] [core₂ : FiberCore ν β ε δ ι α κ₂ φ₂]

/-! ## The code-carrying carriers: a relation each, never an erasure map -/

/-- `Task`: `start` carries a fiber id only; `resume` carries code. -/
def TaskMeans (C : κ₁ → κ₂ → Prop) :
    Task ν σ β ε δ ι α κ₁ → Task ν σ β ε δ ι α κ₂ → Prop
  | .start c₁, .start c₂ => c₁ = c₂
  | .resume t₁ k₁ a₁, .resume t₂ k₂ a₂ => t₁ = t₂ ∧ k₁ = k₂ ∧ C a₁ a₂
  | .wake l₁ p₁, .wake l₂ p₂ => l₁ = l₂ ∧ p₁ = p₂
  | _, _ => False

/-- `Bucket`: a priority and its FIFO of tasks. -/
def BucketMeans (C : κ₁ → κ₂ → Prop)
    (b₁ : Bucket ν σ β ε δ ι α κ₁) (b₂ : Bucket ν σ β ε δ ι α κ₂) : Prop :=
  b₁.priority = b₂.priority ∧ ListRel (TaskMeans C) b₁.tasks b₂.tasks

/-- `Dispatcher`: buckets in priority order plus the armed latch. -/
def DispatcherMeans (C : κ₁ → κ₂ → Prop)
    (d₁ : Dispatcher ν σ β ε δ ι α κ₁) (d₂ : Dispatcher ν σ β ε δ ι α κ₂) : Prop :=
  ListRel (BucketMeans C) d₁.buckets d₂.buckets ∧ d₁.armed = d₂.armed

/-- `Race`: six code-free fields and the unforked entrant programs. -/
def RaceMeans (C : κ₁ → κ₂ → Prop)
    (r₁ : Race ν σ β ε δ ι α κ₁) (r₂ : Race ν σ β ε δ ι α κ₂) : Prop :=
  r₁.id = r₂.id ∧ r₁.host = r₂.host ∧ r₁.token = r₂.token ∧
    r₁.state = r₂.state ∧ r₁.settled = r₂.settled ∧ r₁.registering = r₂.registering ∧
    ListRel C r₁.programs r₂.programs

/-! ## The control projection -/

/-- The observable control data outside the exit/store observation, at the generic
alphabet: the finite battery's `FiberControl` lifted to any core. -/
structure FiberControl (ε δ ι α χ : Type u) : Type u where
  id : FiberId
  parked : Parked
  interruptible : Option Bool
  interruptedCause : Option (Cause ε δ ι α)
  deferredInterrupt : Bool
  context : χ

/-- One function of the `FiberCore` instance. The mask is read only while the fiber is
live: the finite battery compared it that way when the frame's `finishFrame` still
discarded the last pop's saved state (`E4-RTERM-CE-005`); the repaired frame keeps that
state, and `FiberMeans` below relates the saved states of exited fibers as well. -/
def controlOf {κ φ : Type (max u v)} [c : FiberCore ν β ε δ ι α κ φ]
    (f : RunFiber ν σ β ε δ ι α χ κ φ) : FiberControl ε δ ι α χ :=
  ⟨f.id, f.parked,
    if f.exit.isSome then none else some (c.interruptible f.frame),
    c.interruptedCause f.frame, c.deferredInterrupt f.frame, f.context⟩

/-! ## The fifteen fields of `RunFiber` and the ten of `RunMachine` -/

/-- Code-free by equality: `id`, `running`, `parked`, `pending`, `finalizing`, `exit`,
`currentOpCount`, `maxOpsBeforeYield`, `preventYield`, `yieldOverride`, `observers`,
`children`, `context` (thirteen; `Pending` carries a name, never code). Code-carrying:
`dispatcher`, through `Task.resume`. Related by `S`: `frame`, live or exited (the loop may
re-enter an exited fiber's saved state through a late `loop`/`deliver` command, and the
exit path only clears it). -/
def FiberMeans (C : κ₁ → κ₂ → Prop) (S : φ₁ → φ₂ → Prop)
    (f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁) (f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂) : Prop :=
  controlOf f₁ = controlOf f₂ ∧
    f₁.running = f₂.running ∧ f₁.pending = f₂.pending ∧ f₁.finalizing = f₂.finalizing ∧
    f₁.exit = f₂.exit ∧ f₁.currentOpCount = f₂.currentOpCount ∧
    f₁.maxOpsBeforeYield = f₂.maxOpsBeforeYield ∧ f₁.preventYield = f₂.preventYield ∧
    f₁.yieldOverride = f₂.yieldOverride ∧ f₁.observers = f₂.observers ∧
    f₁.children = f₂.children ∧ DispatcherMeans C f₁.dispatcher f₂.dispatcher ∧
    S f₁.frame f₂.frame

/-- Code-free by equality: `nextId`, `nextToken`, `nextRace`, `middlewareInstalled`,
`armed`, `state`, `stuck` (seven). Code-carrying: `fibers` and `races`, pairwise. Excluded:
`trace` (D3); the two instances need not share the event type. -/
def BookMeans (C : κ₁ → κ₂ → Prop) (S : φ₁ → φ₂ → Prop)
    (m₁ : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
    (m₂ : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂) : Prop :=
  ListRel (FiberMeans C S) m₁.fibers m₂.fibers ∧
    ListRel (RaceMeans C) m₁.races m₂.races ∧
    m₁.nextId = m₂.nextId ∧ m₁.nextToken = m₂.nextToken ∧ m₁.nextRace = m₂.nextRace ∧
    m₁.middlewareInstalled = m₂.middlewareInstalled ∧ m₁.armed = m₂.armed ∧
    m₁.state = m₂.state ∧ m₁.stuck = m₂.stuck

/-! ## The commands: the same shape, code related -/

/-- Every command but `resume` is code-free; `resume` carries the answer. -/
def CmdMeans (C : κ₁ → κ₂ → Prop) :
    Cmd ν σ β ε δ ι α κ₁ → Cmd ν σ β ε δ ι α κ₂ → Prop
  | .evaluate a, .evaluate b => a = b
  | .loop a y, .loop b y' => a = b ∧ y = y'
  | .deliver a y, .deliver b y' => a = b ∧ y = y'
  | .finish a e, .finish b e' => a = b ∧ e = e'
  | .resume a t c, .resume b t' c' => a = b ∧ t = t' ∧ C c c'
  | .launch a, .launch b => a = b
  | .enrollRace a c, .enrollRace b c' => a = b ∧ c = c'
  | .registrationDone a y, .registrationDone b y' => a = b ∧ y = y'
  | .interruptTarget t w x, .interruptTarget t' w' x' => t = t' ∧ w = w' ∧ x = x'
  | .afterInterrupt h y k, .afterInterrupt h' y' k' => h = h' ∧ y = y' ∧ k = k'
  | .raceCancel r h y rem vis, .raceCancel r' h' y' rem' vis' =>
      r = r' ∧ h = h' ∧ y = y' ∧ rem = rem' ∧ vis = vis'
  | .trackChild p c, .trackChild p' c' => p = p' ∧ c = c'
  | .observe f e o, .observe f' e' o' => f = f' ∧ e = e' ∧ o = o'
  | .exitDone f, .exitDone f' => f = f'
  | .closeParAwait h y fs, .closeParAwait h' y' fs' => h = h' ∧ y = y' ∧ fs = fs'
  | .link md s t i x, .link md' s' t' i' x' =>
      md = md' ∧ s = s' ∧ t = t' ∧ i = i' ∧ x = x'
  | .drainDue, .drainDue => True
  | .wake l p, .wake l' p' => l = l' ∧ p = p'
  | _, _ => False

/-! ## The one-sided invariant of the left instance -/

/-- A park never resumes through a named continuation: no arm of the machine parks with
`Resume.continueWith`, and the term instance has no reading of an arbitrary name there. -/
def PendingOk {κ φ : Type (max u v)} (f : RunFiber ν σ β ε δ ι α χ κ φ) : Prop :=
  ∀ p ∈ f.pending, ∀ name, p.resumeWith ≠ Resume.continueWith name

/-- What the loop carries on the left instance beside the book: the store predicate the
concrete instance chooses, and `PendingOk` on every fiber. -/
def MachineOk {κ φ η : Type (max u v)} (StOk : St → Prop)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop :=
  StOk m.state ∧ ∀ f ∈ m.fibers, PendingOk f

section Invariant

variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable {StOk : St → Prop} {m : RunMachine ν σ β ε δ ι α χ St κ φ η}

theorem MachineOk.state (h : MachineOk StOk m) : StOk m.state := h.1

theorem MachineOk.fibers (h : MachineOk StOk m) : ∀ f ∈ m.fibers, PendingOk f := h.2

theorem machineOk_emit (h : MachineOk StOk m) (e : List (RunEvent ν σ β ε δ ι α χ κ η)) :
    MachineOk StOk (m.emit e) := h

theorem machineOk_halt (h : MachineOk StOk m) (why : Stuck) : MachineOk StOk (m.halt why) := h

theorem machineOk_disarm (h : MachineOk StOk m) (owner : FiberId) :
    MachineOk StOk (m.disarm owner) := h

theorem machineOk_arm (h : MachineOk StOk m) (owner : FiberId) : MachineOk StOk (m.arm owner) := h

theorem machineOk_middleware (h : MachineOk StOk m) :
    MachineOk StOk { m with middlewareInstalled := true } := h

theorem machineOk_updateRace (h : MachineOk StOk m) (r : Race ν σ β ε δ ι α κ) :
    MachineOk StOk (m.updateRace r) := h

theorem machineOk_stateOf (h : MachineOk StOk m) {s : St} (hs : StOk s) :
    MachineOk StOk { m with state := s } := ⟨hs, h.2⟩

theorem pendingOk_dispatcher {f : RunFiber ν σ β ε δ ι α χ κ φ} (hf : PendingOk f)
    (d : Dispatcher ν σ β ε δ ι α κ) : PendingOk { f with dispatcher := d } := hf

theorem pendingOk_yield {f : RunFiber ν σ β ε δ ι α χ κ φ} (hf : PendingOk f) (v : Option Bool) :
    PendingOk { f with yieldOverride := v } := hf

theorem pendingOk_of_fiber? (h : MachineOk StOk m) {id : FiberId} {f : RunFiber ν σ β ε δ ι α χ κ φ}
    (hf : m.fiber? id = some f) : PendingOk f :=
  h.2 f (List.mem_of_find?_eq_some hf)

theorem machineOk_update (h : MachineOk StOk m) {f : RunFiber ν σ β ε δ ι α χ κ φ}
    (hf : PendingOk f) : MachineOk StOk (m.update f) := by
  refine ⟨h.1, fun g hg => ?_⟩
  unfold RunMachine.update at hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  split
  · exact hf
  · exact h.2 g' hg'

theorem machineOk_modify (h : MachineOk StOk m) (id : FiberId)
    {k : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ}
    (hk : ∀ f, PendingOk f → PendingOk (k f)) : MachineOk StOk (m.modify id k) := by
  unfold RunMachine.modify
  cases hf : m.fiber? id with
  | none => exact h
  | some f => exact machineOk_update h (hk f (pendingOk_of_fiber? h hf))

/-- Recording an interrupt keeps or clears the parks. -/
theorem interruptRecord_pendingOk (i : RunInterp ν σ β ε δ ι α χ St κ) (who : Option FiberId)
    (extra : ReasonAnnotations α) {f : RunFiber ν σ β ε δ ι α χ κ φ} (hf : PendingOk f) :
    PendingOk (interruptRecord i who extra f).1 := by
  unfold interruptRecord
  dsimp only
  repeat' split
  all_goals first
    | exact hf
    | exact fun p hp => by simp at hp

end Invariant

section Book

variable {C : κ₁ → κ₂ → Prop} {S : φ₁ → φ₂ → Prop}
variable {m₁ : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁}
variable {m₂ : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂}

theorem BookMeans.fibers (h : BookMeans C S m₁ m₂) :
    ListRel (FiberMeans C S) m₁.fibers m₂.fibers := h.1
theorem BookMeans.races (h : BookMeans C S m₁ m₂) :
    ListRel (RaceMeans C) m₁.races m₂.races := h.2.1
theorem BookMeans.nextId (h : BookMeans C S m₁ m₂) : m₁.nextId = m₂.nextId := h.2.2.1
theorem BookMeans.nextToken (h : BookMeans C S m₁ m₂) : m₁.nextToken = m₂.nextToken :=
  h.2.2.2.1
theorem BookMeans.nextRace (h : BookMeans C S m₁ m₂) : m₁.nextRace = m₂.nextRace :=
  h.2.2.2.2.1
theorem BookMeans.middleware (h : BookMeans C S m₁ m₂) :
    m₁.middlewareInstalled = m₂.middlewareInstalled := h.2.2.2.2.2.1
theorem BookMeans.armed (h : BookMeans C S m₁ m₂) : m₁.armed = m₂.armed :=
  h.2.2.2.2.2.2.1
theorem BookMeans.state (h : BookMeans C S m₁ m₂) : m₁.state = m₂.state :=
  h.2.2.2.2.2.2.2.1
theorem BookMeans.stuck (h : BookMeans C S m₁ m₂) : m₁.stuck = m₂.stuck :=
  h.2.2.2.2.2.2.2.2

/-- The trace is not in the book, so `emit` is free on either side, with unrelated event
lists (decision D3). -/
theorem book_emit (h : BookMeans C S m₁ m₂) (e₁ : List (RunEvent ν σ β ε δ ι α χ κ₁ η₁))
    (e₂ : List (RunEvent ν σ β ε δ ι α χ κ₂ η₂)) :
    BookMeans C S (m₁.emit e₁) (m₂.emit e₂) := h

theorem book_halt (h : BookMeans C S m₁ m₂) (why : Stuck) :
    BookMeans C S (m₁.halt why) (m₂.halt why) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, rfl⟩

theorem book_disarm (h : BookMeans C S m₁ m₂) (owner : FiberId) :
    BookMeans C S (m₁.disarm owner) (m₂.disarm owner) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    congrArg (fun l => List.filter (fun x => x ≠ owner) l) h.armed,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem book_arm (h : BookMeans C S m₁ m₂) (owner : FiberId) :
    BookMeans C S (m₁.arm owner) (m₂.arm owner) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    by unfold RunMachine.arm; rw [h.armed],
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem book_middleware (h : BookMeans C S m₁ m₂) :
    BookMeans C S { m₁ with middlewareInstalled := true } { m₂ with middlewareInstalled := true } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, rfl, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem book_stateOf (h : BookMeans C S m₁ m₂) (s : St) :
    BookMeans C S { m₁ with state := s } { m₂ with state := s } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, rfl,
    h.2.2.2.2.2.2.2.2⟩

theorem fiberMeans_id {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) : f₁.id = f₂.id :=
  congrArg FiberControl.id h.1

theorem fiberMeans_exit {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) : f₁.exit = f₂.exit :=
  h.2.2.2.2.1

theorem fiberMeans_parked {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) : f₁.parked = f₂.parked :=
  congrArg FiberControl.parked h.1

theorem fiberMeans_context {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) : f₁.context = f₂.context :=
  congrArg FiberControl.context h.1

theorem fiberMeans_interruptedCause {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) :
    core₁.interruptedCause f₁.frame = core₂.interruptedCause f₂.frame :=
  congrArg FiberControl.interruptedCause h.1

theorem fiberMeans_deferred {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) :
    core₁.deferredInterrupt f₁.frame = core₂.deferredInterrupt f₂.frame :=
  congrArg FiberControl.deferredInterrupt h.1

/-- The mask of a live fiber agrees. -/
theorem fiberMeans_interruptible {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (h : FiberMeans C S f₁ f₂) (hlive : f₁.exit = none) :
    core₁.interruptible f₁.frame = core₂.interruptible f₂.frame := by
  have hc := congrArg FiberControl.interruptible h.1
  have hlive' : f₂.exit = none := (fiberMeans_exit h).symm.trans hlive
  simp only [controlOf, hlive, hlive', Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq] at hc
  exact hc

/-- `update`: the map's `if g.id = f.id` never reduces on a variable, so the lemma is by
induction on the pairwise relation. -/
theorem listRel_update {l₁ : List (RunFiber ν σ β ε δ ι α χ κ₁ φ₁)}
    {l₂ : List (RunFiber ν σ β ε δ ι α χ κ₂ φ₂)} (h : ListRel (FiberMeans C S) l₁ l₂)
    {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁} {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂}
    (hf : FiberMeans C S f₁ f₂) :
    ListRel (FiberMeans C S) (l₁.map fun g => if g.id = f₁.id then f₁ else g)
      (l₂.map fun g => if g.id = f₂.id then f₂ else g) := by
  induction h with
  | nil => exact ListRel.nil
  | @cons a b l l' hab _ ih =>
    refine ListRel.cons ?_ ih
    show FiberMeans C S (if a.id = f₁.id then f₁ else a) (if b.id = f₂.id then f₂ else b)
    by_cases hx : a.id = f₁.id
    · have hy : b.id = f₂.id := by rw [← fiberMeans_id hab, ← fiberMeans_id hf]; exact hx
      rw [if_pos hx, if_pos hy]; exact hf
    · have hy : ¬ (b.id = f₂.id) := by rw [← fiberMeans_id hab, ← fiberMeans_id hf]; exact hx
      rw [if_neg hx, if_neg hy]; exact hab

theorem book_update (h : BookMeans C S m₁ m₂) {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (hf : FiberMeans C S f₁ f₂) :
    BookMeans C S (m₁.update f₁) (m₂.update f₂) :=
  ⟨listRel_update h.1 hf, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- `fiber?` is `find?` on the id, and the ids agree pairwise. -/
theorem listRel_find {l₁ : List (RunFiber ν σ β ε δ ι α χ κ₁ φ₁)}
    {l₂ : List (RunFiber ν σ β ε δ ι α χ κ₂ φ₂)} (h : ListRel (FiberMeans C S) l₁ l₂)
    (id : FiberId) :
    OptRel (FiberMeans C S) (l₁.find? fun f => f.id = id) (l₂.find? fun f => f.id = id) := by
  induction h with
  | nil => exact True.intro
  | @cons a b l l' hab _ ih =>
    have hid : a.id = b.id := fiberMeans_id hab
    by_cases hx : a.id = id
    · have hy : b.id = id := by rw [← hid]; exact hx
      have e₁ : (List.find? (fun f => f.id = id) (a :: l)) = some a := by
        simp only [List.find?_cons_of_pos, decide_eq_true_eq, hx]
      have e₂ : (List.find? (fun f => f.id = id) (b :: l')) = some b := by
        simp only [List.find?_cons_of_pos, decide_eq_true_eq, hy]
      rw [e₁, e₂]; exact hab
    · have hy : ¬ (b.id = id) := by rw [← hid]; exact hx
      have e₁ : (List.find? (fun f => f.id = id) (a :: l))
          = List.find? (fun f => f.id = id) l := by
        simp only [List.find?_cons_of_neg, decide_eq_true_eq, hx, not_false_eq_true]
      have e₂ : (List.find? (fun f => f.id = id) (b :: l'))
          = List.find? (fun f => f.id = id) l' := by
        simp only [List.find?_cons_of_neg, decide_eq_true_eq, hy, not_false_eq_true]
      rw [e₁, e₂]; exact ih

theorem book_fiber? (h : BookMeans C S m₁ m₂) (id : FiberId) :
    OptRel (FiberMeans C S) (m₁.fiber? id) (m₂.fiber? id) := listRel_find h.1 id

theorem book_modify (h : BookMeans C S m₁ m₂) (id : FiberId)
    {k₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁ → RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {k₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂ → RunFiber ν σ β ε δ ι α χ κ₂ φ₂}
    (hk : ∀ f₁ f₂, FiberMeans C S f₁ f₂ → FiberMeans C S (k₁ f₁) (k₂ f₂)) :
    BookMeans C S (m₁.modify id k₁) (m₂.modify id k₂) := by
  have hf := book_fiber? h id
  unfold RunMachine.modify
  cases h₁ : m₁.fiber? id with
  | none =>
    cases h₂ : m₂.fiber? id with
    | none => exact h
    | some g => rw [h₁, h₂] at hf; exact absurd hf not_false
  | some f =>
    cases h₂ : m₂.fiber? id with
    | none => rw [h₁, h₂] at hf; exact absurd hf not_false
    | some g => rw [h₁, h₂] at hf; exact book_update h (hk f g hf)

/-- Both machines find a fiber, or neither. -/
theorem book_fiber?_cases (h : BookMeans C S m₁ m₂) (id : FiberId) :
    (m₁.fiber? id = none ∧ m₂.fiber? id = none) ∨
      ∃ f₁ f₂, m₁.fiber? id = some f₁ ∧ m₂.fiber? id = some f₂ ∧ FiberMeans C S f₁ f₂ := by
  have hf := book_fiber? h id
  cases h₁ : m₁.fiber? id with
  | none =>
    cases h₂ : m₂.fiber? id with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some g => rw [h₁, h₂] at hf; exact absurd hf not_false
  | some f =>
    cases h₂ : m₂.fiber? id with
    | none => rw [h₁, h₂] at hf; exact absurd hf not_false
    | some g => rw [h₁, h₂] at hf; exact Or.inr ⟨f, g, rfl, rfl, hf⟩

theorem listRel_insert (priority : Nat) {t₁ : Task ν σ β ε δ ι α κ₁} {t₂ : Task ν σ β ε δ ι α κ₂}
    (ht : TaskMeans C t₁ t₂) :
    ∀ {l₁ : List (Bucket ν σ β ε δ ι α κ₁)} {l₂ : List (Bucket ν σ β ε δ ι α κ₂)},
      ListRel (BucketMeans C) l₁ l₂ →
      ListRel (BucketMeans C) (Dispatcher.insert priority t₁ l₁) (Dispatcher.insert priority t₂ l₂) := by
  intro l₁ l₂ h
  induction h with
  | nil => exact ListRel.cons ⟨rfl, ListRel.cons ht ListRel.nil⟩ ListRel.nil
  | @cons b₁ b₂ l₁ l₂ hb hl ih =>
    show ListRel _
      (if b₁.priority = priority then ⟨b₁.priority, b₁.tasks ++ [t₁]⟩ :: l₁
        else if priority < b₁.priority then ⟨priority, [t₁]⟩ :: b₁ :: l₁
        else b₁ :: Dispatcher.insert priority t₁ l₁)
      (if b₂.priority = priority then ⟨b₂.priority, b₂.tasks ++ [t₂]⟩ :: l₂
        else if priority < b₂.priority then ⟨priority, [t₂]⟩ :: b₂ :: l₂
        else b₂ :: Dispatcher.insert priority t₂ l₂)
    rw [← hb.1]
    by_cases hp : b₁.priority = priority
    · rw [if_pos hp, if_pos hp]
      exact ListRel.cons ⟨rfl, ListRel.append hb.2 (ListRel.cons ht ListRel.nil)⟩ hl
    · rw [if_neg hp, if_neg hp]
      by_cases hlt : priority < b₁.priority
      · rw [if_pos hlt, if_pos hlt]
        exact ListRel.cons ⟨rfl, ListRel.cons ht ListRel.nil⟩ (ListRel.cons hb hl)
      · rw [if_neg hlt, if_neg hlt]
        exact ListRel.cons hb ih

theorem dispatcherMeans_enqueue {d₁ : Dispatcher ν σ β ε δ ι α κ₁} {d₂ : Dispatcher ν σ β ε δ ι α κ₂}
    (hd : DispatcherMeans C d₁ d₂) (priority : Nat) {t₁ : Task ν σ β ε δ ι α κ₁}
    {t₂ : Task ν σ β ε δ ι α κ₂} (ht : TaskMeans C t₁ t₂) :
    DispatcherMeans C (d₁.enqueue priority t₁) (d₂.enqueue priority t₂) :=
  ⟨listRel_insert priority ht hd.1, rfl⟩

theorem fiberMeans_enqueue {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (hf : FiberMeans C S f₁ f₂) (priority : Nat)
    {t₁ : Task ν σ β ε δ ι α κ₁} {t₂ : Task ν σ β ε δ ι α κ₂} (ht : TaskMeans C t₁ t₂) :
    FiberMeans C S { f₁ with dispatcher := f₁.dispatcher.enqueue priority t₁ }
      { f₂ with dispatcher := f₂.dispatcher.enqueue priority t₂ } :=
  ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1,
    dispatcherMeans_enqueue hf.2.2.2.2.2.2.2.2.2.2.2.1 priority ht,
    hf.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A post (the scheduler surface) keeps the book: both find the owner or neither. -/
theorem book_postTask {StOk : St → Prop} (hok : MachineOk StOk m₁) (h : BookMeans C S m₁ m₂) (owner : FiberId)
    (priority : Nat) {t₁ : Task ν σ β ε δ ι α κ₁} {t₂ : Task ν σ β ε δ ι α κ₂}
    (ht : TaskMeans C t₁ t₂) :
    MachineOk StOk (m₁.postTask owner priority t₁) ∧
      BookMeans C S (m₁.postTask owner priority t₁) (m₂.postTask owner priority t₂) := by
  unfold RunMachine.postTask
  rcases book_fiber?_cases h owner with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · simp only [h₁, h₂]
    exact ⟨machineOk_halt hok _, book_halt h _⟩
  · simp only [h₁, h₂]
    exact ⟨machineOk_emit (machineOk_arm (machineOk_update hok
        (pendingOk_dispatcher (pendingOk_of_fiber? hok h₁) _)) _) _,
      book_emit (book_arm (book_update h (fiberMeans_enqueue hf priority ht)) _) _ _⟩

/-- The drain of related owed lists keeps the book and answers related commands. -/
theorem book_drainOwed_aux {StOk : St → Prop} {d₁ : List (Owed κ₁)} {d₂ : List (Owed κ₂)}
    (hd : ListRel (OwedMeans C) d₁ d₂) :
    ∀ (n₁ : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) (n₂ : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂),
      MachineOk StOk n₁ → BookMeans C S n₁ n₂ →
      MachineOk StOk (drainOwed n₁ d₁).1 ∧
        BookMeans C S (drainOwed n₁ d₁).1 (drainOwed n₂ d₂).1 ∧
        ListRel (CmdMeans C) (drainOwed n₁ d₁).2 (drainOwed n₂ d₂).2 := by
  induction hd with
  | nil => intro n₁ n₂ hok h; exact ⟨hok, h, ListRel.nil⟩
  | @cons a b l₁ l₂ hab hl ih =>
    intro n₁ n₂ hok h
    have hmode := hab.2.2.2
    unfold drainOwed
    rcases ha : a.mode with _ | ⟨owner, priority⟩ <;>
      rcases hb : b.mode with _ | ⟨owner', priority'⟩ <;> rw [ha, hb] at hmode
    · obtain ⟨hok', h', hc⟩ := ih n₁ n₂ hok h
      exact ⟨hok', h', ListRel.cons ⟨hab.1, hab.2.1, hab.2.2.1⟩ hc⟩
    · exact absurd hmode (by simp)
    · exact absurd hmode (by simp)
    · obtain ⟨rfl, rfl⟩ := WakeMode.scheduled.inj hmode
      have ht : TaskMeans C (Task.resume a.waiter a.token a.code : Task ν σ β ε δ ι α κ₁)
          (Task.resume b.waiter b.token b.code : Task ν σ β ε δ ι α κ₂) :=
        ⟨hab.1, hab.2.1, hab.2.2.1⟩
      obtain ⟨hok', h'⟩ := book_postTask hok h owner priority ht
      exact ih _ _ hok' h'

/-- The drain of related owed lists (the scheduler surface): both machines keep the book. -/
theorem book_drainOwed {StOk : St → Prop} (hok : MachineOk StOk m₁) (h : BookMeans C S m₁ m₂)
    {d₁ : List (Owed κ₁)} {d₂ : List (Owed κ₂)} (hd : ListRel (OwedMeans C) d₁ d₂) :
    MachineOk StOk (drainOwed m₁ d₁).1 ∧
      BookMeans C S (drainOwed m₁ d₁).1 (drainOwed m₂ d₂).1 ∧
      ListRel (CmdMeans C) (drainOwed m₁ d₁).2 (drainOwed m₂ d₂).2 :=
  book_drainOwed_aux hd m₁ m₂ hok h

theorem all_exits {l₁ : List (RunFiber ν σ β ε δ ι α χ κ₁ φ₁)}
    {l₂ : List (RunFiber ν σ β ε δ ι α χ κ₂ φ₂)} (h : ListRel (FiberMeans C S) l₁ l₂) :
    (l₁.all fun f => f.exit.isSome) = (l₂.all fun f => f.exit.isSome) := by
  induction h with
  | nil => rfl
  | @cons x y _ _ hd _ ih =>
    show (x.exit.isSome && _) = (y.exit.isSome && _)
    rw [hd.2.2.2.2.1, ih]

theorem book_finished (h : BookMeans C S m₁ m₂) : m₁.finished = m₂.finished :=
  all_exits h.1

theorem completedExits_rel {l₁ : List (RunFiber ν σ β ε δ ι α χ κ₁ φ₁)}
    {l₂ : List (RunFiber ν σ β ε δ ι α χ κ₂ φ₂)} (h : ListRel (FiberMeans C S) l₁ l₂) :
    (l₁.filterMap fun f => f.exit.map fun ex => (f.id, ex)) =
      (l₂.filterMap fun f => f.exit.map fun ex => (f.id, ex)) := by
  induction h with
  | nil => rfl
  | @cons a b _ _ hab _ ih =>
    simp only [List.filterMap_cons]
    rw [fiberMeans_id hab, fiberMeans_exit hab, ih]

/-- The completed-exit view both instances hand their construction callbacks. -/
theorem book_completedExits (h : BookMeans C S m₁ m₂) :
    m₁.completedExits = m₂.completedExits :=
  completedExits_rel h.1

end Book

/-! ## The loop: one induction, for both instances at once -/

section Loop

variable {C : κ₁ → κ₂ → Prop} {S : φ₁ → φ₂ → Prop} {StOk : St → Prop}
variable [FiberEvaluator ν σ β ε δ ι α χ St κ₁ φ₁ η₁]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ₂ φ₂ η₂]
variable (i₁ : RunInterp ν σ β ε δ ι α χ St κ₁) (i₂ : RunInterp ν σ β ε δ ι α χ St κ₂)

/-- The one obligation the two instances owe: their `driveStep`s agree on the book and keep
the left invariant, on a machine the loop still drives (not halted). It is discharged from
the evaluator arms, since `driveStep` reads code only through `evaluate` and the
interpreter's code-valued hooks. -/
def StepAgrees (StOk : St → Prop) (C : κ₁ → κ₂ → Prop) (S : φ₁ → φ₂ → Prop) : Prop :=
  ∀ (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂)
    c₁ c₂ r₁ r₂, a.stuck = none → MachineOk StOk a → BookMeans C S a b → CmdMeans C c₁ c₂ →
      ListRel (CmdMeans C) r₁ r₂ →
      MachineOk StOk (driveStep i₁ a c₁ r₁).1 ∧
        BookMeans C S (driveStep i₁ a c₁ r₁).1 (driveStep i₂ b c₂ r₂).1 ∧
        ListRel (CmdMeans C) (driveStep i₁ a c₁ r₁).2 (driveStep i₂ b c₂ r₂).2

/-- Under one hypothesis about a single command, the whole fuel-bounded loop preserves the
book — machine *and* residue — and the invariant. -/
theorem book_driveState (hstep : StepAgrees i₁ i₂ StOk C S) :
    ∀ (fuel : Nat) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂) c₁ c₂,
      MachineOk StOk a → BookMeans C S a b → ListRel (CmdMeans C) c₁ c₂ →
      MachineOk StOk (driveState i₁ fuel a c₁).1 ∧
        BookMeans C S (driveState i₁ fuel a c₁).1 (driveState i₂ fuel b c₂).1 ∧
        ListRel (CmdMeans C) (driveState i₁ fuel a c₁).2 (driveState i₂ fuel b c₂).2 := by
  intro fuel
  induction fuel with
  | zero => intro a b c₁ c₂ hok h hc; exact ⟨hok, h, hc⟩
  | succ n ih =>
    intro a b c₁ c₂ hok h hc
    cases hc with
    | nil => rw [driveState_nil, driveState_nil]; exact ⟨hok, h, ListRel.nil⟩
    | @cons x y l l' hxy hl =>
      by_cases hs : b.stuck.isSome = true
      · have hs' : a.stuck.isSome = true := by rw [h.stuck]; exact hs
        rw [driveState_stuck i₁ _ a _ hs', driveState_stuck i₂ _ b _ hs]
        exact ⟨hok, h, ListRel.cons hxy hl⟩
      · have hs' : ¬ (a.stuck.isSome = true) := by rw [h.stuck]; exact hs
        have hsn : a.stuck = none := by
          cases hsk : a.stuck with
          | none => rfl
          | some w => exact absurd (by rw [hsk]; rfl) hs'
        rw [driveState_succ_cons, driveState_succ_cons, if_neg hs', if_neg hs]
        obtain ⟨hok', h', hc'⟩ := hstep a b x y l l' hsn hok h hxy hl
        exact ih _ _ _ _ hok' h' hc'

/-- The receipt of the loop is the same on both sides: the two runs agree on their
frontiers, not merely on their machines. -/
theorem book_settled (hstep : StepAgrees i₁ i₂ StOk C S) (fuel : Nat)
    {a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁} {b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂}
    {c₁ c₂} (hok : MachineOk StOk a) (h : BookMeans C S a b) (hc : ListRel (CmdMeans C) c₁ c₂) :
    settled (driveState i₁ fuel a c₁) = settled (driveState i₂ fuel b c₂) := by
  have hr := book_driveState i₁ i₂ hstep fuel a b c₁ c₂ hok h hc
  unfold settled
  rw [ListRel.isEmpty hr.2.2, hr.2.1.stuck]

/-! ### `fire`: a fold over the drained dispatcher -/

theorem taskCmds_rel {t₁ : Task ν σ β ε δ ι α κ₁} {t₂ : Task ν σ β ε δ ι α κ₂}
    (h : TaskMeans C t₁ t₂) : ListRel (CmdMeans C) (taskCmds t₁) (taskCmds t₂) := by
  cases t₁ <;> cases t₂ <;> first
    | exact absurd h not_false
    | (refine ListRel.cons ?_ (ListRel.cons True.intro ListRel.nil); exact h)
    | (refine ListRel.cons ?_ (ListRel.cons True.intro ListRel.nil)
       exact ⟨h.1, h.2.1, h.2.2⟩)

theorem flatten_tasks_rel {l₁ : List (Bucket ν σ β ε δ ι α κ₁)}
    {l₂ : List (Bucket ν σ β ε δ ι α κ₂)} (h : ListRel (BucketMeans C) l₁ l₂) :
    ListRel (TaskMeans C) ((l₁.map Bucket.tasks).flatten) ((l₂.map Bucket.tasks).flatten) := by
  induction h with
  | nil => exact ListRel.nil
  | cons hd _ ih => exact ListRel.append hd.2 ih

theorem drain_rel {d₁ : Dispatcher ν σ β ε δ ι α κ₁}
    {d₂ : Dispatcher ν σ β ε δ ι α κ₂} (h : DispatcherMeans C d₁ d₂) :
    ListRel (TaskMeans C) (d₁.drain).1 (d₂.drain).1 := flatten_tasks_rel h.1

theorem fiberMeans_drained {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (hf : FiberMeans C S f₁ f₂) :
    FiberMeans C S { f₁ with dispatcher := (f₁.dispatcher.drain).2 }
      { f₂ with dispatcher := (f₂.dispatcher.drain).2 } :=
  ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1,
    ⟨ListRel.nil, rfl⟩, hf.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem book_fireStep (hstep : StepAgrees i₁ i₂ StOk C S) (fuel : Nat) (owner : FiberId)
    {a₁ : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁ × Bool}
    {a₂ : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂ × Bool}
    {t₁ : Task ν σ β ε δ ι α κ₁} {t₂ : Task ν σ β ε δ ι α κ₂}
    (ha : MachineOk StOk a₁.1 ∧ BookMeans C S a₁.1 a₂.1 ∧ a₁.2 = a₂.2) (ht : TaskMeans C t₁ t₂) :
    MachineOk StOk (fireStep i₁ fuel owner a₁ t₁).1 ∧
      BookMeans C S (fireStep i₁ fuel owner a₁ t₁).1 (fireStep i₂ fuel owner a₂ t₂).1 ∧
      (fireStep i₁ fuel owner a₁ t₁).2 = (fireStep i₂ fuel owner a₂ t₂).2 := by
  unfold fireStep
  rw [ha.2.2]
  by_cases hb : a₂.2 = true
  · rw [if_pos hb, if_pos hb]
    have hm := book_emit ha.2.1 [RunEvent.ranTask owner t₁] [RunEvent.ranTask owner t₂]
    have hmok := machineOk_emit ha.1 [RunEvent.ranTask owner t₁]
    exact ⟨(book_driveState i₁ i₂ hstep fuel _ _ _ _ hmok hm (taskCmds_rel ht)).1,
      (book_driveState i₁ i₂ hstep fuel _ _ _ _ hmok hm (taskCmds_rel ht)).2.1,
      book_settled i₁ i₂ hstep fuel hmok hm (taskCmds_rel ht)⟩
  · rw [if_neg hb, if_neg hb]; exact ha

theorem book_fireState (hstep : StepAgrees i₁ i₂ StOk C S) (fuel : Nat)
    {a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁} {b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂}
    (hok : MachineOk StOk a) (h : BookMeans C S a b) (owner : FiberId) :
    MachineOk StOk (fireState i₁ fuel a owner).1 ∧
      BookMeans C S (fireState i₁ fuel a owner).1 (fireState i₂ fuel b owner).1 ∧
      (fireState i₁ fuel a owner).2 = (fireState i₂ fuel b owner).2 := by
  unfold fireState
  rcases book_fiber?_cases h owner with ⟨h₁, h₂⟩ | ⟨o₁, o₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]; exact ⟨hok, h, rfl⟩
  · rw [h₁, h₂]
    refine foldl_rel
      (P := fun (x : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁ × Bool)
              (y : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂ × Bool) =>
            MachineOk StOk x.1 ∧ BookMeans C S x.1 y.1 ∧ x.2 = y.2)
      (R := TaskMeans C) (f₁ := fireStep i₁ fuel owner) (f₂ := fireStep i₂ fuel owner)
      (fun _ _ _ _ hp hr => book_fireStep i₁ i₂ hstep fuel owner hp hr)
      (drain_rel hf.2.2.2.2.2.2.2.2.2.2.2.1) ?_
    exact ⟨machineOk_disarm (machineOk_update hok
        (pendingOk_dispatcher (pendingOk_of_fiber? hok h₁) _)) owner,
      book_disarm (book_update h (fiberMeans_drained hf)) owner, rfl⟩

/-! ### `flushAll` and `flushRoot`: recursions on rounds -/

/-- The one-step equation of the round loop, spelled so that the recursive call stays
folded. -/
theorem flushAllState_succ (i : RunInterp ν σ β ε δ ι α χ St κ₁) (fuel n : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) :
    flushAllState i fuel (n + 1) m =
      (match m.armed with
       | [] => (m, true)
       | owner :: _ =>
         if m.stuck.isSome then (m, true)
         else if (fireState i fuel m owner).2 then
           flushAllState i fuel n (fireState i fuel m owner).1
         else fireState i fuel m owner) := rfl

theorem book_flushAllState (hstep : StepAgrees i₁ i₂ StOk C S) (fuel : Nat) :
    ∀ (rounds : Nat) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂), MachineOk StOk a → BookMeans C S a b →
      MachineOk StOk (flushAllState i₁ fuel rounds a).1 ∧
        BookMeans C S (flushAllState i₁ fuel rounds a).1 (flushAllState i₂ fuel rounds b).1 ∧
        (flushAllState i₁ fuel rounds a).2 = (flushAllState i₂ fuel rounds b).2 := by
  intro rounds
  induction rounds with
  | zero =>
    intro a b hok h
    exact ⟨hok, h, by
      show (a.armed.isEmpty || a.stuck.isSome) = (b.armed.isEmpty || b.stuck.isSome)
      rw [h.armed, h.stuck]⟩
  | succ n ih =>
    intro a b hok h
    rw [flushAllState_succ i₁ fuel n a, flushAllState_succ i₂ fuel n b]
    cases hb : b.armed with
    | nil =>
      simp only [h.armed.trans hb]
      exact ⟨hok, h, trivial⟩
    | cons owner rest =>
      simp only [h.armed.trans hb]
      by_cases hs : b.stuck.isSome = true
      · have hs' : a.stuck.isSome = true := by rw [h.stuck]; exact hs
        rw [if_pos hs', if_pos hs]; exact ⟨hok, h, rfl⟩
      · have hs' : ¬ (a.stuck.isSome = true) := by rw [h.stuck]; exact hs
        rw [if_neg hs', if_neg hs]
        have hfire := book_fireState i₁ i₂ hstep fuel hok h owner
        rw [hfire.2.2]
        by_cases hr : (fireState i₂ fuel b owner).2 = true
        · rw [if_pos hr, if_pos hr]; exact ih _ _ hfire.1 hfire.2.1
        · rw [if_neg hr, if_neg hr]; exact ⟨hfire.1, hfire.2.1, hfire.2.2⟩

theorem flushRootState_zero (i : RunInterp ν σ β ε δ ι α χ St κ₁) (fuel : Nat) (root : FiberId)
    (m : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) :
    flushRootState i fuel root 0 m =
      (match m.fiber? root with
       | none => (m, true)
       | some o => (m, o.dispatcher.buckets.isEmpty || m.stuck.isSome)) := rfl

theorem flushRootState_succ (i : RunInterp ν σ β ε δ ι α χ St κ₁) (fuel : Nat) (root : FiberId)
    (n : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) :
    flushRootState i fuel root (n + 1) m =
      (match m.fiber? root with
       | none => (m, true)
       | some o =>
         if o.dispatcher.buckets.isEmpty || m.stuck.isSome then (m, true)
         else if (fireState i fuel m root).2 then
           flushRootState i fuel root n (fireState i fuel m root).1
         else fireState i fuel m root) := rfl

theorem dispatcherMeans_isEmpty {d₁ : Dispatcher ν σ β ε δ ι α κ₁}
    {d₂ : Dispatcher ν σ β ε δ ι α κ₂} (h : DispatcherMeans C d₁ d₂) :
    d₁.buckets.isEmpty = d₂.buckets.isEmpty := ListRel.isEmpty h.1

theorem book_flushRootState (hstep : StepAgrees i₁ i₂ StOk C S) (fuel : Nat) (root : FiberId) :
    ∀ (rounds : Nat) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂), MachineOk StOk a → BookMeans C S a b →
      MachineOk StOk (flushRootState i₁ fuel root rounds a).1 ∧
        BookMeans C S (flushRootState i₁ fuel root rounds a).1
          (flushRootState i₂ fuel root rounds b).1 ∧
        (flushRootState i₁ fuel root rounds a).2 = (flushRootState i₂ fuel root rounds b).2 := by
  intro rounds
  induction rounds with
  | zero =>
    intro a b hok h
    rw [flushRootState_zero, flushRootState_zero]
    rcases book_fiber?_cases h root with ⟨h₁, h₂⟩ | ⟨o₁, o₂, h₁, h₂, hf⟩
    · rw [h₁, h₂]; exact ⟨hok, h, rfl⟩
    · rw [h₁, h₂]
      refine ⟨hok, h, ?_⟩
      show (o₁.dispatcher.buckets.isEmpty || a.stuck.isSome) =
        (o₂.dispatcher.buckets.isEmpty || b.stuck.isSome)
      rw [dispatcherMeans_isEmpty hf.2.2.2.2.2.2.2.2.2.2.2.1, h.stuck]
  | succ n ih =>
    intro a b hok h
    rw [flushRootState_succ, flushRootState_succ]
    rcases book_fiber?_cases h root with ⟨h₁, h₂⟩ | ⟨o₁, o₂, h₁, h₂, hf⟩
    · rw [h₁, h₂]; exact ⟨hok, h, rfl⟩
    · rw [h₁, h₂]
      have he : o₁.dispatcher.buckets.isEmpty = o₂.dispatcher.buckets.isEmpty :=
        dispatcherMeans_isEmpty hf.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [he, h.stuck]
      by_cases hc : (o₂.dispatcher.buckets.isEmpty || b.stuck.isSome) = true
      · rw [if_pos hc, if_pos hc]; exact ⟨hok, h, rfl⟩
      · rw [if_neg hc, if_neg hc]
        have hfire := book_fireState i₁ i₂ hstep fuel hok h root
        rw [hfire.2.2]
        by_cases hr : (fireState i₂ fuel b root).2 = true
        · rw [if_pos hr, if_pos hr]; exact ih _ _ hfire.1 hfire.2.1
        · rw [if_neg hr, if_neg hr]; exact ⟨hfire.1, hfire.2.1, hfire.2.2⟩

/-! ### The decisions, and replay -/

theorem fiberMeans_yield {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (hf : FiberMeans C S f₁ f₂) (v : Option Bool) :
    FiberMeans C S { f₁ with yieldOverride := v } { f₂ with yieldOverride := v } :=
  ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.1, rfl, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The `interruptFrom` arm with its destructuring `let`s expanded, so a `rw` reaches the
fiber lookup; `rfl` by structure eta on the pair. -/
theorem stepDecisionState_interruptFrom (i : RunInterp ν σ β ε δ ι α χ St κ₁) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) (interruptor : Option FiberId)
    (annotations : ReasonAnnotations α) (target : FiberId) :
    stepDecisionState i fuel m (RunDecision.interruptFrom interruptor annotations target) =
      (match m.fiber? target with
       | none => (m, true)
       | some t =>
         let m' := (if core₁.deferredInterrupt (interruptRecord i interruptor annotations t).1.frame &&
                       (interruptRecord i interruptor annotations t).1.running then
                     (m.emit [RunEvent.interruptRecorded interruptor target]).emit
                       [RunEvent.interruptDeferred target]
                   else m.emit [RunEvent.interruptRecorded interruptor target]).update
                     (interruptRecord i interruptor annotations t).1
         if (interruptRecord i interruptor annotations t).2 then
           ((driveState i fuel m' [Cmd.evaluate target, Cmd.drainDue]).1,
             settled (driveState i fuel m' [Cmd.evaluate target, Cmd.drainDue]))
         else (m', true)) := rfl

/-- The two hook obligations beside `StepAgrees`: the external `Completion` reads into
related code, and the interrupt record — a `FiberCore` homomorphism obligation — agrees. -/
def HooksAgree (StOk : St → Prop) (C : κ₁ → κ₂ → Prop) (S : φ₁ → φ₂ → Prop) : Prop :=
  (∀ answer, C (i₁.answerCode answer) (i₂.answerCode answer)) ∧
    (∀ (t₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁) (t₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂) who extra,
      FiberMeans C S t₁ t₂ →
      FiberMeans C S (interruptRecord i₁ who extra t₁).1 (interruptRecord i₂ who extra t₂).1 ∧
        (interruptRecord i₁ who extra t₁).2 = (interruptRecord i₂ who extra t₂).2) ∧
    -- the clock step (the timer, A4): the same store, the owed resume in the book, the
    -- invariant kept
    ∀ millis s, StOk s →
      StOk (i₁.clockStep millis s).2 ∧ (i₁.clockStep millis s).2 = (i₂.clockStep millis s).2 ∧
        ListRel (OwedMeans C) (i₁.clockStep millis s).1.toList (i₂.clockStep millis s).1.toList

/-- The advance lemma (the timer, A4): fire by fire, the two instances drain the same owed
resume, drive and flush in the book, and recur on machines in the book. -/
theorem book_advanceState (hstep : StepAgrees i₁ i₂ StOk C S)
    (hclock : ∀ millis s, StOk s →
      StOk (i₁.clockStep millis s).2 ∧ (i₁.clockStep millis s).2 = (i₂.clockStep millis s).2 ∧
        ListRel (OwedMeans C) (i₁.clockStep millis s).1.toList (i₂.clockStep millis s).1.toList)
    (fuel millis : Nat) :
    ∀ (rounds : Nat) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂), MachineOk StOk a → BookMeans C S a b →
      MachineOk StOk (advanceState i₁ fuel millis rounds a).1 ∧
        BookMeans C S (advanceState i₁ fuel millis rounds a).1 (advanceState i₂ fuel millis rounds b).1 ∧
        (advanceState i₁ fuel millis rounds a).2 = (advanceState i₂ fuel millis rounds b).2
  | 0, a, b, hok, h => ⟨hok, h, rfl⟩
  | rounds + 1, a, b, hok, h => by
    unfold advanceState
    by_cases hs : b.stuck.isSome = true
    · have hs' : a.stuck.isSome = true := by rw [h.stuck]; exact hs
      rw [if_pos hs', if_pos hs]; exact ⟨hok, h, rfl⟩
    · have hs' : ¬ (a.stuck.isSome = true) := by rw [h.stuck]; exact hs
      rw [if_neg hs', if_neg hs]
      obtain ⟨hcok, hceq, hcrel⟩ := hclock millis a.state hok.1
      rw [← h.state]
      rcases hc1 : i₁.clockStep millis a.state with ⟨o₁, st₁⟩
      rcases hc2 : i₂.clockStep millis a.state with ⟨o₂, st₂⟩
      rw [hc1] at hcok hceq hcrel
      rw [hc2] at hceq hcrel
      simp only at hcok hceq hcrel
      subst hceq
      have hok' : MachineOk StOk { a with state := st₁ } := machineOk_stateOf hok hcok
      have h' : BookMeans C S { a with state := st₁ } { b with state := st₁ } := book_stateOf h st₁
      cases o₁ with
      | none =>
        cases o₂ with
        | none => exact ⟨hok', h', rfl⟩
        | some d₂ => exact absurd hcrel (by intro hr; cases hr)
      | some d₁ =>
        cases o₂ with
        | none => exact absurd hcrel (by intro hr; cases hr)
        | some d₂ =>
          dsimp only
          have hd : OwedMeans C d₁ d₂ := by
            cases hcrel with
            | cons hd _ => exact hd
          obtain ⟨hok1, h1, hcmds⟩ := book_drainOwed hok' h' (ListRel.cons hd ListRel.nil)
          have hc : ListRel (CmdMeans C)
              ((drainOwed { a with state := st₁ } [d₁]).2 ++ [Cmd.drainDue])
              ((drainOwed { b with state := st₁ } [d₂]).2 ++ [Cmd.drainDue]) :=
            ListRel.append hcmds (ListRel.cons True.intro ListRel.nil)
          obtain ⟨hok2, h2, _⟩ := book_driveState i₁ i₂ hstep fuel _ _ _ _ hok1 h1 hc
          have hsettled := book_settled i₁ i₂ hstep fuel hok1 h1 hc
          rw [hsettled]
          by_cases hsd : settled (driveState i₂ fuel (drainOwed { b with state := st₁ } [d₂]).1
              ((drainOwed { b with state := st₁ } [d₂]).2 ++ [Cmd.drainDue])) = true
          · rw [if_pos hsd, if_pos hsd]
            obtain ⟨hok3, h3, hf⟩ := book_flushAllState i₁ i₂ hstep fuel fuel _ _ hok2 h2
            rw [hf]
            by_cases hfr : (flushAllState i₂ fuel fuel (driveState i₂ fuel
                (drainOwed { b with state := st₁ } [d₂]).1
                ((drainOwed { b with state := st₁ } [d₂]).2 ++ [Cmd.drainDue])).1).2 = true
            · rw [if_pos hfr, if_pos hfr]
              exact book_advanceState hstep hclock fuel millis rounds _ _ hok3 h3
            · rw [if_neg hfr, if_neg hfr]
              exact ⟨hok3, h3, hf⟩
          · rw [if_neg hsd, if_neg hsd]
            exact ⟨hok2, h2, rfl⟩

/-- The decision lemma, once for all eight decisions. -/
theorem book_stepDecisionState (hstep : StepAgrees i₁ i₂ StOk C S) (hooks : HooksAgree i₁ i₂ StOk C S)
    (fuel : Nat)
    {a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁} {b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂}
    (hok : MachineOk StOk a) (h : BookMeans C S a b) (decision : RunDecision ν σ β ε δ ι α) :
    MachineOk StOk (stepDecisionState i₁ fuel a decision).1 ∧
      BookMeans C S (stepDecisionState i₁ fuel a decision).1
        (stepDecisionState i₂ fuel b decision).1 ∧
      (stepDecisionState i₁ fuel a decision).2 = (stepDecisionState i₂ fuel b decision).2 := by
  obtain ⟨hans, hrec, hclock⟩ := hooks
  cases decision with
  | fire owner => exact book_fireState i₁ i₂ hstep fuel hok h owner
  | flush => exact book_flushAllState i₁ i₂ hstep fuel fuel a b hok h
  | advance millis => exact book_advanceState i₁ i₂ hstep hclock fuel millis fuel a b hok h
  | evaluate id =>
    have hc : ListRel (CmdMeans C)
        ([Cmd.evaluate id, Cmd.drainDue] : List (Cmd ν σ β ε δ ι α κ₁))
        ([Cmd.evaluate id, Cmd.drainDue] : List (Cmd ν σ β ε δ ι α κ₂)) :=
      ListRel.cons rfl (ListRel.cons True.intro ListRel.nil)
    exact ⟨(book_driveState i₁ i₂ hstep fuel a b _ _ hok h hc).1,
      (book_driveState i₁ i₂ hstep fuel a b _ _ hok h hc).2.1,
      book_settled i₁ i₂ hstep fuel hok h hc⟩
  | yieldVerdict id verdict =>
    exact ⟨machineOk_modify hok id (fun _ hf => hf),
      book_modify h id (fun _ _ hf => fiberMeans_yield hf (some verdict)), rfl⟩
  | answerAsync id token answer =>
    have hc : ListRel (CmdMeans C)
        ([Cmd.resume id token (i₁.answerCode answer), Cmd.drainDue] : List (Cmd ν σ β ε δ ι α κ₁))
        ([Cmd.resume id token (i₂.answerCode answer), Cmd.drainDue] : List (Cmd ν σ β ε δ ι α κ₂)) :=
      ListRel.cons ⟨rfl, rfl, hans answer⟩ (ListRel.cons True.intro ListRel.nil)
    exact ⟨(book_driveState i₁ i₂ hstep fuel a b _ _ hok h hc).1,
      (book_driveState i₁ i₂ hstep fuel a b _ _ hok h hc).2.1,
      book_settled i₁ i₂ hstep fuel hok h hc⟩
  | interruptFrom interruptor annotations target =>
    have hc : ListRel (CmdMeans C)
        ([Cmd.evaluate target, Cmd.drainDue] : List (Cmd ν σ β ε δ ι α κ₁))
        ([Cmd.evaluate target, Cmd.drainDue] : List (Cmd ν σ β ε δ ι α κ₂)) :=
      ListRel.cons rfl (ListRel.cons True.intro ListRel.nil)
    rw [stepDecisionState_interruptFrom i₁ fuel a, stepDecisionState_interruptFrom i₂ fuel b]
    rcases book_fiber?_cases h target with ⟨h₁, h₂⟩ | ⟨t₁, t₂, h₁, h₂, hf⟩
    · rw [h₁, h₂]; exact ⟨hok, h, rfl⟩
    · rw [h₁, h₂]
      simp only []
      have hr := hrec t₁ t₂ interruptor annotations hf
      have hpend : PendingOk (interruptRecord i₁ interruptor annotations t₁).1 :=
        interruptRecord_pendingOk i₁ interruptor annotations (pendingOk_of_fiber? hok h₁)
      have hbase2 : BookMeans C S
          (((a.emit [RunEvent.interruptRecorded interruptor target]).emit
            [RunEvent.interruptDeferred target]).update
              (interruptRecord i₁ interruptor annotations t₁).1)
          (((b.emit [RunEvent.interruptRecorded interruptor target]).emit
            [RunEvent.interruptDeferred target]).update
              (interruptRecord i₂ interruptor annotations t₂).1) := book_update h hr.1
      have hbase2ok : MachineOk StOk
          (((a.emit [RunEvent.interruptRecorded interruptor target]).emit
            [RunEvent.interruptDeferred target]).update
              (interruptRecord i₁ interruptor annotations t₁).1) :=
        machineOk_update (machineOk_emit (machineOk_emit hok _) _) hpend
      have hbase1 : BookMeans C S
          ((a.emit [RunEvent.interruptRecorded interruptor target]).update
              (interruptRecord i₁ interruptor annotations t₁).1)
          ((b.emit [RunEvent.interruptRecorded interruptor target]).update
              (interruptRecord i₂ interruptor annotations t₂).1) := book_update h hr.1
      have hbase1ok : MachineOk StOk
          ((a.emit [RunEvent.interruptRecorded interruptor target]).update
              (interruptRecord i₁ interruptor annotations t₁).1) :=
        machineOk_update (machineOk_emit hok _) hpend
      have hd : core₁.deferredInterrupt (interruptRecord i₁ interruptor annotations t₁).1.frame
          = core₂.deferredInterrupt (interruptRecord i₂ interruptor annotations t₂).1.frame :=
        fiberMeans_deferred hr.1
      have hrun : (interruptRecord i₁ interruptor annotations t₁).1.running
          = (interruptRecord i₂ interruptor annotations t₂).1.running := hr.1.2.1
      rw [hd, hrun, hr.2]
      by_cases hc2 : (core₂.deferredInterrupt (interruptRecord i₂ interruptor annotations t₂).1.frame
          && (interruptRecord i₂ interruptor annotations t₂).1.running) = true
      · rw [if_pos hc2, if_pos hc2]
        by_cases hap : (interruptRecord i₂ interruptor annotations t₂).2 = true
        · rw [if_pos hap, if_pos hap]
          exact ⟨(book_driveState i₁ i₂ hstep fuel _ _ _ _ hbase2ok hbase2 hc).1,
            (book_driveState i₁ i₂ hstep fuel _ _ _ _ hbase2ok hbase2 hc).2.1,
            book_settled i₁ i₂ hstep fuel hbase2ok hbase2 hc⟩
        · rw [if_neg hap, if_neg hap]
          exact ⟨hbase2ok, hbase2, rfl⟩
      · rw [if_neg hc2, if_neg hc2]
        by_cases hap : (interruptRecord i₂ interruptor annotations t₂).2 = true
        · rw [if_pos hap, if_pos hap]
          exact ⟨(book_driveState i₁ i₂ hstep fuel _ _ _ _ hbase1ok hbase1 hc).1,
            (book_driveState i₁ i₂ hstep fuel _ _ _ _ hbase1ok hbase1 hc).2.1,
            book_settled i₁ i₂ hstep fuel hbase1ok hbase1 hc⟩
        · rw [if_neg hap, if_neg hap]
          exact ⟨hbase1ok, hbase1, rfl⟩
  | installMiddleware => exact ⟨machineOk_middleware hok, book_middleware h, rfl⟩

/-- Two replays classify alike, and their machines keep the book. -/
def ReplayRel (C : κ₁ → κ₂ → Prop) (S : φ₁ → φ₂ → Prop) :
    ReplayResult ν σ β ε δ ι α χ St κ₁ φ₁ η₁ → ReplayResult ν σ β ε δ ι α χ St κ₂ φ₂ η₂ → Prop
  | .finished m₁, .finished m₂ => BookMeans C S m₁ m₂
  | .frontier m₁, .frontier m₂ => BookMeans C S m₁ m₂
  | .stuck w₁ m₁, .stuck w₂ m₂ => w₁ = w₂ ∧ BookMeans C S m₁ m₂
  | _, _ => False

theorem ReplayRel.machine {r₁ : ReplayResult ν σ β ε δ ι α χ St κ₁ φ₁ η₁}
    {r₂ : ReplayResult ν σ β ε δ ι α χ St κ₂ φ₂ η₂} (h : ReplayRel C S r₁ r₂) :
    BookMeans C S r₁.machine r₂.machine := by
  cases r₁ <;> cases r₂ <;> first | exact h | exact h.2 | exact absurd h not_false

theorem replayEval_nil (i : RunInterp ν σ β ε δ ι α χ St κ₁) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) :
    replayEval i fuel [] m =
      (match m.stuck with
       | some why => ReplayResult.stuck why m
       | none => if m.finished then ReplayResult.finished m else ReplayResult.frontier m) := rfl

theorem replayEval_cons (i : RunInterp ν σ β ε δ ι α χ St κ₁) (fuel : Nat)
    (d : RunDecision ν σ β ε δ ι α) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁) :
    replayEval i fuel (d :: tape) m =
      (match m.stuck with
       | some why => ReplayResult.stuck why m
       | none =>
         if (stepDecisionState i fuel m d).2 then
           replayEval i fuel tape (stepDecisionState i fuel m d).1
         else ReplayResult.frontier (stepDecisionState i fuel m d).1) := rfl

/-- **Replay agrees.** Two instances with `StepAgrees` and the two hook obligations replay
every tape to the same classification and related books. -/
theorem book_replayEval (hstep : StepAgrees i₁ i₂ StOk C S) (hooks : HooksAgree i₁ i₂ StOk C S)
    (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂), MachineOk StOk a → BookMeans C S a b →
      ReplayRel C S (replayEval i₁ fuel tape a) (replayEval i₂ fuel tape b) := by
  intro tape
  induction tape with
  | nil =>
    intro a b _ h
    rw [replayEval_nil, replayEval_nil, h.stuck]
    cases hs : b.stuck with
    | some why => exact ⟨rfl, h⟩
    | none =>
      rw [book_finished h]
      by_cases hb : b.finished = true
      · rw [if_pos hb, if_pos hb]; exact h
      · rw [if_neg hb, if_neg hb]; exact h
  | cons d rest ih =>
    intro a b hok h
    rw [replayEval_cons, replayEval_cons, h.stuck]
    cases hs : b.stuck with
    | some why => exact ⟨rfl, h⟩
    | none =>
      have hd := book_stepDecisionState i₁ i₂ hstep hooks fuel hok h d
      rw [hd.2.2]
      by_cases hr : (stepDecisionState i₂ fuel b d).2 = true
      · rw [if_pos hr, if_pos hr]; exact ih _ _ hd.1 hd.2.1
      · rw [if_neg hr, if_neg hr]; exact hd.2.1

/-- The sufficiency receipt of a whole tape agrees. -/
theorem book_suffices (hstep : StepAgrees i₁ i₂ StOk C S) (hooks : HooksAgree i₁ i₂ StOk C S)
    (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂), MachineOk StOk a → BookMeans C S a b →
      Suffices i₁ fuel tape a = Suffices i₂ fuel tape b := by
  intro tape
  induction tape with
  | nil => intro a b _ _; rfl
  | cons d rest ih =>
    intro a b hok h
    have hd := book_stepDecisionState i₁ i₂ hstep hooks fuel hok h d
    unfold Suffices
    rw [h.stuck]
    cases hs : b.stuck with
    | some why => rfl
    | none =>
      dsimp only
      rw [hd.2.2, ih _ _ hd.1 hd.2.1]

end Loop

end Generic

/-! ## What the book gives at the value alphabet -/

section Observation

variable {ν σ χ κ₁ φ₁ η₁ κ₂ φ₂ η₂ : Type}
variable [FiberCore ν Val Err Defect FiberId Ann κ₁ φ₁] [FiberCore ν Val Err Defect FiberId Ann κ₂ φ₂]
variable {C : κ₁ → κ₂ → Prop} {S : φ₁ → φ₂ → Prop}

theorem bookMeans_exits {m₁ : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ₁ φ₁ η₁}
    {m₂ : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ₂ φ₂ η₂} (h : BookMeans C S m₁ m₂) :
    (m₁.fibers.map fun f => (f.id, f.exit)) = (m₂.fibers.map fun f => (f.id, f.exit)) :=
  ListRel.map h.1 fun a b hab => by rw [fiberMeans_id hab, fiberMeans_exit hab]

/-- The observation of a related pair is one observation: `obs` reads exits and stores
only, and the book compares both. -/
theorem bookMeans_obs {m₁ : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ₁ φ₁ η₁}
    {m₂ : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ₂ φ₂ η₂} (h : BookMeans C S m₁ m₂) :
    obs m₁ = obs m₂ := by
  unfold obs
  rw [bookMeans_exits h, h.state]

/-- The control lists of the finite battery are equal whenever the book holds. -/
theorem bookMeans_controls {m₁ : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ₁ φ₁ η₁}
    {m₂ : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ₂ φ₂ η₂} (h : BookMeans C S m₁ m₂) :
    m₁.fibers.map controlOf = m₂.fibers.map controlOf :=
  ListRel.map h.1 fun _ _ hab => hab.1

end Observation

end Effect4.Machine
