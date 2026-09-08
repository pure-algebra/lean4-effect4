import Effect4.Laws.Program.Simulation.Walk

/-!
# The book at the native alphabets (P3, step 4b)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The generic book
of `Machine/Book.lean`, instantiated to the frame instance (`interpOf`, `Prim` code, the
five-field frame) and the term instance (`interpR`, `RProgram`, the `ScopeFrame` slots) with
the code relation `CodeMeans root` and the saved-state relation `Means root`. The lemmas
here are the bookkeeping the concrete step obligation repeats: a fiber field by field, a
machine's counters, fibers, races and store, the dispatcher's insertion, the tasks and the
one-iteration result `IterRel`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## The two instances -/

abbrev FRun := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev FMachine := Api.Machine
abbrev FIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev FCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev FInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev FTask := Task EffName EffThunk Val Err Defect FiberId Ann
abbrev RTask := Task EffName EffThunk Val Err Defect FiberId Ann RProgram
abbrev FRace := Race EffName EffThunk Val Err Defect FiberId Ann
abbrev RRace := Race EffName EffThunk Val Err Defect FiberId Ann RProgram

/-- The fiber relation of the book at the native alphabets. -/
def FMeans (root : NativeEff) (f₁ : FRun) (f₂ : RFiber) : Prop :=
  FiberMeans (CodeMeans root) (Means root) f₁ f₂

/-- The machine relation of the book at the native alphabets. -/
def BMeans (root : NativeEff) (m₁ : FMachine) (m₂ : RState) : Prop :=
  BookMeans (CodeMeans root) (Means root) m₁ m₂

/-- The command relation at the native alphabets. -/
abbrev CMeans (root : NativeEff) : FCmd → RCmd → Prop := CmdMeans (CodeMeans root)

/-- One iteration's result on both sides: machines in the book with the invariant, fibers
related, the latch, the outcome and the nested commands the same. -/
structure IterRel (root : NativeEff) (it₁ : FIter) (it₂ : RIter) : Prop where
  ok : MachineOk StoresOk it₁.machine
  machine : BMeans root it₁.machine it₂.machine
  fiber : FMeans root it₁.fiber it₂.fiber
  yielding : it₁.yielding = it₂.yielding
  outcome : it₁.outcome = it₂.outcome
  nested : ListRel (CMeans root) it₁.nested it₂.nested

/-! ## Fibers, field by field -/

section Fiber

variable {root : NativeEff} {f₁ : FRun} {f₂ : RFiber}

theorem FMeans.id (h : FMeans root f₁ f₂) : f₁.id = f₂.id := fiberMeans_id h
theorem FMeans.parked (h : FMeans root f₁ f₂) : f₁.parked = f₂.parked := fiberMeans_parked h
theorem FMeans.context (h : FMeans root f₁ f₂) : f₁.context = f₂.context := fiberMeans_context h
theorem FMeans.running (h : FMeans root f₁ f₂) : f₁.running = f₂.running := h.2.1
theorem FMeans.pending (h : FMeans root f₁ f₂) : f₁.pending = f₂.pending := h.2.2.1
theorem FMeans.finalizing (h : FMeans root f₁ f₂) : f₁.finalizing = f₂.finalizing := h.2.2.2.1
theorem FMeans.exit (h : FMeans root f₁ f₂) : f₁.exit = f₂.exit := h.2.2.2.2.1
theorem FMeans.opCount (h : FMeans root f₁ f₂) : f₁.currentOpCount = f₂.currentOpCount :=
  h.2.2.2.2.2.1
theorem FMeans.maxOps (h : FMeans root f₁ f₂) : f₁.maxOpsBeforeYield = f₂.maxOpsBeforeYield :=
  h.2.2.2.2.2.2.1
theorem FMeans.preventYield (h : FMeans root f₁ f₂) : f₁.preventYield = f₂.preventYield :=
  h.2.2.2.2.2.2.2.1
theorem FMeans.yieldOverride (h : FMeans root f₁ f₂) : f₁.yieldOverride = f₂.yieldOverride :=
  h.2.2.2.2.2.2.2.2.1
theorem FMeans.observers (h : FMeans root f₁ f₂) : f₁.observers = f₂.observers :=
  h.2.2.2.2.2.2.2.2.2.1
theorem FMeans.children (h : FMeans root f₁ f₂) : f₁.children = f₂.children :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem FMeans.dispatcher (h : FMeans root f₁ f₂) :
    DispatcherMeans (CodeMeans root) f₁.dispatcher f₂.dispatcher := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem FMeans.means (h : FMeans root f₁ f₂) : Means root f₁.frame f₂.frame :=
  h.2.2.2.2.2.2.2.2.2.2.2.2

theorem FMeans.interruptible (h : FMeans root f₁ f₂) :
    f₁.frame.interruptible = f₂.frame.interruptible := h.means.1
theorem FMeans.interruptedCause (h : FMeans root f₁ f₂) :
    f₁.frame.interruptedCause = f₂.frame.interruptedCause := h.means.2.1
theorem FMeans.deferred (h : FMeans root f₁ f₂) :
    f₁.frame.deferredInterrupt = f₂.frame.deferredInterrupt := h.means.2.2.1
theorem FMeans.current (h : FMeans root f₁ f₂) :
    CodeMeans root f₁.frame.current f₂.frame.current := h.means.2.2.2.1
theorem FMeans.stack (h : FMeans root f₁ f₂) : StackMeans root f₁.frame.stack f₂.frame.stack :=
  h.means.2.2.2.2.1
theorem FMeans.maskInv (h : FMeans root f₁ f₂) : MaskInv f₂.frame.interruptible f₂.frame.stack :=
  h.means.2.2.2.2.2

/-- The relation from its fields. -/
theorem FMeans.mk' (hid : f₁.id = f₂.id) (hpk : f₁.parked = f₂.parked)
    (hctx : f₁.context = f₂.context) (hrun : f₁.running = f₂.running)
    (hpend : f₁.pending = f₂.pending) (hfin : f₁.finalizing = f₂.finalizing)
    (hex : f₁.exit = f₂.exit) (hoc : f₁.currentOpCount = f₂.currentOpCount)
    (hmo : f₁.maxOpsBeforeYield = f₂.maxOpsBeforeYield) (hpy : f₁.preventYield = f₂.preventYield)
    (hyo : f₁.yieldOverride = f₂.yieldOverride) (hobs : f₁.observers = f₂.observers)
    (hch : f₁.children = f₂.children)
    (hdisp : DispatcherMeans (CodeMeans root) f₁.dispatcher f₂.dispatcher)
    (hS : Means root f₁.frame f₂.frame) : FMeans root f₁ f₂ := by
  refine ⟨?_, hrun, hpend, hfin, hex, hoc, hmo, hpy, hyo, hobs, hch, hdisp, hS⟩
  show FiberControl.mk f₁.id f₁.parked (if f₁.exit.isSome then none else some f₁.frame.interruptible)
      f₁.frame.interruptedCause f₁.frame.deferredInterrupt f₁.context =
    FiberControl.mk f₂.id f₂.parked (if f₂.exit.isSome then none else some f₂.frame.interruptible)
      f₂.frame.interruptedCause f₂.frame.deferredInterrupt f₂.context
  rw [hid, hpk, hctx, hex, hS.1, hS.2.1, hS.2.2.1]

theorem FMeans.withFrame (h : FMeans root f₁ f₂) {fr₁ : FFiber} {fr₂ : RSaved}
    (hS : Means root fr₁ fr₂) : FMeans root { f₁ with frame := fr₁ } { f₂ with frame := fr₂ } :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher hS

theorem FMeans.answer (h : FMeans root f₁ f₂) {c₁ : NCode} {c₂ : RProgram}
    (hc : CodeMeans root c₁ c₂) :
    FMeans root { f₁ with frame := { f₁.frame with current := c₁ } }
      { f₂ with frame := { f₂.frame with current := c₂ } } :=
  h.withFrame (means_answerWith h.means hc)

theorem FMeans.park (h : FMeans root f₁ f₂) (p : Pending EffName Val Err Defect FiberId Ann) :
    FMeans root (f₁.park p) (f₂.park p) :=
  FMeans.mk' h.id rfl h.context h.running (by show f₁.pending ++ [p] = f₂.pending ++ [p]; rw [h.pending])
    h.finalizing h.exit h.opCount h.maxOps h.preventYield h.yieldOverride h.observers h.children
    h.dispatcher h.means

theorem FMeans.withContext (h : FMeans root f₁ f₂) (ctx : Ctx) (maxOps : Nat) (prevent : Bool) :
    FMeans root { f₁ with context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent }
      { f₂ with context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent } :=
  FMeans.mk' h.id h.parked rfl h.running h.pending h.finalizing h.exit h.opCount rfl rfl
    h.yieldOverride h.observers h.children h.dispatcher h.means

theorem FMeans.withObservers (h : FMeans root f₁ f₂) (obs : List Observer) :
    FMeans root { f₁ with observers := obs } { f₂ with observers := obs } :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride rfl h.children h.dispatcher h.means

theorem FMeans.withChildren (h : FMeans root f₁ f₂) (ch : List FiberId) :
    FMeans root { f₁ with children := ch } { f₂ with children := ch } :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers rfl h.dispatcher h.means

theorem FMeans.withRunning (h : FMeans root f₁ f₂) (b : Bool) :
    FMeans root { f₁ with running := b } { f₂ with running := b } :=
  FMeans.mk' h.id h.parked h.context rfl h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher h.means

theorem FMeans.started (h : FMeans root f₁ f₂) :
    FMeans root { f₁ with running := true, currentOpCount := 0, parked := .notParked }
      { f₂ with running := true, currentOpCount := 0, parked := .notParked } :=
  FMeans.mk' h.id rfl h.context rfl h.pending h.finalizing h.exit rfl h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher h.means

theorem FMeans.unparked (h : FMeans root f₁ f₂) :
    FMeans root { f₁ with parked := .notParked, pending := [] }
      { f₂ with parked := .notParked, pending := [] } :=
  FMeans.mk' h.id rfl h.context h.running rfl h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher h.means

theorem FMeans.withPending (h : FMeans root f₁ f₂)
    (l : List (Pending EffName Val Err Defect FiberId Ann)) :
    FMeans root { f₁ with pending := l } { f₂ with pending := l } :=
  FMeans.mk' h.id h.parked h.context h.running rfl h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher h.means

theorem FMeans.withYield (h : FMeans root f₁ f₂) (v : Option Bool) :
    FMeans root { f₁ with yieldOverride := v } { f₂ with yieldOverride := v } :=
  fiberMeans_yield h v

theorem FMeans.counted (h : FMeans root f₁ f₂) :
    FMeans root (Effect4.Machine.countOp f₁) (Effect4.Machine.countOp f₂) :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit
    (by show f₁.currentOpCount + 1 = f₂.currentOpCount + 1; rw [h.opCount]) h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher h.means

theorem FMeans.verdict (h : FMeans root f₁ f₂) :
    Effect4.Machine.yieldVerdict f₁ = Effect4.Machine.yieldVerdict f₂ := by
  unfold Effect4.Machine.yieldVerdict
  rw [h.yieldOverride, h.opCount, h.maxOps]

/-- The pairwise relation through two maps into two carriers. -/
theorem ListRel.map_rel {α β γ₁ γ₂ : Type} {R : α → β → Prop} {P : γ₁ → γ₂ → Prop}
    {g₁ : α → γ₁} {g₂ : β → γ₂} (hg : ∀ a b, R a b → P (g₁ a) (g₂ b)) :
    ∀ {l₁ : List α} {l₂ : List β}, ListRel R l₁ l₂ → ListRel P (l₁.map g₁) (l₂.map g₂)
  | _, _, .nil => ListRel.nil
  | _, _, .cons hd tl => ListRel.cons (hg _ _ hd) (ListRel.map_rel hg tl)

/-! ### Tasks and the dispatcher -/

theorem taskMeans_start (child : FiberId) :
    TaskMeans (CodeMeans root) (Task.start child : FTask) (Task.start child : RTask) := rfl

theorem taskMeans_resume (id : FiberId) (token : Nat) {c₁ : NCode} {c₂ : RProgram}
    (hc : CodeMeans root c₁ c₂) :
    TaskMeans (CodeMeans root) (Task.resume id token c₁ : FTask) (Task.resume id token c₂ : RTask) :=
  ⟨rfl, rfl, hc⟩

theorem listRel_insert (priority : Nat) {t₁ : FTask} {t₂ : RTask}
    (ht : TaskMeans (CodeMeans root) t₁ t₂) :
    ∀ {l₁ : List (Bucket EffName EffThunk Val Err Defect FiberId Ann)}
      {l₂ : List (Bucket EffName EffThunk Val Err Defect FiberId Ann RProgram)},
      ListRel (BucketMeans (CodeMeans root)) l₁ l₂ →
      ListRel (BucketMeans (CodeMeans root)) (Dispatcher.insert priority t₁ l₁)
        (Dispatcher.insert priority t₂ l₂) := by
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

theorem dispatcherMeans_enqueue {d₁ : Dispatcher EffName EffThunk Val Err Defect FiberId Ann}
    {d₂ : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram}
    (hd : DispatcherMeans (CodeMeans root) d₁ d₂) (priority : Nat) {t₁ : FTask} {t₂ : RTask}
    (ht : TaskMeans (CodeMeans root) t₁ t₂) :
    DispatcherMeans (CodeMeans root) (d₁.enqueue priority t₁) (d₂.enqueue priority t₂) :=
  ⟨listRel_insert priority ht hd.1, rfl⟩

theorem FMeans.enqueue (h : FMeans root f₁ f₂) (priority : Nat) {t₁ : FTask} {t₂ : RTask}
    (ht : TaskMeans (CodeMeans root) t₁ t₂) :
    FMeans root { f₁ with dispatcher := f₁.dispatcher.enqueue priority t₁ }
      { f₂ with dispatcher := f₂.dispatcher.enqueue priority t₂ } :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children (dispatcherMeans_enqueue h.dispatcher priority ht)
    h.means

/-- A fresh fiber over related programs. -/
theorem fmeans_make (root : NativeEff) (id : FiberId) {c₁ : NCode} {c₂ : RProgram}
    (hc : CodeMeans root c₁ c₂) (flag : Bool) (budget : Nat × Bool) (ctx : Ctx) :
    FMeans root (RunFiber.make id c₁ flag budget ctx) (RunFiber.make id c₂ flag budget ctx) :=
  FMeans.mk' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ⟨ListRel.nil, rfl⟩
    (means_start root hc flag)

end Fiber

/-! ## Machines -/

section Machine

variable {root : NativeEff} {m₁ : FMachine} {m₂ : RState}

theorem BMeans.fibers (h : BMeans root m₁ m₂) : ListRel (FMeans root) m₁.fibers m₂.fibers := h.1
theorem BMeans.races (h : BMeans root m₁ m₂) :
    ListRel (RaceMeans (CodeMeans root)) m₁.races m₂.races := h.2.1
theorem BMeans.nextId (h : BMeans root m₁ m₂) : m₁.nextId = m₂.nextId := h.2.2.1
theorem BMeans.nextToken (h : BMeans root m₁ m₂) : m₁.nextToken = m₂.nextToken := h.2.2.2.1
theorem BMeans.nextRace (h : BMeans root m₁ m₂) : m₁.nextRace = m₂.nextRace := h.2.2.2.2.1
theorem BMeans.middleware (h : BMeans root m₁ m₂) :
    m₁.middlewareInstalled = m₂.middlewareInstalled := h.2.2.2.2.2.1
theorem BMeans.armed (h : BMeans root m₁ m₂) : m₁.armed = m₂.armed := h.2.2.2.2.2.2.1
theorem BMeans.state (h : BMeans root m₁ m₂) : m₁.state = m₂.state := h.2.2.2.2.2.2.2.1
theorem BMeans.stuck (h : BMeans root m₁ m₂) : m₁.stuck = m₂.stuck := h.2.2.2.2.2.2.2.2
theorem BMeans.completedExits (h : BMeans root m₁ m₂) : m₁.completedExits = m₂.completedExits :=
  book_completedExits h

theorem BMeans.mk' (hf : ListRel (FMeans root) m₁.fibers m₂.fibers)
    (hr : ListRel (RaceMeans (CodeMeans root)) m₁.races m₂.races) (hid : m₁.nextId = m₂.nextId)
    (htok : m₁.nextToken = m₂.nextToken) (hrace : m₁.nextRace = m₂.nextRace)
    (hmid : m₁.middlewareInstalled = m₂.middlewareInstalled) (harm : m₁.armed = m₂.armed)
    (hst : m₁.state = m₂.state) (hstuck : m₁.stuck = m₂.stuck) : BMeans root m₁ m₂ :=
  ⟨hf, hr, hid, htok, hrace, hmid, harm, hst, hstuck⟩

theorem BMeans.update (h : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber} (hf : FMeans root f₁ f₂) :
    BMeans root (m₁.update f₁) (m₂.update f₂) := book_update h hf

theorem BMeans.modify (h : BMeans root m₁ m₂) (id : FiberId) {k₁ : FRun → FRun} {k₂ : RFiber → RFiber}
    (hk : ∀ f₁ f₂, FMeans root f₁ f₂ → FMeans root (k₁ f₁) (k₂ f₂)) :
    BMeans root (m₁.modify id k₁) (m₂.modify id k₂) := book_modify h id hk

theorem BMeans.emit (h : BMeans root m₁ m₂)
    (e₁ : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (e₂ : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    BMeans root (m₁.emit e₁) (m₂.emit e₂) := h

theorem BMeans.halt (h : BMeans root m₁ m₂) (why : Stuck) : BMeans root (m₁.halt why) (m₂.halt why) :=
  book_halt h why

theorem BMeans.arm (h : BMeans root m₁ m₂) (owner : FiberId) :
    BMeans root (m₁.arm owner) (m₂.arm owner) := book_arm h owner

theorem BMeans.stateOf (h : BMeans root m₁ m₂) (s : Stores) :
    BMeans root { m₁ with state := s } { m₂ with state := s } := book_stateOf h s

theorem BMeans.middlewareOn (h : BMeans root m₁ m₂) :
    BMeans root { m₁ with middlewareInstalled := true } { m₂ with middlewareInstalled := true } :=
  book_middleware h

theorem BMeans.withNextToken (h : BMeans root m₁ m₂) (n : Nat) :
    BMeans root { m₁ with nextToken := n } { m₂ with nextToken := n } :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

theorem BMeans.withStateToken (h : BMeans root m₁ m₂) (s : Stores) (n : Nat) :
    BMeans root { m₁ with state := s, nextToken := n } { m₂ with state := s, nextToken := n } :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, rfl,
    h.2.2.2.2.2.2.2.2⟩

theorem BMeans.appendFiber (h : BMeans root m₁ m₂) {c₁ : FRun} {c₂ : RFiber}
    (hc : FMeans root c₁ c₂) (n : Nat) :
    BMeans root { m₁ with fibers := m₁.fibers ++ [c₁], nextId := n }
      { m₂ with fibers := m₂.fibers ++ [c₂], nextId := n } :=
  ⟨ListRel.append h.1 (ListRel.cons hc ListRel.nil), h.2.1, rfl, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem BMeans.appendRace (h : BMeans root m₁ m₂) {r₁ : FRace} {r₂ : RRace}
    (hr : RaceMeans (CodeMeans root) r₁ r₂) (nr nt : Nat) :
    BMeans root { m₁ with nextRace := nr, nextToken := nt, races := m₁.races ++ [r₁] }
      { m₂ with nextRace := nr, nextToken := nt, races := m₂.races ++ [r₂] } :=
  ⟨h.1, ListRel.append h.2.1 (ListRel.cons hr ListRel.nil), h.2.2.1, rfl, rfl, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem BMeans.mapFibers (h : BMeans root m₁ m₂) {g₁ : FRun → FRun} {g₂ : RFiber → RFiber}
    (hg : ∀ f₁ f₂, FMeans root f₁ f₂ → FMeans root (g₁ f₁) (g₂ f₂)) :
    BMeans root { m₁ with fibers := m₁.fibers.map g₁ } { m₂ with fibers := m₂.fibers.map g₂ } :=
  ⟨ListRel.map_rel hg h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem BMeans.fiber?_cases (h : BMeans root m₁ m₂) (id : FiberId) :
    (m₁.fiber? id = none ∧ m₂.fiber? id = none) ∨
      ∃ f₁ f₂, m₁.fiber? id = some f₁ ∧ m₂.fiber? id = some f₂ ∧ FMeans root f₁ f₂ :=
  book_fiber?_cases h id

/-! ### Races -/

theorem raceMeans_id {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    r₁.id = r₂.id := h.1
theorem raceMeans_host {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    r₁.host = r₂.host := h.2.1
theorem raceMeans_token {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    r₁.token = r₂.token := h.2.2.1
theorem raceMeans_state {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    r₁.state = r₂.state := h.2.2.2.1
theorem raceMeans_settled {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    r₁.settled = r₂.settled := h.2.2.2.2.1
theorem raceMeans_registering {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    r₁.registering = r₂.registering := h.2.2.2.2.2.1
theorem raceMeans_programs {r₁ : FRace} {r₂ : RRace} (h : RaceMeans (CodeMeans root) r₁ r₂) :
    ListRel (CodeMeans root) r₁.programs r₂.programs := h.2.2.2.2.2.2

theorem raceMeans_mk' {r₁ : FRace} {r₂ : RRace} (hid : r₁.id = r₂.id) (hhost : r₁.host = r₂.host)
    (htok : r₁.token = r₂.token) (hst : r₁.state = r₂.state) (hsettled : r₁.settled = r₂.settled)
    (hreg : r₁.registering = r₂.registering) (hprog : ListRel (CodeMeans root) r₁.programs r₂.programs) :
    RaceMeans (CodeMeans root) r₁ r₂ :=
  ⟨hid, hhost, htok, hst, hsettled, hreg, hprog⟩

theorem listRel_findRace {l₁ : List FRace} {l₂ : List RRace}
    (h : ListRel (RaceMeans (CodeMeans root)) l₁ l₂) (id : Nat) :
    OptRel (RaceMeans (CodeMeans root)) (l₁.find? fun r => r.id = id) (l₂.find? fun r => r.id = id) := by
  induction h with
  | nil => exact True.intro
  | @cons a b l l' hab _ ih =>
    have hid : a.id = b.id := raceMeans_id hab
    by_cases hx : a.id = id
    · have hy : b.id = id := by rw [← hid]; exact hx
      have e₁ : (List.find? (fun r => r.id = id) (a :: l)) = some a := by
        simp only [List.find?_cons_of_pos, decide_eq_true_eq, hx]
      have e₂ : (List.find? (fun r => r.id = id) (b :: l')) = some b := by
        simp only [List.find?_cons_of_pos, decide_eq_true_eq, hy]
      rw [e₁, e₂]; exact hab
    · have hy : ¬ (b.id = id) := by rw [← hid]; exact hx
      have e₁ : (List.find? (fun r => r.id = id) (a :: l)) = List.find? (fun r => r.id = id) l := by
        simp only [List.find?_cons_of_neg, decide_eq_true_eq, hx, not_false_eq_true]
      have e₂ : (List.find? (fun r => r.id = id) (b :: l')) = List.find? (fun r => r.id = id) l' := by
        simp only [List.find?_cons_of_neg, decide_eq_true_eq, hy, not_false_eq_true]
      rw [e₁, e₂]; exact ih

theorem BMeans.race? (h : BMeans root m₁ m₂) (id : Nat) :
    OptRel (RaceMeans (CodeMeans root)) (m₁.race? id) (m₂.race? id) :=
  listRel_findRace h.2.1 id

theorem BMeans.race?_cases (h : BMeans root m₁ m₂) (id : Nat) :
    (m₁.race? id = none ∧ m₂.race? id = none) ∨
      ∃ r₁ r₂, m₁.race? id = some r₁ ∧ m₂.race? id = some r₂ ∧ RaceMeans (CodeMeans root) r₁ r₂ := by
  have hr := h.race? id
  cases h₁ : m₁.race? id with
  | none =>
    cases h₂ : m₂.race? id with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some g => rw [h₁, h₂] at hr; exact absurd hr not_false
  | some f =>
    cases h₂ : m₂.race? id with
    | none => rw [h₁, h₂] at hr; exact absurd hr not_false
    | some g => rw [h₁, h₂] at hr; exact Or.inr ⟨f, g, rfl, rfl, hr⟩

theorem listRel_updateRace {l₁ : List FRace} {l₂ : List RRace}
    (h : ListRel (RaceMeans (CodeMeans root)) l₁ l₂) {r₁ : FRace} {r₂ : RRace}
    (hr : RaceMeans (CodeMeans root) r₁ r₂) :
    ListRel (RaceMeans (CodeMeans root)) (l₁.map fun s => if s.id = r₁.id then r₁ else s)
      (l₂.map fun s => if s.id = r₂.id then r₂ else s) := by
  induction h with
  | nil => exact ListRel.nil
  | @cons a b l l' hab _ ih =>
    refine ListRel.cons ?_ ih
    show RaceMeans _ (if a.id = r₁.id then r₁ else a) (if b.id = r₂.id then r₂ else b)
    by_cases hx : a.id = r₁.id
    · have hy : b.id = r₂.id := by rw [← raceMeans_id hab, ← raceMeans_id hr]; exact hx
      rw [if_pos hx, if_pos hy]; exact hr
    · have hy : ¬ (b.id = r₂.id) := by rw [← raceMeans_id hab, ← raceMeans_id hr]; exact hx
      rw [if_neg hx, if_neg hy]; exact hab

theorem BMeans.updateRace (h : BMeans root m₁ m₂) {r₁ : FRace} {r₂ : RRace}
    (hr : RaceMeans (CodeMeans root) r₁ r₂) : BMeans root (m₁.updateRace r₁) (m₂.updateRace r₂) :=
  ⟨h.1, listRel_updateRace h.2.1 hr, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end Machine

/-! ## The invariant, at the shapes the arms produce -/

theorem pendingOk_make (id : FiberId) (c : NCode) (flag : Bool) (budget : Nat × Bool) (ctx : Ctx) :
    PendingOk (RunFiber.make id c flag budget ctx : FRun) :=
  fun _ h => by simp [RunFiber.make] at h

theorem pendingOk_park {f : FRun} (hf : PendingOk f) (p : Pending EffName Val Err Defect FiberId Ann)
    (hp : ∀ name, p.resumeWith ≠ Resume.continueWith name) : PendingOk (f.park p) := by
  intro q hq
  simp only [RunFiber.park, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hf q hq
  · exact hp

theorem pendingOk_of_fields {f g : FRun} (hf : PendingOk f) (h : g.pending = f.pending) : PendingOk g := by
  intro p hp; rw [h] at hp; exact hf p hp

theorem machineOk_appendFiber {m : FMachine} (hok : MachineOk StoresOk m) {c : FRun} (hc : PendingOk c)
    (n : Nat) : MachineOk StoresOk { m with fibers := m.fibers ++ [c], nextId := n } := by
  refine ⟨hok.1, fun g hg => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hok.2 g hg
  · exact hc

theorem machineOk_withNextToken {m : FMachine} (hok : MachineOk StoresOk m) (n : Nat) :
    MachineOk StoresOk { m with nextToken := n } := hok

theorem machineOk_withStateToken {m : FMachine} (hok : MachineOk StoresOk m) {s : Stores}
    (hs : StoresOk s) (n : Nat) : MachineOk StoresOk { m with state := s, nextToken := n } :=
  ⟨hs, hok.2⟩

theorem machineOk_appendRace {m : FMachine} (hok : MachineOk StoresOk m) (r : FRace) (nr nt : Nat) :
    MachineOk StoresOk { m with nextRace := nr, nextToken := nt, races := m.races ++ [r] } := hok

theorem machineOk_mapFibers {m : FMachine} (hok : MachineOk StoresOk m) {g : FRun → FRun}
    (hg : ∀ f, PendingOk f → PendingOk (g f)) : MachineOk StoresOk { m with fibers := m.fibers.map g } := by
  refine ⟨hok.1, fun f hf => ?_⟩
  obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
  exact hg f' (hok.2 f' hf')

end Effect4.Program.Sched
