import Effect4.Laws.Machine.Lift
import Effect4.Laws.Machine.Edits

/-!
Concepts: reactive-scheduling R9, store-typing R4 and scope-lifetime-finalization R11.
Question: Atomic stages and Timeout phases need context at actual interrupt lookups.
Consumer: their common ghost command and settlement producer.
Each message retains one shared proof world for machine and queued-command assertions.
The existing message word supplies runtime order and generated commands.
This producer establishes no application phase, reply admission or progress.
-/
set_option autoImplicit false
namespace Effect4.Machine.ContextualMessages
open Effect4 Effect4.Machine
universe u v w z
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable {κ φ η : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable [FiberCore ν β ε δ ι α κ φ]
variable {V : Type w} {Context : Type z}

/-- Primitive message producers read the actual machine, queue and addressed lookup.
The context can retain a detached snapshot whose assertion belongs to `P` or `Q`. -/
structure Local (order : Effect4.Laws.Effects.WorldOrder V)
    (P : Context → V → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (Q : Context → V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop) : Prop where
  observe : ∀ context world m commands target observer, P context world m → Q context world m commands →
    ∃ next, order.le world next ∧ P context next (m.observe target observer) ∧
      Q context next (m.observe target observer) commands
  drop : ∀ context world m commands token, P context world m → Q context world m commands →
    ∃ next, order.le world next ∧ P context next (m.dropToken token) ∧
      Q context next (m.dropToken token) commands
  interrupt : ∀ context world m commands target cause fiber,
    m.fiber? target = some fiber → P context world m → Q context world m commands →
    ∃ next, order.le world next ∧ P context next (m.update (interruptWithCause cause fiber).1) ∧
      Q context next (m.update (interruptWithCause cause fiber).1)
        (commands ++ if (interruptWithCause cause fiber).2 then [.evaluate target] else [])

variable {order : Effect4.Laws.Effects.WorldOrder V}
variable {P : Context → V → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
variable {Q : Context → V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}

/-- One actual message retains the joint world through its generated command suffix. -/
theorem Local.one (facts : Local order P Q) (context : Context) (world : V)
    (message : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (commands : List (Cmd ν σ β ε δ ι α κ)) (held : P context world m) (queued : Q context world m commands) :
    ∃ next, order.le world next ∧ P context next (applyFiberEdit message m).1 ∧
      Q context next (applyFiberEdit message m).1 (commands ++ (applyFiberEdit message m).2) := by
  cases message with
  | observe target observer =>
    simpa only [applyFiberEdit, List.append_nil] using facts.observe context world m commands target observer held queued
  | dropToken token =>
    simpa only [applyFiberEdit, List.append_nil] using facts.drop context world m commands token held queued
  | interrupt target cause =>
    cases found : m.fiber? target with
    | none =>
      refine ⟨world, order.refl world, ?_, ?_⟩
      · simpa only [applyFiberEdit, found] using held
      · simpa only [applyFiberEdit, found, List.append_nil] using queued
    | some fiber =>
      simpa only [applyFiberEdit, found] using
        facts.interrupt context world m commands target cause fiber found held queued

/-- A contextual message producer may require an immutable admission fact.
Consumer: Timeout excludes typed failures from actual interrupt messages. -/
structure Admitted (Allowed : Context → FiberEdit ε δ ι α → Prop) : Prop where
  one : ∀ context world message m commands, Allowed context message →
    P context world m → Q context world m commands →
    ∃ next, order.le world next ∧ P context next (applyFiberEdit message m).1 ∧
      Q context next (applyFiberEdit message m).1 (commands ++ (applyFiberEdit message m).2)

/-- An admitted word retains the actual lookup state at every message.
The same next world carries both assertions, including accumulated commands. -/
theorem Admitted.fold {Allowed : Context → FiberEdit ε δ ι α → Prop}
    (facts : Admitted (order := order) (P := P) (Q := Q) Allowed)
    (context : Context) (world : V) (messages : List (FiberEdit ε δ ι α))
    (admitted : ∀ message ∈ messages, Allowed context message)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (held : P context world acc.1) (queued : Q context world acc.1 acc.2) :
    let out := messages.foldl (fun result message =>
      let changed := applyFiberEdit message result.1
      (changed.1, result.2 ++ changed.2)) acc
    ∃ next, order.le world next ∧ P context next out.1 ∧ Q context next out.1 out.2 := by
  induction messages generalizing world acc with
  | nil => exact ⟨world, order.refl world, held, queued⟩
  | cons message rest ih =>
    dsimp only [List.foldl_cons]
    obtain ⟨middle, first, kept, tail⟩ :=
      facts.one context world message acc.1 acc.2 (admitted message (List.mem_cons_self)) held queued
    obtain ⟨last, second, result, commands⟩ := ih middle
      (fun item member => admitted item (List.mem_cons_of_mem message member))
      ((applyFiberEdit message acc.1).1, acc.2 ++ (applyFiberEdit message acc.1).2) kept tail
    exact ⟨last, order.trans first second, result, commands⟩

/-- Admitted addressed edits retain the actual installed machine and generated queue. -/
theorem Admitted.apply {Allowed : Context → FiberEdit ε δ ι α → Prop}
    (facts : Admitted (order := order) (P := P) (Q := Q) Allowed)
    (context : Context) (world : V) (messages : List (FiberEdit ε δ ι α))
    (admitted : ∀ message ∈ messages, Allowed context message)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (held : P context world m) (queued : Q context world m []) :
    ∃ next, order.le world next ∧ P context next (applyFiberEdits messages m).1 ∧
      Q context next (applyFiberEdits messages m).1 (applyFiberEdits messages m).2 :=
  facts.fold context world messages admitted (m, []) held queued

/-- Admission is trivial for the original unrestricted message interface. -/
theorem Local.admitted (facts : Local order P Q) :
    Admitted (order := order) (P := P) (Q := Q) (fun _ _ => True) :=
  ⟨fun context world message m commands _ held queued =>
    facts.one context world message m commands held queued⟩

/-- The existing message fold retains the same chosen world for its machine and full queue.
Consumer: actual native settlement, including each successive interrupt lookup. -/
theorem Local.fold (facts : Local order P Q) (context : Context) (world : V)
    (messages : List (FiberEdit ε δ ι α))
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (held : P context world acc.1) (queued : Q context world acc.1 acc.2) :
    let out := messages.foldl (fun result message =>
      let changed := applyFiberEdit message result.1
      (changed.1, result.2 ++ changed.2)) acc
    ∃ next, order.le world next ∧ P context next out.1 ∧ Q context next out.1 out.2 :=
  facts.admitted.fold context world messages (fun _ _ => True.intro) acc held queued

/-- Actual native addressed edits retain their joint machine and generated-command assertions. -/
theorem Local.apply (facts : Local order P Q) (context : Context) (world : V)
    (messages : List (FiberEdit ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (held : P context world m) (queued : Q context world m []) :
    ∃ next, order.le world next ∧ P context next (applyFiberEdits messages m).1 ∧
      Q context next (applyFiberEdits messages m).1 (applyFiberEdits messages m).2 :=
  facts.fold context world messages (m, []) held queued

/-- Settlement composes installation, contextual messages and the actual owner reread.
Consumers: Atomic stages and Timeout phases retain one world through the disposition.
The local outcome producer receives both assertions at that same world. -/
theorem Admitted.settle {Allowed : Context → FiberEdit ε δ ι α → Prop}
    (facts : Admitted (order := order) (P := P) (Q := Q) Allowed) (context : Context) (world : V)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (it : Iter ν σ β ε δ ι α χ St κ φ η)
    (admitted : ∀ message ∈ it.edits, Allowed context message)
    (Post : V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (plain : it.edits = [] →
      ∃ next, order.le world next ∧ Post next (settleOutcome id rest it).1 (settleOutcome id rest it).2)
    (installed : it.edits ≠ [] → P context world (it.machine.update it.fiber))
    (queued : it.edits ≠ [] → Q context world (it.machine.update it.fiber) [])
    (missing : ∀ middle m commands, order.le world middle →
      P context middle m → Q context middle m commands → m.fiber? it.fiber.id = none →
      ∃ next, order.le middle next ∧ Post next (m.halt (.unknownFiber it.fiber.id)) [])
    (outcome : ∀ middle m commands owner, order.le world middle →
      P context middle m → Q context middle m commands → m.fiber? it.fiber.id = some owner →
      let revised := {it with machine := m, fiber := owner, nested := commands ++ it.nested, edits := []}
      ∃ next, order.le middle next ∧
        Post next (settleOutcome id rest revised).1 (settleOutcome id rest revised).2) :
    ∃ next, order.le world next ∧ Post next (settle id rest it).1 (settle id rest it).2 := by
  cases edits : it.edits with
  | nil => simpa only [Machine.settle, edits] using plain edits
  | cons message tail =>
    have nonempty : it.edits ≠ [] := by rw [edits]; intro impossible; cases impossible
    obtain ⟨middle, advanced, held, commands⟩ :=
      facts.apply context world it.edits admitted (it.machine.update it.fiber)
        (installed nonempty) (queued nonempty)
    cases found : (applyFiberEdits it.edits (it.machine.update it.fiber)).1.fiber? it.fiber.id with
    | none =>
      obtain ⟨next, later, post⟩ := missing middle _ _ advanced held commands found
      refine ⟨next, order.trans advanced later, ?_⟩
      simp only [edits] at found post
      simpa only [Machine.settle, edits, found] using post
    | some owner =>
      obtain ⟨next, later, post⟩ := outcome middle _ _ owner advanced held commands found
      refine ⟨next, order.trans advanced later, ?_⟩
      simp only [edits] at found post
      simpa only [Machine.settle, edits, found] using post

end Effect4.Machine.ContextualMessages
