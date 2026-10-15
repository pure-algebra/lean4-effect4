import Effect4.Laws.Program.AnswerSlots.Stable

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: saved callbacks retain constructor correlations as well as leaf annotations.
Consumers: full finalizer source and registration-body invariants.
The existing stable family carries one supplied predicate on actual code.
These local laws establish no native command history or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.PredicateFamily
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.AnswerSlots

/-- Current code and saved code carry the same supplied invariant. -/
def edge (P : NCode → Prop) (_ : Unit) (_ _ : Unit) : NCode → Prop := P

/-- The existing code constructors expose only their actual immediate children. -/
def Children (P : NCode → Prop) : NCode → Prop
  | .onSuccess body _ | .onFailure body _ | .onSuccessAndFailure body _ _
  | .onExit body _ _ | .exitFrame body => P body
  | .onSuccessConst body next => P body ∧ P next
  | _ => True

/-- The actual interpreter hooks preserve the supplied invariant on existing code. -/
structure Rules (root : NativeEff) (table : RowTable) (P : NCode → Prop) : Prop where
  success : ∀ value, P (.success value)
  failure : ∀ cause, P (.failure cause)
  children : ∀ code, P code → Children P code
  mask : ∀ flag, P (.setInterruptible flag)
  suspend : ∀ view thunk, P (.suspend thunk) ∨ P (.withFiber thunk) → P ((interpAt root view table).suspendBody thunk)
  value : ∀ view frame value provided next pushed, P frame →
    frame.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed) →
      P next ∧ ∀ code ∈ pushed, P code
  cause : ∀ view frame cause provided next pushed, P frame →
    frame.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed) →
      P next ∧ ∀ code ∈ pushed, P code
  loopContinue : ∀ view callback cursor next body, P (.whileLoop callback cursor) →
    (interpAt root view table).loopEnter callback cursor = .continue next body →
      P body ∧ P (.whileLoop callback next)
  loopFinish : ∀ view callback cursor body, P (.whileLoop callback cursor) →
    (interpAt root view table).loopEnter callback cursor = .finish body → P body
  finalizer : ∀ view frame exit next, P frame →
    (match frame with
      | .onExit _ callback _ => ((interpAt root view table).finalizerProgram callback exit).map
          (finalizerCode (interpAt root view table) exit)
      | _ => none) = some next → P next

/-- The stable unit class keeps every value and the supplied actual code invariant. -/
def spec (root : NativeEff) (table : RowTable) (P : NCode → Prop) (rules : Rules root table P) : StableSpec where
  root := root
  table := table
  Kind := Unit
  rootKind := ()
  value _ _ := True
  code _ := P
  success _ value _ := rules.success value
  failure _ cause := rules.failure cause

/-- A list of actual code certificates is the unit-indexed saved path. -/
theorem path (P : NCode → Prop) (frames : List NCode) (owned : ∀ code ∈ frames, P code) :
    Contracts.Path (edge P ()) () () frames := by
  induction frames with
  | nil => exact .nil ()
  | cons frame rest ih => exact .cons (owned frame (.head _)) (ih (fun code member => owned code (.tail _ member)))

/-- Reading the unit saved path recovers every actual frame certificate. -/
theorem path_owned (P : NCode → Prop) {input output : Unit} {frames : List NCode}
    (held : Contracts.Path (edge P ()) input output frames) : ∀ code ∈ frames, P code := by
  induction held with
  | nil kind => intro code member; cases member
  | cons head tail ih =>
    intro code member
    rcases List.mem_cons.mp member with same | rest
    · rw [same]; exact head
    · exact ih code rest

/-- One actual saved-family producer serves every constructor-aware code invariant. -/
theorem family (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view) :
    AnswerFlow.SavedFamily ((spec root table P rules).model view)
      (interpAt root view table).toPrimInterp (edge P) := by
  constructor
  · intros; trivial
  · intros; trivial
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := rules.value view frame value provided next pushed held actual
    cases output
    exact ⟨(), code, path P pushed stack⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := rules.cause view frame cause provided next pushed held actual
    cases output
    exact ⟨(), code, path P pushed stack⟩
  · intro world input output frame held nextWorld future exit next good installed
    cases frame
    case onExit body callback flag => exact rules.finalizer view _ exit next held installed
    all_goals cases installed
  · intros; trivial

/-- One actual current-head producer exposes the supplied invariant's existing child facts. -/
theorem head (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view) (code : NCode) (owned : P code) :
    AnswerFlow.HeadAt ((spec root table P rules).model view)
      (interpAt root view table).toPrimInterp (edge P) () () code := by
  have children := rules.children code owned
  cases code
  case success value => exact .success value trivial
  case failure cause => exact .failure cause trivial
  case sync thunk => exact .sync thunk trivial
  case suspend thunk => exact .suspend thunk (rules.suspend view thunk (.inl owned))
  case withFiber thunk => exact .withFiber thunk (rules.suspend view thunk (.inr owned))
  case yieldableError error => exact .yieldableError error trivial
  case iterator name cursor =>
    refine .iterator name cursor owned ?_
    intro next pushed actual
    obtain ⟨code, slots⟩ := rules.value view _ cursor none next pushed owned actual
    exact ⟨(), code, path P pushed slots⟩
  case whileLoop name cursor =>
    refine .whileLoop name cursor ?_ ?_
    · intro next body actual
      have slots := rules.loopContinue view name cursor next body owned actual
      exact ⟨(), slots.1, .cons slots.2 (.nil ())⟩
    · intro body actual
      exact ⟨(), rules.loopFinish view name cursor body owned actual, .nil ()⟩
  case onSuccess body name => exact .onSuccess () body name children owned
  case onSuccessConst body next => exact .onSuccessConst () body next children.1 owned
  case onFailure body name => exact .onFailure () body name children owned
  case onSuccessAndFailure body success failure => exact .onSuccessAndFailure () body success failure children owned
  case exitFrame body => exact .exitFrame () body children owned
  case onExit body name flag => exact .onExit () body name flag children owned
  case yieldNowWith priority => exact .yieldNowWith priority owned
  case async register signal cancel => exact .async register signal cancel owned
  case setInterruptible flag => exact .setInterruptible flag trivial
  case asyncFinalizer name => exact .asyncFinalizer name trivial

/-- Existing stable consumers use the generic constructor-aware producer. -/
def laws (root : NativeEff) (table : RowTable) (P : NCode → Prop) (rules : Rules root table P) :
    StableLaws (spec root table P rules) where
  Edge := edge P
  family := family root table P rules
  head view kind code held := by cases kind; exact head root table P rules view code held

end Effect4.Program.CodeClosure.PredicateFamily
