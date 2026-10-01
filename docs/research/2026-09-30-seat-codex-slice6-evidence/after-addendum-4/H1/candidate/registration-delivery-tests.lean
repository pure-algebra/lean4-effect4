/-- The empty stack is the identity on its input/output type. -/
theorem stackReply_empty_declared (root : ProgramSource) (w : W) (fiber : RFiber)
    (replyTy : EffTy) (empty : fiber.frame.stack = []) (reply : StackReply root w fiber replyTy) :
    w.Γ fiber.id = some replyTy := by
  obtain ⟨final, declared, stack, _⟩ := reply
  rw [empty] at stack
  cases stack
  exact declared

def directRegistration : RProgram := .vis (.inr (.raceRegister 0)) Effects.Program.pure
def registrationFiber : RFiber :=
  RunFiber.make Api.root directRegistration true (stores.budgetOf emptyCtx) emptyCtx

def registeredRace (buffered : Bool) : Effect4.Program.Typed.RRace :=
  { id := 0, host := Api.root, token := 0
    state := { Supervision.RaceAllState.initial [] with
      accepted := if buffered then some (.success (.nat 42)) else none }
    settled := buffered, programs := [], registering := true }

def registrationMachine (buffered : Bool) : RState :=
  { m0 with fibers := [registrationFiber], races := [registeredRace buffered],
    nextToken := 1, nextRace := 1 }

def registrationWorld (rootTy : EffTy) : W :=
  { initialWorld rootTy with Θ := fun id token =>
      if id = Api.root ∧ token = 0 then some (EffTy.pure .nat) else none }

/-- Both immediate buffered settlement and the no-answer park reject this same mismatch. -/
theorem registration_mismatch_rejected (buffered : Bool) :
    ¬ RegistrationState (program : ProgramSource) (registrationWorld ty)
      (registrationMachine buffered) := by
  intro registration
  obtain ⟨race, resultTy, located, _, token, stack⟩ :=
    registration registrationFiber (List.mem_singleton_self _) 0 rfl
  have located' : (registrationMachine buffered).race? 0 = some (registeredRace buffered) := rfl
  rw [located'] at located
  cases located
  have token' : (registrationWorld ty).Θ Api.root 0 = some (EffTy.pure .nat) := rfl
  rw [token'] at token
  cases token
  have declared := stackReply_empty_declared (program : ProgramSource) (registrationWorld ty)
    registrationFiber (EffTy.pure .nat) rfl stack
  change some ty = some (EffTy.pure .nat) at declared
  cases declared

theorem registration_typed_state_rejected (buffered : Bool) :
    ¬ TypedState (program : ProgramSource) ty (registrationWorld ty)
      (registrationMachine buffered) := by
  intro typed
  exact registration_mismatch_rejected buffered typed.2.2.2.2.2

/-- A matching root/token pair admits either buffering state under this exact new clause. -/
theorem registration_matching_green (buffered : Bool) :
    RegistrationState (program : ProgramSource) (registrationWorld (EffTy.pure .nat))
      (registrationMachine buffered) := by
  intro fiber hf raceId marker
  rw [List.mem_singleton] at hf
  subst fiber
  change some 0 = some raceId at marker
  cases marker
  refine ⟨registeredRace buffered, EffTy.pure .nat, rfl, rfl, rfl,
    EffTy.pure .nat, rfl, .nil _, ?_⟩
  exact ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

def natProgram : NativeEff := .succeed (.lit (.nat 0))
def natWorld : W := initialWorld (EffTy.pure .nat)
def natFiber : RFiber :=
  RunFiber.make Api.root (.pure (.success (.nat 0))) true (stores.budgetOf emptyCtx) emptyCtx
def natMachine : RState := { loadR natProgram 20 20 with fibers := [natFiber] }

/-- Authority on a nat-typed active host does not authorize a unit-producing command. -/
theorem afterInterrupt_nat_stack_rejected :
    ¬ CommandDeliveryOk (natProgram : ProgramSource) natWorld natMachine
      (.afterInterrupt Api.root false (.awaitAll [])) := by
  intro delivery
  obtain ⟨replyTy, ⟨answer, error, _, reply⟩, stack⟩ := delivery natFiber rfl
  subst replyTy
  have declared := stackReply_empty_declared (natProgram : ProgramSource) natWorld natFiber
    (EffTy.pure .unit) rfl stack
  change some (EffTy.pure .nat) = some (EffTy.pure .unit) at declared
  cases declared

theorem raceCancel_nat_stack_rejected :
    ¬ CommandDeliveryOk (natProgram : ProgramSource) natWorld natMachine
      (.raceCancel 0 Api.root false [] []) := by
  intro delivery
  obtain ⟨answer, error, _, stack⟩ := delivery natFiber rfl
  have declared := stackReply_empty_declared (natProgram : ProgramSource) natWorld natFiber
    (EffTy.pure .unit) rfl stack
  change some (EffTy.pure .nat) = some (EffTy.pure .unit) at declared
  cases declared

theorem closeParAwait_nat_stack_rejected :
    ¬ CommandDeliveryOk (natProgram : ProgramSource) natWorld natMachine
      (.closeParAwait Api.root false []) := by
  intro delivery
  obtain ⟨answer, error, _, _, stack⟩ := delivery natFiber rfl
  have declared := stackReply_empty_declared (natProgram : ProgramSource) natWorld natFiber
    ⟨.unit, error, Env.Requirement.empty⟩ rfl stack
  change some (EffTy.pure .nat) = some (⟨.unit, error, Env.Requirement.empty⟩ : EffTy) at declared
  cases declared

/-- The matching unit stack accepts the empty await-all continuation clause. -/
theorem afterInterrupt_unit_stack_green :
    CommandDeliveryOk (program : ProgramSource) (initialWorld ty) m0
      (.afterInterrupt Api.root false (.awaitAll [])) := by
  intro fiber found
  have member : fiber ∈ m0.fibers := List.mem_of_find?_eq_some found
  change fiber ∈ [_] at member
  rw [List.mem_singleton] at member
  subst fiber
  refine ⟨EffTy.pure .unit, ⟨.never, .never, ?_, rfl⟩, ty, rfl, .nil _, ?_⟩
  · intro id hid; cases hid
  · exact ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

#print axioms registration_mismatch_rejected
#print axioms registration_typed_state_rejected
#print axioms registration_matching_green
#print axioms afterInterrupt_nat_stack_rejected
#print axioms raceCancel_nat_stack_rejected
#print axioms closeParAwait_nat_stack_rejected
#print axioms afterInterrupt_unit_stack_green
