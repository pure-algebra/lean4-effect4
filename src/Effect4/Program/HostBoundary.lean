import Effect4.Program.Profile

/-!
Boundary classifications for the selected small host models. This is a driver view of
existing program/machine data, not stored syntax or a second evaluator. Pending means
that a validated call has no supplied reply at this observation, not that the semantic
relation has no possible transition. The session protocol supplies actual reply validation.
Authority: Test/contracts/foundation-wave2.contract.md, Host protocol.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- Input validation happens before interpreting a supplied host completion. -/
inductive HostInputCheck
  | admitted
  | malformed (reason : String)
  | outsideProfile (reason : String)
deriving DecidableEq, Repr

/-- All four boundary outcomes retain the current host state. Completed failure carries
its resulting state just like completed success. Raw JavaScript objects never occur here. -/
inductive HostBoundaryResult (HostState : Type)
  | completed (completion : Completion Val Err Defect FiberId Ann) (state : HostState)
  | pending (state : HostState)
  | malformed (reason : String) (state : HostState)
  | outsideProfile (reason : String) (state : HostState)
deriving DecidableEq

namespace HostBoundaryResult

def state {HostState : Type} : HostBoundaryResult HostState → HostState
  | .completed _ state | .pending state | .malformed _ state | .outsideProfile _ state => state

/-- Classify a currently supplied result after input validation. `none` with admitted input
is pending even if a semantic transition is possible. This function does not validate an
arbitrary completion; a session must establish its recorded-reply envelope separately. -/
def ofAttempt {HostState : Type} (check : HostInputCheck) (current : HostState)
    (attempt : Option (Completion Val Err Defect FiberId Ann × HostState)) :
    HostBoundaryResult HostState :=
  match check with
  | .malformed reason => .malformed reason current
  | .outsideProfile reason => .outsideProfile reason current
  | .admitted =>
    match attempt with
    | none => .pending current
    | some (completion, state) => .completed completion state

end HostBoundaryResult

namespace Profile.Scalar

/-- Exact row identity, natural shape, then profile domain. A same-name altered row is
not this binding. Out-of-domain input is not a program failure. -/
def checkRequest (row : Row) (request : Val) : HostInputCheck :=
  if row = waitRow then
    match request with
    | .nat n => if n ≤ profile.natBound then .admitted
        else .outsideProfile "nat outside the profile"
    | _ => .malformed "expected a natural request"
  else .malformed "unknown scalar row"

/-- `answered` is the explicit finite observation choice: withholding a reply leaves a
validated call pending. It is not a claim that all possible host replies are deterministic. -/
def poll (row : Row) (request : Val) (state : State) (answered : Bool) :
    HostBoundaryResult State :=
  .ofAttempt (checkRequest row request) state (if answered then step? row request state else none)

end Profile.Scalar

namespace Profile.Resource

/-- Validate exact binding and acquisition. A closed acquired slot is still well-formed:
it completes with the selected misuse defect. An index never acquired is malformed. -/
def checkRequest (row : Row) (request : Val) (state : State) : HostInputCheck :=
  if row = acquireRow then
    if request = .unit then .admitted else .malformed "expected unit acquisition request"
  else if row = useRow ∨ row = releaseRow then
    match request with
    | Value.external index =>
      if index < state.slots.length then .admitted else .malformed "resource was never acquired"
    | _ => .malformed "expected an external resource handle"
  else .malformed "unknown resource row"

def poll (row : Row) (request : Val) (state : State) (answered : Bool) :
    HostBoundaryResult State :=
  .ofAttempt (checkRequest row request state) state (if answered then step? row request state else none)

/-- Every model resource belongs to this run's cleanup ledger. This is an explicit
ownership premise, not a conclusion drawn from matching allocation counts. -/
def OwnsAll (state : State) (owned : List Nat) : Prop :=
  ∀ index, index < state.slots.length → index ∈ owned

/-- Cleanup completed for every entry of the selected ownership ledger. This checks the
resulting slot states, so registering a finalizer alone cannot establish it. -/
def CleanupComplete (state : State) (owned : List Nat) : Prop :=
  ∀ index, index ∈ owned → state.slots[index]? = some false

end Profile.Resource

namespace Profile.Choice

/-- A finite relational host example. The work can charge either one or two units;
the selected completion records which outcome occurred. No choice is implicit in state. -/
def spec : HostSpec Nat Nat where
  Rep := Scalar.Rep
  RelatedState := fun stores _ => stores.externals.allocated = []
  Work := fun _ _ before after => after = before + 1 ∨ after = before + 2
  RowStep := fun row request before completion after =>
    row = Scalar.waitRow ∧ request = .nat 0 ∧
      ((completion = .ofExit (.success (.nat 1)) ∧ after = before + 1) ∨
       (completion = .ofExit (.success (.nat 2)) ∧ after = before + 2))
  observe := fun stores _ => stores.externals.answers = []

end Profile.Choice

end Effect4.Program
