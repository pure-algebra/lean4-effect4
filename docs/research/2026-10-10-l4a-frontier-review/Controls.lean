import Effect4.Laws.Program.Agreement.HostedLoop
import Effect4.Program.Authoring.Module

/-! Controls for proposed claim `rows-loop-frontier`, Q4/Q6b, R6/R12.
Placement and consumers are in PLAN.md. These controls establish no general
source/machine agreement or resumable-state relation. -/
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Test.L4aFrontierReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Program.Agreement Effect4.Program.Authoring

def row : Row := (Row.host "Review.wait" .nat .nat .never "frontier review").row
def rows : RowTable := [row]
def quiet : Effects.Comodel (RowSig rows) Nat := ⟨fun _ _ => none⟩
def root : NativeEff := .succeed (.lit .unit)
def call (n : Nat) : NCode := Prim.async (EffName.external (.external 0) (.nat n) []) false none
def fr (n : Nat) : NFiber := fiberOf (call n) []
def stores1 : Stores := { Stores.empty with nextName := 1 }

def waitingRequest (o : Option (RunEnd Nat)) : Option Val :=
  match o with
  | some (.waits code _ _) => (callOf code).map Prod.snd
  | _ => none

def waitingSupply (o : Option (RunEnd Nat)) : Option Nat :=
  match o with
  | some (.waits _ s _) => some s.nextName
  | _ => none

def waitingHost (o : Option (RunEnd Nat)) : Option Nat :=
  match o with
  | some (.waits _ _ st) => some st
  | _ => none

/-- Reader: reflexivity at a declared data row. -/
example : ReachesC quiet root 0 (fr 1) Stores.empty 0 (fr 1) Stores.empty 0 :=
  ReachesC.refl quiet root (fr 1) Stores.empty 0

/-- Reader: unanswered calls retain all three waiting fields at every positive budget. -/
example (n : Nat) : localRunC quiet root (n + 1) (fr 1) Stores.empty 3 =
    some (.waits (call 1) Stores.empty 3) :=
  localRunC_waits (by rfl) (by rfl) Stores.empty n

/-- Red control: a different request prevents this zero-offset relation. -/
example : ¬ ReachesC quiet root 0 (fr 1) Stores.empty 0 (fr 2) Stores.empty 0 := by
  intro h
  have unequal : (some (Val.nat 1) : Option Val) ≠ some (Val.nat 2) := by decide
  exact unequal (congrArg waitingRequest (h 1))

/-- Red control: the waiting stores are observable. -/
example : ¬ ReachesC quiet root 0 (fr 1) Stores.empty 0 (fr 1) stores1 0 := by
  intro h
  have unequal : (some 0 : Option Nat) ≠ some 1 := by decide
  exact unequal (congrArg waitingSupply (h 1))

/-- Red control: the waiting host state is observable. -/
example : ¬ ReachesC quiet root 0 (fr 1) Stores.empty 0 (fr 1) Stores.empty 1 := by
  intro h
  have unequal : (some 0 : Option Nat) ≠ some 1 := by decide
  exact unequal (congrArg waitingHost (h 1))

#guard dataRow rows 0
#guard callOf (call 1) = some (0, .nat 1)
#guard callOf (Prim.success .unit) = none
#guard (localRunC quiet root 0 (fr 1) Stores.empty 0).isNone
#guard waitingRequest (localRunC quiet root 1 (fr 1) Stores.empty 0) = some (.nat 1)
#guard waitingSupply (localRunC quiet root 1 (fr 1) stores1 0) = some 1
#guard waitingHost (localRunC quiet root 1 (fr 1) Stores.empty 3) = some 3

/-- Limit control: this observation cannot identify a continuation that has not run. -/
example : ReachesC quiet root 0 (fr 1) Stores.empty 0
    (fiberOf (call 1) [Prim.success (.nat 9)]) Stores.empty 0 := by
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

/-- The source call names row zero, before any admission check. -/
def sourceCall : NativeEff := .perform (.external 0) (.lit (.nat 1))
def admittedObservation : RowsObservation Nat :=
  observeRows quiet (denoteRowsB rows 0 sourceCall []) Stores.empty 0
#guard LoopedDataRows rows sourceCall
#guard admittedObservation.stop = .waiting 0 (.nat 1)
#guard admittedObservation.stores = Stores.empty
#guard admittedObservation.host = 0

def emptyQuiet : Effects.Comodel (RowSig []) Nat := ⟨fun _ _ => none⟩
def missingObservation : RowsObservation Nat :=
  observeRows emptyQuiet (denoteRowsB [] 0 sourceCall []) Stores.empty 0

/- Excluded-input control: recognition by callOf does not establish row admission.
The local code waits; source meaning reports its unsupported-row exit. -/
#guard IsCall (call 1)
#guard hostAnswer emptyQuiet (call 1) 0 = none
#guard waitingRequest (localRunC emptyQuiet root 1 (fr 1) Stores.empty 0) = some (.nat 1)
#guard !(dataRow [] 0)
#guard !(LoopedDataRows [] sourceCall)
#guard missingObservation.stop = .finished outsideExit
#guard missingObservation.stores = Stores.empty
#guard missingObservation.host = 0

end Test.L4aFrontierReview
