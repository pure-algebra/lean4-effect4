import Test.Dogfood.Proofs.HostTimeoutSlots

/-!
# Answer-body assertions for Timeout's native continuations

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the command assertion over `Run.Frame.HistoryOf`.
Source positions use the complete concrete lexical assertion.
Saved frames relate the value they receive to the value the remaining stack expects.
The predicates inspect existing code and names; they introduce no program representation.
The transport proof must discharge every actual callback and administrative wrapper.
These assertions alone establish neither reachability nor progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Proofs.HostTimeoutFlow
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots

abbrev View := List (FiberId × ExitV)
def interpreter (view : View) :=
  interpAt HostTimeoutSource.program view Test.Dogfood.Scenario.Timeout.fetch.table

mutual
/-- A native code position expects one successful value class. -/
inductive CodeAt (B : List Val) : Kind → NCode → Prop
  | source (point : Point) (slots : EnvAt B point.path point.env) :
      CodeAt B (kindAt point.path) (resolve HostTimeoutSource.program point)
  | head {kind : Kind} {code : NCode} (good : HeadAt B kind code) : CodeAt B kind code

/-- The actual primitive head exposes its typed body and callbacks. -/
inductive HeadAt (B : List Val) : Kind → NCode → Prop
  | success {kind : Kind} {value : Val} (good : ValueAt B kind value) :
      HeadAt B kind (.success value)
  | failure (kind : Kind) (cause : CauseV) : HeadAt B kind (.failure cause)
  | sync (kind : Kind) (thunk : EffThunk)
      (answer : ∀ view state next value,
        (interpreter view).syncState thunk state = some (next, value) → ValueAt B kind value)
      (fallback : ∀ view, ValueAt B kind ((interpreter view).syncValue thunk)) :
      HeadAt B kind (.sync thunk)
  | suspend (kind : Kind) (thunk : EffThunk)
      (body : ∀ view, CodeAt B kind ((interpreter view).suspendBody thunk)) :
      HeadAt B kind (.suspend thunk)
  | action (kind : Kind) (thunk : EffThunk)
      (operation : View → WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx)
      (action : ∀ view, (interpreter view).withFiberOf thunk = some (operation view))
      (good : ∀ view, ActionAt B kind (operation view)) : HeadAt B kind (.withFiber thunk)
  | onSuccess (input output : Kind) (body : NCode) (name : EffName)
      (first : CodeAt B input body)
      (next : ∀ view value, ValueAt B input value →
        CodeAt B output ((interpreter view).contA name value)) :
      HeadAt B output (.onSuccess body name)
  | constant (output : Kind) (body next : NCode)
      (first : CodeAt B .unit body) (saved : CodeAt B output next) :
      HeadAt B output (.onSuccessConst body next)
  | onFailure (kind : Kind) (body : NCode) (name : EffName)
      (first : CodeAt B kind body)
      (caught : ∀ view cause, CodeAt B kind ((interpreter view).contE name cause)) :
      HeadAt B kind (.onFailure body name)
  | onExit (kind : Kind) (body : NCode) (name : EffName) (flag : Bool)
      (first : CodeAt B kind body)
      (cleanup : ∀ view exit program, ExitAt B kind exit →
        (interpreter view).finalizerProgram name exit = some program → CodeAt B .unit program) :
      HeadAt B kind (.onExit body name flag)
  | loop (name : EffName) (cursor : Val) (good : CursorAt B cursor)
      (enter : ∀ view next, CursorAt B next → LoopAt B ((interpreter view).loopEnter name next))
      (resume : ∀ view previous answer, CursorAt B previous → ValueAt B .result answer →
        LoopAt B ((interpreter view).loopResume name previous answer)) :
      HeadAt B .result (.whileLoop name cursor)
  | yieldNow (priority : Nat) : HeadAt B .unit (.yieldNowWith priority)
  | external (op : NativeOp) (request : Val) (path : List Nat) :
      HeadAt B .body (.async (.external op request path) false none)
  | sleep (millis : ClockMillis) : HeadAt B .unit
      (.async (.store (.registerSleep millis)) true (some (.store .cancelSleep)))

/-- Loop callbacks retain the cursor's result and the exact source body. -/
inductive LoopAt (B : List Val) : LoopNext Val NCode → Prop
  | enter (cursor : Val) (body : NCode) (good : CursorAt B cursor)
      (bodyGood : CodeAt B .result body) : LoopAt B (.continue cursor body)
  | finish (code : NCode) (good : CodeAt B .result code) : LoopAt B (.finish code)

/-- The timeout's native fiber actions expose only body races and administrative cleanup. -/
inductive ActionAt (B : List Val) : Kind →
    WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx → Prop
  | race (programs : List NCode) (site : Option (List Nat))
      (entrants : ∀ program ∈ programs, CodeAt B .body program) :
      ActionAt B .body (.raceAllFirst programs site)
  | mask (kind : Kind) (body : NCode) (flag : Bool) (good : CodeAt B kind body) :
      ActionAt B kind (.setInterruptible body flag)
  | cancelRace (race : Nat) : ActionAt B .unit (.cancelRace race)
  | dropObservers (token : Nat) : ActionAt B .unit (.dropObservers token)
end

/-- A saved frame relates its incoming success to its continuation's success class. -/
inductive SavedAt (B : List Val) : Kind → Kind → NCode → Prop
  | success (input output : Kind) (body : NCode) (name : EffName)
      (next : ∀ view value, ValueAt B input value →
        CodeAt B output ((interpreter view).contA name value)) :
      SavedAt B input output (.onSuccess body name)
  | constant (output : Kind) (body next : NCode) (saved : CodeAt B output next) :
      SavedAt B .unit output (.onSuccessConst body next)
  | failure (kind : Kind) (body : NCode) (name : EffName)
      (caught : ∀ view cause, CodeAt B kind ((interpreter view).contE name cause)) :
      SavedAt B kind kind (.onFailure body name)
  | exit (kind : Kind) (body : NCode) (name : EffName) (flag : Bool)
      (cleanup : ∀ view exit program, ExitAt B kind exit →
        (interpreter view).finalizerProgram name exit = some program → CodeAt B .unit program) :
      SavedAt B kind kind (.onExit body name flag)
  | mask (kind : Kind) (flag : Bool) : SavedAt B kind kind (.setInterruptible flag)
  | loop (name : EffName) (cursor : Val) (good : CursorAt B cursor)
      (resume : ∀ view previous answer, CursorAt B previous → ValueAt B .result answer →
        LoopAt B ((interpreter view).loopResume name previous answer)) :
      SavedAt B .result .result (.whileLoop name cursor)
  | cancel (kind : Kind) (name : EffName)
      (cleanup : ∀ view cause, CodeAt B kind ((interpreter view).cancelThenFail name cause)) :
      SavedAt B kind kind (.asyncFinalizer name)

/-- Saved continuations form an ordered chain of successful value classes. -/
inductive StackAt (B : List Val) : Kind → Kind → List NCode → Prop
  | nil (kind : Kind) : StackAt B kind kind []
  | cons {input middle output : Kind} {frame : NCode} {rest : List NCode}
      (head : SavedAt B input middle frame) (tail : StackAt B middle output rest) :
      StackAt B input output (frame :: rest)

/-- A running native frame retains a path from its current value class to a body answer. -/
def FrameAt (B : List Val) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∃ kind, CodeAt B kind frame.current ∧ StackAt B kind .body frame.stack

/-- No continuation remains between a successful root and its body assertion. -/
theorem empty_stack_body {B : List Val} {kind : Kind} (stack : StackAt B kind .body []) :
    kind = .body := by cases stack; rfl

/-- A directly typed success with no saved continuation is an applied body. -/
theorem successful_body {B : List Val} {kind : Kind} {value : Val}
    (good : ValueAt B kind value) (stack : StackAt B kind .body []) : value ∈ B := by
  rw [empty_stack_body stack] at good
  cases good with
  | body member => exact member

end Test.Dogfood.Proofs.HostTimeoutFlow
