import Effect4.Laws.Step.Callback
import Effect4.Laws.Step.Store
import Effect4.Program.Authoring.Rows
import Effect4.Step.Elab.Inputs

/-!
# Callback readers and controls

The readers apply the shared laws to numeric and deferred-handle inputs.
The controls distinguish caller-scope freezing from relocation of a capture's internal fold.
Checker refusals retain wrong capture types and wrong callback result shapes.
These finite evaluations establish neither a whole run nor target or host behavior.
-/

set_option autoImplicit false
namespace Test.Program.StepCallback
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Schema Effect4.Schema.Model

step_context% Captures (outer : .nat)
step_context% CallbackInputs (current : .nat, outer : .nat)

def returnCaptured : Step CallbackInputs.types (.prod .nat .nat) :=
  step_inputs% CallbackInputs => .pair outer current

def caller : Env := { names := ["r", "outer"] }
def callerValues : List Store.Val := [Machine.Val.cell ⟨0⟩, .nat 7]

/-- This capture observes the last slot of its original caller scope. -/
def depthSource : TermSrc := fun env _ => .ok (.var (env.names.length - 1))
def sources : {t : Ty} → Input Captures.types t → TermSrc :=
  input_sources% (Captures) {outer := depthSource}

def increment : Step CallbackInputs.types .nat :=
  step_inputs% CallbackInputs => .add current outer

def numeric : Src NativeOp := Step.callback returnCaptured sources (Ref.modifyWith (var "r"))

def numericTree : Term := .app "pair" (.cons (.var 1) (.cons (.var 2) .nil))
#guard numeric caller [] == .ok (.perform (.refModifyWith numericTree) (.var 0))
#guard evalTerm (callerValues ++ [.nat 3]) numericTree == some (Store.Val.list [.nat 7, .nat 3])

/-- Control: resolving the capture inside the callback changes the returned value. -/
def naive : Src NativeOp := Ref.modifyWith (var "r") fun current =>
  returnCaptured.term (input_sources% (CallbackInputs) {current := current, outer := depthSource})
#guard naive caller [] == .ok (.perform
  (.refModifyWith (.app "pair" (.cons (.var 2) (.cons (.var 2) .nil)))) (.var 0))

/-- A capture with its own item at the original caller's depth plus one. -/
def internalFold : Term := .fold (some .nat)
  (.app "cons" (.cons (.lit (.nat 4)) (.cons (.app "nil" .nil) .nil)))
  (.lit (.nat 0)) (.var 3)
def foldSource : TermSrc := fun _ _ => .ok internalFold

def folded : Src NativeOp := Step.callback returnCaptured
  (input_sources% (Captures) {outer := foldSource}) (Ref.modifyWith (var "r"))
def liftedFold : Term := internalFold.weaken 2
#guard folded caller [] == .ok (.perform
  (.refModifyWith (.app "pair" (.cons liftedFold (.cons (.var 2) .nil)))) (.var 0))
#guard evalTerm (callerValues ++ [.nat 3]) liftedFold == some (.nat 4)
-- Freezing without relocating the fold reads its accumulator instead of its item.
#guard evalTerm (callerValues ++ [.nat 3]) internalFold == some (.nat 0)

/-- A used capture keeps the refusal's original location and reason. -/
def refusing : TermSrc := fun _ path => .error ⟨path, .unbound "missing"⟩
#guard (Step.callback returnCaptured
  (input_sources% (Captures) {outer := refusing}) (Ref.modifyWith (var "r"))) caller [8]
  == .error ⟨[8], .unbound "missing"⟩

/-- Numeric reader: the shared law reads the original capture and the current cell value. -/
example : Reads (returnCaptured.term
    (Step.callbackSources sources caller [] (minted (caller.mint "current"))))
    (caller.push [caller.mint "current"]) [] (callerValues ++ [.nat 3])
    (Store.Val.list [.nat 7, .nat 3]) := by
  have inputs : ∀ {t : Ty} (x : Input Captures.types t),
      Reads (sources x) caller [] callerValues
        ((imageAt Leaves.deferredKeys t).toVal (x.get ((7 : Nat), ()))) := by
    intro t x
    cases x with
    | here => exact ⟨.var 1, rfl, rfl⟩
    | there _ x => nomatch x
  exact Step.callback_term_reads (L := Leaves.deferredKeys) returnCaptured
    (vs := ((7 : Nat), ())) rfl inputs (caller.mint "current") (3 : Nat)
    (reads_minted_last rfl [] "current" (.nat 3)) rfl

/-- Numeric typing reader: a depth-sensitive capture is checked at the original scope. -/
example : TypesEach nativeSignature (returnCaptured.term
    (Step.callbackSources sources caller [] (minted (caller.mint "current"))))
    (caller.push [caller.mint "current"]) [] [.refOf .nat, .nat, .nat] (.prod .nat .nat) := by
  have inputs : ∀ {t : Ty} (x : Input Captures.types t),
      TypesEach nativeSignature (sources x) caller [] [.refOf .nat, .nat] t := by
    intro t x const
    cases x with
    | here => exact ⟨.var 1, rfl, rfl⟩
    | there _ x => nomatch x
  exact Step.callback_term_types nativeSignature rfl returnCaptured rfl inputs
    (caller.mint "current") (types_minted_last rfl [] "current" .nat)
    (Step.facts_of_normal returnCaptured rfl)

def H : Ty := .deferredOf .nat .never
step_context% HandleCaptures (replacement : H)
step_context% HandleInputs (current : H, replacement : H)
def replaceHandle : Step HandleInputs.types (.prod H H) :=
  step_inputs% HandleInputs => .pair current replacement
def handleSources : {t : Ty} → Input HandleCaptures.types t → TermSrc :=
  input_sources% (HandleCaptures) {replacement := depthSource}
def handleValues : List Store.Val := [Machine.Val.cell ⟨0⟩, Machine.Val.promise ⟨1⟩]
def handleProgram : Src NativeOp := Step.callback replaceHandle handleSources (Ref.modifyWith (var "r"))
def handleTree : Term := .app "pair" (.cons (.var 2) (.cons (.var 1) .nil))
#guard handleProgram caller [] == .ok (.perform (.refModifyWith handleTree) (.var 0))
#guard Machine.syncOpStep (.refModify ⟨0⟩ handleTree handleValues)
  { Machine.Stores.empty with refs := [Machine.Val.promise ⟨0⟩] } ==
    some ({ Machine.Stores.empty with refs := [Machine.Val.promise ⟨1⟩] }, Machine.Val.promise ⟨0⟩)
#guard Checker.check nativeSignature [.refOf H, H] []
  (.perform (.refModifyWith handleTree) (.var 0)) == .ok (EffTy.pure H)

/-- Handle reader: the same law returns the previous handle and stores the captured handle. -/
example : Reads (replaceHandle.term
    (Step.callbackSources handleSources caller [] (minted (caller.mint "current"))))
    (caller.push [caller.mint "current"]) [] (handleValues ++ [Machine.Val.promise ⟨0⟩])
    (Store.Val.list [Machine.Val.promise ⟨0⟩, Machine.Val.promise ⟨1⟩]) := by
  have inputs : ∀ {t : Ty} (x : Input HandleCaptures.types t),
      Reads (handleSources x) caller [] handleValues
        ((imageAt Leaves.deferredKeys t).toVal (x.get ((⟨1⟩ : Machine.DeferredKey), ()))) := by
    intro t x
    cases x with
    | here => exact ⟨.var 1, rfl, rfl⟩
    | there _ x => nomatch x
  exact Step.callback_term_reads (L := Leaves.deferredKeys) replaceHandle
    (vs := ((⟨1⟩ : Machine.DeferredKey), ())) rfl inputs (caller.mint "current")
    (⟨0⟩ : Machine.DeferredKey) (reads_minted_last rfl [] "current" (Machine.Val.promise ⟨0⟩)) rfl

/-- Handle typing reader: handle payload types remain contextual rather than opaque acceptance. -/
example : TypesEach nativeSignature (replaceHandle.term
    (Step.callbackSources handleSources caller [] (minted (caller.mint "current"))))
    (caller.push [caller.mint "current"]) [] [.refOf H, H, H] (.prod H H) := by
  have inputs : ∀ {t : Ty} (x : Input HandleCaptures.types t),
      TypesEach nativeSignature (handleSources x) caller [] [.refOf H, H] t := by
    intro t x const
    cases x with
    | here => exact ⟨.var 1, rfl, rfl⟩
    | there _ x => nomatch x
  exact Step.callback_term_types nativeSignature rfl replaceHandle rfl inputs
    (caller.mint "current") (types_minted_last rfl [] "current" H)
    (Step.facts_of_normal replaceHandle rfl)

-- The checker refuses a capture whose actual handle payload differs from the declared payload.
#guard (Checker.check nativeSignature [.refOf H, .deferredOf .bool .never] []
  (.perform (.refModifyWith handleTree) (.var 0))).toOption == none
-- A numeric capture supplied as a string is refused through the real generated callback.
#guard match (Step.callback increment sources (Ref.updateWith (var "r"))) caller [] with
  | .ok tree => (Checker.check nativeSignature [.refOf .nat, .string] [] tree).toOption == none
  | .error _ => false
-- The same callback cannot serve an update row: update requires C rather than [B, C].
#guard match (Step.callback returnCaptured sources (Ref.updateWith (var "r"))) caller [] with
  | .ok tree => (Checker.check nativeSignature [.refOf .nat, .nat] [] tree).toOption == none
  | .error _ => false

end Test.Program.StepCallback
