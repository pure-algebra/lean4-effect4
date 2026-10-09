import Effect4.Author
import Effect4.Codegen.Authoring.Forms
import Effect4.Run
import Effect4.Step.Callback
import Effect4.Step.Elab.Inputs

/-! Finite callers of the thirteen effectful Ref rows on latest's pure callback profile.
Each observation contains the operation's reply and the cell read afterward.
The set caller explicitly discards its raw reply through Forms.asVoid.
Placement: controls of ref-steps-agree, translation-simulation, R10.
These are finite machine evaluations, with no host or scheduling theorem. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.RefPrograms
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

step_context% NatCaptures (amount : .nat)
abbrev NatInputs : InputContext := ("current", .nat) :: NatCaptures
def updateBody : Step NatInputs.types .nat :=
  step_inputs% NatInputs => .add current amount
def optionalBody (writes : Bool) : Step NatInputs.types (.option .nat) :=
  step_inputs% NatInputs => if writes then .some (.add current amount) else .none
def modifyBody : Step NatInputs.types (.prod .nat .nat) :=
  step_inputs% NatInputs => .pair (.nat 41) (.add current amount)
def modifySomeBody (writes : Bool) : Step NatInputs.types (.prod .nat (.option .nat)) :=
  step_inputs% NatInputs => .pair (.nat 41) (if writes then .some (.add current amount) else .none)

/-- The public row, supplied with a typed step and an outer capture. -/
def numericCall (name : String) (writes : Bool) (q amount : TermSrc) : Src NativeOp :=
  let captures : {t : Ty} → Input NatCaptures.types t → TermSrc := input_sources% (NatCaptures) {amount := amount}
  match name with
  | "make" => succeed (nat 0)
  | "get" => Ref.get q
  | "set" => Forms.asVoid (Ref.set q (nat 7))
  | "getAndSet" => Ref.getAndSet q (nat 7)
  | "setAndGet" => Ref.setAndGet q (nat 7)
  | "update" => Step.callback updateBody captures (Ref.updateWith q)
  | "getAndUpdate" => Step.callback updateBody captures (Ref.getAndUpdateWith q)
  | "updateAndGet" => Step.callback updateBody captures (Ref.updateAndGetWith q)
  | "updateSome" => Step.callback (optionalBody writes) captures (Ref.updateSomeWith q)
  | "getAndUpdateSome" => Step.callback (optionalBody writes) captures (Ref.getAndUpdateSomeWith q)
  | "updateSomeAndGet" => Step.callback (optionalBody writes) captures (Ref.updateSomeAndGetWith q)
  | "modify" => Step.callback modifyBody captures (Ref.modifyWith q)
  | "modifySome" => Step.callback (modifySomeBody writes) captures (Ref.modifySomeWith q)
  | _ => fail (str "unknown Ref catalogue operation")

/-- A captured caller value named like a conventional callback or fold binder. -/
def numeric (name : String) (writes : Bool := true) (captureName : String := "s") : Src NativeOp :=
  bindName captureName (succeed (nat 2)) fun amount =>
    bindWith (Ref.make (nat 5)) fun q =>
      bindWith (numericCall name writes q amount) fun reply =>
        bindWith (Ref.get q) fun next => succeed (tuple [reply, next])

step_context% StringCaptures (replacement : .string)
abbrev StringInputs : InputContext := ("current", .string) :: StringCaptures
def stringBody : Step StringInputs.types (.prod .string .string) :=
  step_inputs% StringInputs => .pair current replacement

def stringProgram : Src NativeOp :=
  bindWith (succeed (ascribe .string (str "after"))) fun replacement =>
    bindWith (Ref.make (ascribe .string (str "before"))) fun q =>
      bindWith (Step.callback stringBody
        (input_sources% (StringCaptures) {replacement := replacement}) (Ref.modifyWith q)) fun reply =>
        bindWith (Ref.get q) fun next => succeed (tuple [reply, next])

abbrev handleTy : Ty := .deferredOf .nat .never
step_context% HandleCaptures (replacement : handleTy)
abbrev HandleInputs : InputContext := ("current", handleTy) :: HandleCaptures
def handleBody : Step HandleInputs.types (.prod .bool handleTy) :=
  step_inputs% HandleInputs => .pair (.sameDeferred current replacement) replacement

def handleProgram : Src NativeOp :=
  bindWith (Deferred.make .nat .never) fun original =>
    bindWith (Deferred.make .nat .never) fun replacement =>
      bindWith (Ref.make original) fun q =>
        bindWith (Step.callback handleBody
          (input_sources% (HandleCaptures) {replacement := replacement}) (Ref.modifyWith q)) fun reply =>
          bindWith (Ref.get q) fun next =>
            succeed (tuple [reply, app "sameHandle" [next, replacement]])

structure Case where
  name : String
  operation : String
  src : Src NativeOp
  expected : Val

/-- The independent expected observation of a number-cell operation. -/
def expectedNumeric (name : String) (writes : Bool) : Val :=
  let next := if ["make", "get"].contains name || (!writes &&
    ["updateSome", "getAndUpdateSome", "updateSomeAndGet", "modifySome"].contains name) then 5 else 7
  let reply := match name with
    | "make" => Val.nat 0
    | "set" | "update" | "updateSome" => Val.unit
    | "get" | "getAndSet" | "getAndUpdate" | "getAndUpdateSome" => Val.nat 5
    | "modify" | "modifySome" => Val.nat 41
    | _ => Val.nat next
  Val.tuple [reply, .nat next]

def operations : List String :=
  ["make", "get", "set", "getAndSet", "setAndGet", "update", "getAndUpdate", "updateAndGet",
   "updateSome", "getAndUpdateSome", "updateSomeAndGet", "modify", "modifySome"]
def optionalOperations : List String :=
  ["updateSome", "getAndUpdateSome", "updateSomeAndGet", "modifySome"]
def cases : List Case :=
  operations.map (fun name => ⟨name, name, numeric name, expectedNumeric name true⟩) ++
  optionalOperations.map (fun name => ⟨name ++ "None", name, numeric name false, expectedNumeric name false⟩) ++
  [⟨"captureAcc", "modify", numeric "modify" true "acc", expectedNumeric "modify" true⟩,
   ⟨"captureItem", "modify", numeric "modify" true "item", expectedNumeric "modify" true⟩,
   ⟨"string", "modify", stringProgram, Val.tuple [.str "before", .str "after"]⟩,
   ⟨"allocatedHandle", "modify", handleProgram, Val.tuple [.bool false, .bool true]⟩]

def observation (src : Src NativeOp) : Option Val := do
  let b ← (Api.Author.program src).toOption
  match (Api.run b.program 1000).exit with
  | some (.success value) => some value
  | _ => none

#guard cases.length == 21 && (cases.map (·.name)).eraseDups.length == 21
#guard (cases.map (·.operation)).eraseDups == operations
#guard cases.all fun c => observation c.src == some c.expected
-- The machine's raw set reply is the cell identity; latest returns its backing object.
#guard observation (bindWith (Ref.make (nat 5)) fun q =>
  bindWith (Ref.set q (nat 7)) fun reply =>
    bindWith (Ref.get q) fun next =>
      succeed (tuple [app "sameHandle" [reply, q], next])) =
  some (Val.tuple [.bool true, .nat 7])
-- A changed next value differs even when the reply remains 41.
#guard expectedNumeric "modify" true != Val.tuple [.nat 41, .nat 5]
-- The public capture must type as a number; successful elaboration alone does not suffice.
#guard (Api.Author.program (bindWith (Ref.make (nat 5)) fun q =>
  Step.callback updateBody (input_sources% (NatCaptures) {amount := str "wrong"})
    (Ref.updateWith q))).toOption.isNone
-- A callback's current slot is not a caller's input.
#guard (Api.Author.program (Ref.update "current" (var "current") (var "current"))).toOption.isNone

end Test.Program.RefPrograms
