import Effect4.Author
import Effect4.Run
import Effect4.Emit
import Effect4.Library.Pull.Ops
import Effect4.Laws.Codegen.ReadPrint

/-! Public branches retain their distinct answer, error and requirement columns.
These finite controls consume the ruled boolean printer and its existing reconstruction law.
Placement: readers and controls of read_print and read_exact, exact-codecs, R8.
Machine observations and the emitted packet remain finite evidence, with no host simulation theorem. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.BranchAuthoring
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The ordinary public conditional carries no branch annotation. -/
def plain (choose : Bool) : Src NativeOp :=
  ifElse (bool choose) (succeed (nat 7)) (succeed (nat 9))

/-- Different answer shapes retain the existing Chunk and End protocol. -/
def batch (choose : Bool) : Src NativeOp :=
  ifElse (bool choose)
    (succeed (Effect4.Pull.chunkValue (listOf [nat 1, nat 2])))
    (succeed (Effect4.Pull.endValue (nat 42)))

def sumBatch (items : TermSrc) : TermSrc :=
  app "add" [app "getOrElse" [app "get" [items, nat 0], nat 0],
    app "getOrElse" [app "get" [items, nat 1], nat 0]]

def batchNumber (choose : Bool) : Src NativeOp :=
  Effect4.Pull.matchEffect (batch choose)
    { onSuccess := fun items => succeed (sumBatch items)
      onDone := fun leftover => succeed leftover
      onFailure := fun _ => succeed (nat 999) }

-- Each branch declares its own tagged error class, without a shared annotation.
eff_failure LeftFailure where code : .nat
eff_failure RightFailure where code : .nat

def errors (choose : Bool) : Src NativeOp :=
  ifElse (bool choose) (LeftFailure.raise (nat 11)) (RightFailure.raise (nat 22))

/-- Recover the actual selected error's numeric field, not the condition used to select it. -/
def errorNumber (choose : Bool) : Src NativeOp :=
  minting "value" fun value => minting "cause" fun cause =>
    matchCause value cause (errors choose) (succeed (nat 999))
      (selectOptionWith (app "causeError" [minted cause]) (succeed (nat 998))
        fun error => succeed (field error "code"))

/-- Each selected branch adds its distinct contribution to one shared cell. -/
def addState (cell : TermSrc) (amount : Nat) : Src NativeOp :=
  bindWith (Ref.get cell) fun current =>
    Forms.asVoid (Ref.set cell (app "add" [current, nat amount]))

def state (choose : Bool) : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun cell =>
    andThen (ifElse (bool choose) (addState cell 1) (addState cell 10)) (Ref.get cell)

/-- The selected failing branch leaves its update available to the failure handler. -/
def stateFailure : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun cell =>
    minting "value" fun value => minting "cause" fun cause =>
      matchCause value cause
        (ifElse (bool true)
          (andThen (addState cell 7) (LeftFailure.raise (nat 7)))
          (andThen (addState cell 10) (RightFailure.raise (nat 10))))
        (succeed (nat 999)) (Ref.get cell)

/-- This native number service is also used by the existing module authoring controls. -/
def numberKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

def required (choose : Bool) : Src NativeOp :=
  ifElse (bool choose) (service numberKey) (succeed (nat 9))

def provided (choose : Bool) : Src NativeOp :=
  provideService numberKey (nat 17) (required choose)

structure Case where
  name : String
  source : Src NativeOp
  expected : Nat

/-- One source inventory supplies both the machine controls and the target producer. -/
def cases : List Case :=
  [ ⟨"plainTrue", plain true, 7⟩, ⟨"plainFalse", plain false, 9⟩
  , ⟨"batchTrue", batchNumber true, 3⟩, ⟨"batchFalse", batchNumber false, 42⟩
  , ⟨"errorLeft", errorNumber true, 11⟩, ⟨"errorRight", errorNumber false, 22⟩
  , ⟨"stateTrue", state true, 1⟩, ⟨"stateFalse", state false, 10⟩
  , ⟨"stateFailure", stateFailure, 7⟩
  , ⟨"serviceTrue", provided true, 17⟩, ⟨"serviceFalse", provided false, 9⟩ ]

def runSource (source : Src NativeOp) : Option ExitV := do
  let built ← (Api.Author.program source).toOption
  (Api.run built.program 10000).exit

#guard cases.all fun c => runSource c.source == some (.success (.nat c.expected))
#guard ((Api.Author.program (batch true)).toOption.map (·.ty.answer)) =
  some (Program.Stream.pulledTy .nat .nat).normalize
#guard ((Api.Author.program (errors true)).toOption.map (·.ty.error)) =
  some (LeftFailure.ty.join RightFailure.ty)
#guard ((Api.Author.program (required true)).toOption.map (·.ty.requires)) =
  some (Effect4.Machine.Env.Requirement.ofList [numberKey])

/-- Captures keep their positional reading beneath zero-argument printed branch thunks. -/
def captured (name : String) (choose : Bool) : Src NativeOp :=
  bindName name (succeed (nat 41)) fun outer =>
    ifElse (bool choose) (succeed outer) (succeed (app "add" [outer, nat 1]))
#guard ["ifCase", "condition", "left", "right", "value", "answer"].all fun name =>
  runSource (captured name true) == some (.success (.nat 41)) &&
  runSource (captured name false) == some (.success (.nat 42))

/-- Read back every finite module, including its declared error classes. -/
def readsBack (source : Src NativeOp) : Bool :=
  match Api.Author.program source with
  | .error _ => false
  | .ok built => match Api.emitModule "main" built.program built.table with
    | .error _ => false
    | .ok emission => decide (Api.readModule emission.module built.table = .ok built.program)
#guard cases.all fun c => readsBack c.source

/-- A concrete carrier of the public plain conditional consumes the shared reconstruction law. -/
def plainTree : NativeEff :=
  .select (.lit (.bool true)) .bool (.succeed (.lit (.nat 7))) (.succeed (.lit (.nat 9)))
#guard elaborate (plain true) = .ok plainTree
example {expression : TypeScript.Expr}
    (printed : Program.print (nativeSignature []) 0 plainTree = .ok expression) :
    Api.read expression = .ok plainTree :=
  read_print (classes := []) nativeLawful (by decide +kernel) printed

-- The helper owns its exported spelling and no host row may capture it.
#guard match Api.emitModule "ifCase" plainTree with
  | .error (.print (.unsafeName "ifCase")) => true
  | _ => false

def collidingRow : RowDef := Row.host "ifCase" .unit .nat .never "branch control"
#guard match Api.emitModule "main" plainTree [collidingRow.row] with
  | .error (.print (.unsafeName "ifCase")) => true
  | _ => false

/-- The exact canonical image has three zero-argument, unannotated thunks. -/
def branchImage : TypeScript.Expr :=
  .call (.ident "ifCase")
    [.arrow none (.bool true),
     .arrow none (.call (.ident "Effect.succeed") [.int 7]),
     .arrow none (.call (.ident "Effect.succeed") [.int 9])]
#guard Api.read branchImage = .ok plainTree
-- Eager conditions, missing/surplus arguments, direct branch effects and payload binders refuse.
#guard (Api.read (.call (.ident "ifCase")
  [.bool true, .arrow none (.call (.ident "Effect.succeed") [.int 7]),
   .arrow none (.call (.ident "Effect.succeed") [.int 9])])).toOption.isNone
#guard (Api.read (.call (.ident "ifCase") [.arrow none (.bool true)])).toOption.isNone
#guard (Api.read (.call (.ident "ifCase")
  [.arrow none (.bool true), .arrow none (.call (.ident "Effect.succeed") [.int 7]),
   .arrow none (.call (.ident "Effect.succeed") [.int 9]), .int 0])).toOption.isNone
#guard (Api.read (.call (.ident "ifCase")
  [.arrow none (.bool true), .call (.ident "Effect.succeed") [.int 7],
   .arrow none (.call (.ident "Effect.succeed") [.int 9])])).toOption.isNone
#guard (Api.read (.call (.ident "ifCase")
  [.lambda [{ name := "a0" }] (.bool true),
   .arrow none (.call (.ident "Effect.succeed") [.int 7]),
   .arrow none (.call (.ident "Effect.succeed") [.int 9])])).toOption.isNone
#guard (Api.read (.call (.ident "ifCase")
  [.arrow none (.bool true),
   .lambda [{ name := "a0" }] (.call (.ident "Effect.succeed") [.int 7]),
   .arrow none (.call (.ident "Effect.succeed") [.int 9])])).toOption.isNone
#guard (Api.read (.call (.ident "ifCase")
  [.arrow (some (.name ["boolean"] [])) (.bool true),
   .arrow none (.call (.ident "Effect.succeed") [.int 7]),
   .arrow none (.call (.ident "Effect.succeed") [.int 9])])).toOption.isNone
-- The former suspension/conditional spelling is retained evidence, outside the new exact image.
#guard (Api.read (.call (.ident "Effect.suspend")
  [.arrow none (.cond (.bool true) (.call (.ident "Effect.succeed") [.int 7])
    (.call (.ident "Effect.succeed") [.int 9]))])).toOption.isNone
#guard (Api.Author.program (ifElse (nat 1) (succeed (nat 7)) (succeed (nat 9)))).toOption.isNone

end Test.Program.BranchAuthoring
