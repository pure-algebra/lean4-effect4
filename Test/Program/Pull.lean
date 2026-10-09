import Effect4.Author
import Effect4.Run
import Effect4.Emit
import Effect4.Library.Pull.Ops
import Effect4.Library.Stream.ArrayDefs
import Effect4.Laws.Library.Pull.Protocol

/-! Public readers and finite controls for Pull's chunk protocol.
The declared answer column supplies both Chunk and End to the checker.
The controls observe handler replies, escaping failures and retained reference state.
They keep generic typing separate from exact protocol shape and nonempty chunks.
Placement: pull-protocol-selection, translation-simulation, R10; constructor readers serve R4.
These controls establish no host Done adapter, asynchronous progress or stream-loop agreement. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.Pull
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

abbrev protocolTy : Ty := Program.Stream.pulledTy .nat .nat

def chunk (items : TermSrc) : Src NativeOp :=
  succeed (ascribe protocolTy (Effect4.Pull.chunkValue items))

def ended (leftover : TermSrc) : Src NativeOp :=
  succeed (ascribe protocolTy (Effect4.Pull.endValue leftover))

def batch : Src NativeOp := chunk (listOf [nat 1, nat 2])
def done : Src NativeOp := ended (nat 42)

/-- The unused success arm retains the declared protocol column on a failing input. -/
def failing (message : String) : Src NativeOp :=
  ifElse (bool false) batch (fail (str message))

def runSource (source : Src NativeOp) : Option ExitV := do
  let built ← (Api.Author.program source).toOption
  (Api.run built.program 2000).exit

def failed (message : String) : ExitV := .failure ⟨[.fail (.text message) .empty]⟩

def handlers : Effect4.Pull.Handlers :=
  { onSuccess := fun items => succeed (tuple [nat 1, items])
    onDone := fun leftover => succeed (tuple [nat 2, leftover])
    onFailure := fun cause => succeed (tuple [nat 3, cause]) }

#guard runSource (Effect4.Pull.matchEffect batch handlers) =
  some (.success (Val.tuple [.nat 1, .list [.nat 1, .nat 2]]))
#guard runSource (Effect4.Pull.matchEffect done handlers) =
  some (.success (Val.tuple [.nat 2, .nat 42]))
#guard runSource (Effect4.Pull.matchEffect (failing "input") handlers) =
  some (.success (Val.tuple [.nat 3, Val.exitErr ⟨[.fail (.text "input") .empty]⟩]))
#guard runSource (Effect4.Pull.catchDone batch (fun leftover => succeed leftover)) =
  some (.success (.list [.nat 1, .nat 2]))
#guard runSource (Effect4.Pull.catchDone done (fun leftover => succeed leftover)) =
  some (.success (.nat 42))
#guard runSource (Effect4.Pull.catchDone (failing "input") (fun _ => succeed (nat 99))) =
  some (failed "input")

/-- The whole ordinary cause reaches the handler, including its defect reason. -/
def compoundFailure : Src NativeOp :=
  ifElse (bool false) batch
    (failCause (Authoring.Cause.both (Authoring.Cause.fail (str "input"))
      (Authoring.Cause.die (nat 3))))

#guard runSource (Effect4.Pull.matchEffect compoundFailure
  { onSuccess := fun _ => succeed unit
    onDone := fun _ => succeed unit
    onFailure := fun cause => succeed cause }) =
  some (.success (Val.exitErr ⟨[.fail (.text "input") .empty, .die (.user 3) .empty]⟩))

/-- A wrong wrapper around the selected handler would recover these failures as 99. -/
def escapes : Effect4.Pull.Handlers :=
  { onSuccess := fun _ => fail (str "success handler")
    onDone := fun _ => fail (str "end handler")
    onFailure := fun _ => succeed (nat 99) }

#guard runSource (Effect4.Pull.matchEffect batch escapes) = some (failed "success handler")
#guard runSource (Effect4.Pull.matchEffect done escapes) = some (failed "end handler")
#guard runSource (Effect4.Pull.matchEffect (failing "input")
  { escapes with onFailure := fun _ => fail (str "failure handler") }) =
  some (failed "failure handler")
#guard runSource (Effect4.Pull.catchDone done (fun _ => fail (str "end handler"))) =
  some (failed "end handler")

/-- The failure handler reads the store left by the input, rather than its initial store. -/
def retained : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun cell =>
    Effect4.Pull.matchEffect
      (andThen (Forms.asVoid (Ref.set cell (nat 7))) (failing "input"))
      { onSuccess := fun _ => succeed (nat 99)
        onDone := fun _ => succeed (nat 99)
        onFailure := fun _ => Ref.get cell }

#guard runSource retained = some (.success (.nat 7))

/-- A failing finalizer prevents an End answer and retains its own store update. -/
def finalizerFailure : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun cell =>
    Effect4.Pull.matchEffect
      (onExitWith done fun _ =>
        andThen (Forms.asVoid (Ref.set cell (nat 8))) (fail (str "finalizer")))
      { onSuccess := fun _ => succeed (tuple [nat 99, unit])
        onDone := fun _ => succeed (tuple [nat 99, unit])
        onFailure := fun cause =>
          bindWith (Ref.get cell) fun value => succeed (tuple [value, cause]) }

#guard runSource finalizerFailure =
  some (.success (Val.tuple [.nat 8, Val.exitErr ⟨[.fail (.text "finalizer") .empty]⟩]))

/-- Caller names survive the minted binders of all three handler paths. -/
def captured (name : String) (input : Src NativeOp) : Src NativeOp :=
  bindName name (succeed (nat 41)) fun outer =>
    Effect4.Pull.matchEffect input
      { onSuccess := fun items => succeed (tuple [outer, items])
        onDone := fun leftover => succeed (tuple [outer, leftover])
        onFailure := fun cause => succeed (tuple [outer, cause]) }

#guard ["value", "cause", "payload", "rest", "answer"].all fun name =>
  runSource (captured name batch) == some (.success (Val.tuple [.nat 41, .list [.nat 1, .nat 2]])) &&
  runSource (captured name done) == some (.success (Val.tuple [.nat 41, .nat 42])) &&
  runSource (captured name (failing "input")) ==
    some (.success (Val.tuple [.nat 41, Val.exitErr ⟨[.fail (.text "input") .empty]⟩]))

/-- Nested selection allocates distinct minted binders while retaining the outer payload. -/
def nested : Src NativeOp :=
  Effect4.Pull.matchEffect batch
    { onSuccess := fun items => Effect4.Pull.catchDone done fun leftover =>
        succeed (tuple [items, leftover])
      onDone := fun _ => succeed unit
      onFailure := fun _ => succeed unit }

#guard runSource nested = some (.success (Val.tuple [.list [.nat 1, .nat 2], .nat 42]))

-- Typing admits an empty batch; the stream binding supplies the nonempty premise.
#guard (Api.Author.program (chunk (ascribe (.list .nat) nilT))).toOption.isSome
#guard runSource (Effect4.Pull.catchDone (chunk (ascribe (.list .nat) nilT))
    (fun leftover => succeed leftover)) = some (.success (.list []))
#guard Program.Stream.pulled? (Program.Stream.chunkVal []) = none
#guard Program.Stream.pulled? (Program.Stream.chunkVal [.nat 1]) = some (.ok [.nat 1])
#guard Program.Stream.pulled? (Program.Stream.endVal (.nat 42)) = some (.error (.nat 42))

-- A malformed payload or a tag outside the declared protocol fails public admission.
#guard (Api.Author.program (Effect4.Pull.catchDone
  (succeed (ascribe protocolTy (Effect4.Pull.chunkValue (nat 1))))
  (fun leftover => succeed leftover))).toOption.isNone
#guard (Api.Author.program (Effect4.Pull.catchDone
  (succeed (ascribe protocolTy (app "pair" [str "Other", listOf [nat 1]])))
  (fun leftover => succeed leftover))).toOption.isNone
#guard (Api.Author.program (Effect4.Pull.matchAnswer (nat 0)
  (fun value => succeed value) (fun value => succeed value))).toOption.isNone
#guard (Api.Author.program (Effect4.Pull.catchDone
  (succeed (app "pair" [str "Other", listOf [nat 1]]))
  (fun leftover => succeed leftover))).toOption.isNone

/-- Generic tag selection can admit a different declared union; it is outside the Pull profile. -/
def otherColumn : Ty :=
  .union (.prod (.lit "Other") (.list .nat)) (.prod (.lit "End") .nat)

def other : Src NativeOp :=
  Effect4.Pull.catchDone
    (succeed (ascribe otherColumn (app "pair" [str "Other", listOf [nat 1]])))
    (fun leftover => succeed leftover)

#guard runSource other = some (.success (.list [.nat 1]))
#guard Program.Stream.pulled? (.list [.str "Other", .list [.nat 1]]) = none

/-- A module declares the answer column once; each body constructs only its actual variant.
Even an always-failing operation exposes the declared protocol column to its caller. -/
eff_module ProtocolDefinitions where
  emit (items : .list .nat) : protocolTy := succeed (Effect4.Pull.chunkValue items);
  finish (leftover : .nat) : protocolTy := succeed (Effect4.Pull.endValue leftover);
  reject (message : .string) : protocolTy error .string := fail message

def declared : ProtocolDefinitions := ProtocolDefinitions.make "pullProtocol"

def runModule (m : Module NativeOp) : Option ExitV := do
  let built ← (Api.Author.build m).toOption
  (Api.run built.program 2000).exit

#guard runModule (declared.module (Effect4.Pull.matchEffect
  (declared.emit (listOf [nat 1, nat 2])) handlers)) =
  some (.success (Val.tuple [.nat 1, .list [.nat 1, .nat 2]]))
#guard runModule (declared.module (Effect4.Pull.matchEffect
  (declared.finish (nat 42)) handlers)) =
  some (.success (Val.tuple [.nat 2, .nat 42]))
#guard runModule (declared.module (Effect4.Pull.matchEffect
  (declared.reject (ascribe .string (str "input"))) handlers)) =
  some (.success (Val.tuple [.nat 3, Val.exitErr ⟨[.fail (.text "input") .empty]⟩]))

-- Inline checking has no expected protocol column for a lone variant or failure.
#guard (Api.Author.program (Effect4.Pull.matchEffect
  (succeed (Effect4.Pull.chunkValue (listOf [nat 1]))) handlers)).toOption.isNone
#guard (Api.Author.program (Effect4.Pull.matchEffect (fail (str "input")) handlers)).toOption.isNone

/-- A stored array pull already declares the same protocol, without caller ascription. -/
def array : Stream.ArrayDefinitions := Stream.ArrayDefinitions.make "pullArray" .nat

def arrayConsumer : Src NativeOp :=
  bindWith (array.openArray (listOf [nat 1, nat 2])) fun receiver =>
    bindWith (Effect4.Pull.matchEffect (array.pull receiver) handlers) fun first =>
      bindWith (Effect4.Pull.matchEffect (array.pull receiver) handlers) fun second =>
        succeed (tuple [first, second])

#guard runModule (array.module arrayConsumer) = some (.success (Val.tuple
  [Val.tuple [.nat 1, .list [.nat 1, .nat 2]], Val.tuple [.nat 2, .unit]]))

/-- Checked target production and source reading are separate from runtime comparison. -/
def readsBack (source : Src NativeOp) : Bool :=
  match Api.Author.program source with
  | .error _ => false
  | .ok built => match Api.emitModule "main" built.program built.table with
    | .error _ => false
    | .ok emitted => decide (Api.readModule emitted.module built.table = .ok built.program)

#guard readsBack (Effect4.Pull.matchEffect batch handlers)
#guard readsBack (Effect4.Pull.matchEffect done handlers)
#guard readsBack (Effect4.Pull.matchEffect (failing "input") handlers)
#guard readsBack (Effect4.Pull.catchDone batch (fun leftover => succeed leftover))
#guard readsBack retained

/-- Read the End constructor on the numeric carrier through the shared source-reading law. -/
example (env : Env) (path : List Nat) (values : List Val) :
    Reads (Effect4.Pull.endValue (nat 42)) env path values (Program.Stream.endVal (.nat 42)) :=
  Effect4.Pull.endValue_reads (reads_lit (.nat 42) env path values rfl)

/-- Read the numeric End constructor through the existing checker rule. -/
example (env : Env) (path : List Nat) (types : List Ty) :
    TypesEach (nativeSignature []) (Effect4.Pull.endValue (nat 42)) env path types
      (.prod (.lit "End") .nat) :=
  Effect4.Pull.endValue_types rfl rfl (fun flag => types_nat 42 flag)

end Test.Program.Pull
