import Effect4.Author
import Effect4.Run
import Effect4.Emit
import Effect4.Library.Channel.Ops
import Effect4.Library.Stream.Definitions
import Effect4.Library.Stream.Ops
import Effect4.Laws.Library.Stream.Definitions

/-! Finite public module controls for whole-batch Channel transformations.
Placement: channel-batch-transform and channel-completion-transform, translation-simulation, R10.
These observations establish no asynchronous progress or outside-runtime simulation. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.Channel
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
abbrev protocolTy : Ty := Program.Stream.pulledTy .nat .nat
abbrev stateTy : Ty := .refOf .nat

-- The current bool printer needs these producer annotations (decisions row 218).
-- The retained packet records the unannotated target refusal.
eff_module Base where
  opened (receiver : stateTy) : stateTy := succeed receiver;
  pull (receiver : stateTy) : protocolTy :=
    bindWith (Ref.get receiver) fun count =>
      andThen (Forms.asVoid (Ref.set receiver (app "add" [count, nat 1])))
        (ifElse (app "lt" [count, nat 2])
          (succeed (ascribe protocolTy (Effect4.Pull.chunkValue (listOf [count, app "add" [count, nat 10]]))))
          (succeed (ascribe protocolTy (Effect4.Pull.endValue (nat 42)))));
  close (receiver : stateTy) : .unit :=
    bindWith (Ref.get receiver) fun count =>
      Forms.asVoid (Ref.set receiver (app "add" [count, nat 100]));
  reject (receiver : stateTy) : protocolTy error .string :=
    andThen (Forms.asVoid (Ref.set receiver (nat 7)))
      (failCause (Authoring.Cause.both (Authoring.Cause.fail (str "input"))
        (Authoring.Cause.die (nat 3))))

def base : Base := Base.make "channelBase"
eff_module Mapped where
  pull (receiver : stateTy) : protocolTy :=
    Effect4.Channel.map base.definitions.pull receiver (fun _ => listOf [nat 10, nat 20]);
  done (receiver : stateTy) : protocolTy :=
    Effect4.Channel.mapDone base.definitions.pull receiver (fun value => app "add" [value, nat 1]);
  effect (receiver : stateTy) : protocolTy :=
    Effect4.Channel.mapEffect base.definitions.pull receiver (fun items => succeed items);
  failMap (receiver : stateTy) : protocolTy error .string :=
    Effect4.Channel.mapEffect base.definitions.pull receiver (fun _ =>
      andThen (Forms.asVoid (Ref.set receiver (nat 8))) (fail (str "mapper")));
  failDone (receiver : stateTy) : protocolTy error .string :=
    Effect4.Channel.mapDoneEffect base.definitions.pull receiver (fun _ =>
      andThen (Forms.asVoid (Ref.set receiver (nat 11))) (fail (str "done mapper")));
  reject (receiver : stateTy) : protocolTy error .string :=
    Effect4.Channel.mapEffect base.definitions.reject receiver (fun _ => succeed (listOf [nat 99]))
def mapped : Mapped := Mapped.make "channelMapped"
eff_module Nested where
  pull (receiver : stateTy) : protocolTy :=
    Effect4.Channel.mapDoneEffect mapped.definitions.pull receiver
      (fun value => succeed (app "add" [value, nat 1]))
def nested : Nested := Nested.make "channelNested"

def moduleOf (source : Src NativeOp) : Module NativeOp :=
  base.install (mapped.install (nested.install { main := source }))
def runSource (source : Src NativeOp) : Option ExitV := do
  let built ← (Api.Author.build (moduleOf source)).toOption
  (Api.run built.program 10000).exit

def select (source : Src NativeOp) : Src NativeOp :=
  Effect4.Pull.catchDone source (fun value => succeed value)
def direct (initial : Nat) (operation : TermSrc → Src NativeOp) : Src NativeOp :=
  bindWith (Ref.make (nat initial)) fun receiver => select (operation receiver)
#guard runSource (direct 0 mapped.pull) = some (.success (.list [.nat 10, .nat 20]))
#guard runSource (direct 0 mapped.effect) = some (.success (.list [.nat 0, .nat 10]))
#guard runSource (direct 2 mapped.pull) = some (.success (.nat 42))
#guard runSource (direct 2 mapped.done) = some (.success (.nat 43))
#guard runSource (direct 0 mapped.done) = some (.success (.list [.nat 0, .nat 10]))
#guard runSource (direct 2 nested.pull) = some (.success (.nat 43))
#guard runSource (direct 0 nested.pull) = some (.success (.list [.nat 10, .nat 20]))

def observeFailure (operation : TermSrc → Src NativeOp) : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    Effect4.Pull.matchEffect (operation receiver)
      { onSuccess := fun _ => succeed unit, onDone := fun _ => succeed unit,
        onFailure := fun cause => bindWith (Ref.get receiver) fun value =>
          succeed (tuple [value, cause]) }
#guard runSource (observeFailure mapped.reject) = some (.success (Val.tuple
  [.nat 7, Val.exitErr ⟨[.fail (.text "input") .empty, .die (.user 3) .empty]⟩]))
#guard runSource (observeFailure mapped.failMap) = some (.success (Val.tuple
  [.nat 8, Val.exitErr ⟨[.fail (.text "mapper") .empty]⟩]))

def observeDoneFailure : Src NativeOp :=
  bindWith (Ref.make (nat 2)) fun receiver =>
    Effect4.Pull.matchEffect (mapped.failDone receiver)
      { onSuccess := fun _ => succeed unit, onDone := fun _ => succeed unit,
        onFailure := fun cause => bindWith (Ref.get receiver) fun value =>
          succeed (tuple [value, cause]) }
#guard runSource observeDoneFailure = some (.success (Val.tuple
  [.nat 11, Val.exitErr ⟨[.fail (.text "done mapper") .empty]⟩]))

def captured (name : String) : Src NativeOp :=
  bindName name (succeed (nat 41)) fun outer =>
    bindWith (Ref.make (nat 0)) fun receiver =>
      select (Effect4.Channel.map base.definitions.pull receiver
        (fun _ => listOf [outer]))
#guard ["state", "items", "value", "cause", "answer"].all fun name =>
  runSource (captured name) == some (.success (.list [.nat 41]))

def source? (receiver : TermSrc) : Option Stream.Source :=
  (Stream.Source.fromDefinitions base.definitions.opened mapped.definitions.pull
    base.definitions.close [receiver]).toOption

def collect : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    match source? receiver with
    | none => fail (str "adapter")
    | some source => bindWith (Stream.runCollect source) fun values =>
        bindWith (Ref.get receiver) fun count => succeed (tuple [values, count])
#guard runSource collect = some (.success (Val.tuple
  [.list [.nat 10, .nat 20, .nat 10, .nat 20], .nat 103]))

def forEach : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    bindWith (Ref.make (nat 0)) fun total =>
      match source? receiver with
      | none => fail (str "adapter")
      | some source => andThen (Stream.runForEach source (fun item =>
          bindWith (Ref.get total) fun value =>
            Forms.asVoid (Ref.set total (app "add" [value, item]))))
          (bindWith (Ref.get total) fun value =>
            bindWith (Ref.get receiver) fun count => succeed (tuple [value, count]))
#guard runSource forEach = some (.success (Val.tuple [.nat 60, .nat 103]))

def recover (source : Src NativeOp) (handler : TermSrc → Src NativeOp) : Src NativeOp :=
  minting "cause" fun cause =>
    Effect4.Program.Authoring.catchCause cause source (handler (minted cause))

/-- A selected mapper failure still runs the acquired source's close exactly once. -/
def collectFailure : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    match (Stream.Source.fromDefinitions base.definitions.opened mapped.definitions.failMap
      base.definitions.close [receiver]).toOption with
    | none => fail (str "adapter")
    | some source =>
      recover (andThen (Stream.runCollect source) (succeed (nat 999)))
        (fun _ => Ref.get receiver)
#guard runSource collectFailure = some (.success (.nat 108))

/-- A body failure in the element consumer retains its writes before close. -/
def forEachFailure : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    match source? receiver with
    | none => fail (str "adapter")
    | some source =>
      recover (andThen (Stream.runForEach source (fun _ =>
        andThen (Forms.asVoid (Ref.set receiver (nat 9))) (fail (str "body"))))
        (succeed (nat 999))) (fun _ => Ref.get receiver)
#guard runSource forEachFailure = some (.success (.nat 109))

#guard (Stream.Source.fromDefinitions base.definitions.opened
  { mapped.definitions.pull with answer := .nat } base.definitions.close [nat 0]).toOption.isNone
#guard (Stream.Source.fromDefinitions base.definitions.opened mapped.definitions.pull
  { base.definitions.close with answer := .nat } [nat 0]).toOption.isNone
#guard (Stream.Source.fromDefinitions base.definitions.opened
  { mapped.definitions.pull with params := [("receiver", .nat)] }
  base.definitions.close [nat 0]).toOption.isNone
#guard (Api.Author.build { main := direct 0 mapped.pull }).toOption.isNone
#guard (Api.Author.build { defs := [{ base.definitions.pull with body := (fun _ => succeed unit) }], main := direct 0 base.pull }).toOption.isNone
#guard (Stream.Source.fromDefinitions base.definitions.opened mapped.definitions.pull
  { base.definitions.close with params := [("receiver", .nat)] } [nat 0]).toOption.isNone
#guard (Stream.Source.fromDefinitions base.definitions.opened
  { mapped.definitions.pull with answer := .union protocolTy (.lit "Other") }
  base.definitions.close [nat 0]).toOption.isNone
#guard (Stream.Source.fromDefinitions base.definitions.opened
  { mapped.definitions.pull with answer := (.union (.prod (.lit "End") .nat) (.prod (.lit "Chunk") (.list .nat))) }
  base.definitions.close [nat 0]).toOption.isSome
#guard (Stream.Source.fromDefinitions
  { base.definitions.opened with answer := .union stateTy stateTy }
  mapped.definitions.pull base.definitions.close [nat 0]).toOption.isSome

/-- Read the accepted adapter's close invocation at the concrete declared carrier. -/
example {source : Stream.Source}
    (accepted : Stream.Source.fromDefinitions base.definitions.opened mapped.definitions.pull
      base.definitions.close [nat 0] = .ok source) (state : TermSrc) :
    source.close state = Def.invoke base.definitions.close.name [state] :=
  (Stream.Source.fromDefinitions_declarations accepted).2.2.2.2.2.2 state

/-- An entire packed request retains several captured arguments across a Channel invocation. -/
eff_module CapturedRequest where
  pull (offset : .nat) (receiver : stateTy) : protocolTy :=
    Effect4.Channel.map base.definitions.pull receiver (fun _ => listOf [offset])
def withCapture : CapturedRequest := CapturedRequest.make "capturedRequest"
def packedRequest : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    select (Effect4.Channel.map withCapture.definitions.pull
      (requestOf [nat 41, receiver]) (fun items => items))
#guard ((Api.Author.build (withCapture.install (moduleOf packedRequest))).toOption.bind
  fun built => (Api.run built.program 10000).exit) = some (.success (.list [.nat 41]))

/-- Adapter admission concerns supplied declarations, not an independently installed block.
The generic consumer does not read the forged element field. This is an explicit limit. -/
def copiedMetadata : Option Stream.Source :=
  (Stream.Source.fromDefinitions base.definitions.opened
    { mapped.definitions.pull with answer := Program.Stream.pulledTy .bool .nat }
    base.definitions.close [nat 0]).toOption
#guard copiedMetadata.map (·.elem) = some .bool
#guard runSource (bindWith (Ref.make (nat 0)) fun receiver =>
    match Stream.Source.fromDefinitions base.definitions.opened
      { mapped.definitions.pull with answer := Program.Stream.pulledTy .bool .nat }
      base.definitions.close [receiver] with
    | .error _ => fail (str "adapter")
    | .ok source => Stream.runForEach source (fun _ => succeed unit)) = some (.success .unit)

end Test.Program.Channel
