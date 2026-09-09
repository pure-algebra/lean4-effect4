import Effect4.Api
import Effect4.Laws.Program.Admit

namespace Test.Api.AcquireHandleContract
open Effect4 Effect4.Program Effect4.Machine

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def resource := "Host.Resource"
def table : RowTable :=
  [ { name := "acquire", spelling := "Host.acquire", kind := .async,
      registration := .external, request := .unit, answer := .handle resource, error := .never, cite := "" }
  , { name := "close", spelling := "Host.close", kind := .async,
      registration := .external, request := .handle resource, answer := .unit, error := .never, cite := "" }
  , { name := "read", spelling := "Host.read", kind := .async,
      registration := .external, request := .handle resource, answer := .nat, error := .never, cite := "" } ]

def acquire : NativeEff := .callback (.external 0) (.lit .unit)
def answer (v : Val) : Completion Val Err Defect FiberId Ann := .ofExit (.success v)
def program : NativeEff :=
  .scoped (.bind (.acquireRelease acquire (.callback (.external 1) (.var 0)))
    (.callback (.external 2) (.var 0)))

#guard HandleKind.external.byte = 7
#guard HandleKind.ofByte? 6 = none
#guard HandleKind.ofByte? 7 = some .external
-- the value spelling and the kind byte agree; the internal spellings are the four named ones
#guard Value.external 3 = .handle HandleKind.external.byte 3
#guard internalHandleTargets = ["Ref.Ref<number>", "Deferred.Deferred<number, number>", "Scope.Scope", "Context.Context<unknown>"]
#guard !externalHandleTarget "Scope.Scope"
#guard externalHandleTarget resource
#guard nativeServiceTy ⟨⟨4⟩, ⟨8⟩⟩ = some (.handle "SqlClient.SqlClient")
#guard nativeServiceTy ⟨⟨5⟩, ⟨9⟩⟩ = some (.handle "KeyValueStore.KeyValueStore")
#guard LawfulTable table
#guard Val.hasTy (.handle 7 0) (.handle resource) [resource]
#guard !Val.hasTy (.handle 7 0) (.handle "Other.Resource") [resource]
#guard !Val.hasTy (.handle 7 1) (.handle resource) [resource]
#guard !Val.hasTy (.handle 7 0) NativeOp.refTy ["Ref.Ref<number>"]
#guard externalValue (.handle resource) [] (.nat 0) = some ([resource], .handle 7 0)
#guard externalValue (.handle resource) [] (.nat 1) = none
#guard externalValue (.handle resource) [resource] (.handle 7 0) = none
#guard Api.typeOf program table =
  some ⟨.nat, .never, Env.Requirement.single (nativeSignature table).scopeKey⟩
#guard Api.roundTrip program table = .ok program
#guard (Api.run program 1000 [] [answer (.nat 0), answer (.nat 7), answer .unit] table).exit =
  some (.success (.nat 7))
#guard (Api.run program 1000 [] [answer (.nat 0), answer (.nat 7), answer .unit] table).stores.externals.allocated =
  [resource]

def parked := (Api.replay acquire 1000 [Api.evaluate] [] [] table).machine
#guard (prepareAsyncAnswer (interpOf acquire table) parked Api.root 1 (answer (.nat 0))).1.externals.allocated = []
#guard (prepareAsyncAnswer (interpOf acquire table) parked Api.root 0 (answer (.nat 0))).1.externals.allocated = [resource]
#guard letI := evaluatorFor acquire table
  let (next, settled) := stepDecisionState (interpOf acquire table) 0 parked
    (.answerAsync Api.root 0 (answer (.nat 0)))
  next.state.externals.allocated.isEmpty && !settled
#guard letI := evaluatorFor acquire table
  let stopped := { parked with stuck := some (.unknownFiber ⟨99⟩) }
  let (next, settled) := stepDecisionState (interpOf acquire table) 0 stopped
    (.answerAsync Api.root 0 (answer (.nat 0)))
  next.state.externals.allocated.isEmpty && settled
#guard match Api.replayChecked acquire 1000 [Api.evaluate, .answerAsync Api.root 0 (answer (.nat 0))] [] [] table with
  | .inl run => run.exit = some (.success (.handle 7 0)) && run.stores.externals.allocated == [resource]
  | .inr _ => false
#guard match Api.replayChecked acquire 1000 [Api.evaluate, .answerAsync Api.root 0 (answer (.nat 1))] [] [] table with
  | .inr (_, _, .answerType _ _ _, m) => m.state.externals.allocated.isEmpty
  | _ => false

end Test.Api.AcquireHandleContract
