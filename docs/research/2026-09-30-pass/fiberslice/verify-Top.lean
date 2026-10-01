import Research.Pass.FiberSlice.Core

/-! Verifier probe (fiberslice): the top. (1) An internal fiber (a `merge` layer build, site = the
layer's path, `Program/Compile.lean:1453-1455`) has no derived declaration; the prototype reads it
at the top, so a host may name it at `fiberOf unknown unknown` and nowhere else. (2) F12 says no
consumer can use a handle received at `unknown`; the seat tested `awaitFiber` only. Here every
handle consumer of the checker is tried at `unknown`.
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSliceVerify.Top
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice

def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def boolKey : ServiceKey := ⟨⟨5⟩, ⟨5⟩⟩

#guard nativeServiceTy natKey = some .nat
#guard nativeServiceTy boolKey = some .bool

def topRow : Row where
  name := "anyFiber"
  spelling := "Host.anyFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .unknown .unknown
  error := .never
  cite := "verifier probe"

def table : RowTable := [topRow]

/-- Two layers merged (each build is forked by the runtime), then ask the host for a fiber at the
top and join it. -/
def program : Api.Program :=
  .provideLayer (.merge (.effect natKey (.succeed (.lit (.nat 1))))
      (.effect boolKey (.succeed (.lit (.bool true))))) false
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 0) .joinEffect))

#guard (Api.typeOf program table).map (·.answer) = some .unknown

/-- The root first joins the two layer builds, then parks on the host call; flush to get there. -/
def parked : NativeMachine := (Api.replay program 1000 [Api.evaluate, Api.flush] [] table).machine

/-- The root's host-call token, read off the machine's outstanding calls. -/
def token : Nat :=
  ((awaits parked).find? fun (f, _, op, _) => f == Api.root && op == .external 0).map
    (fun (_, t, _, _) => t) |>.getD 999

#guard token != 999
#guard requestOf parked Api.root token == some (.external 0, .unit)

/-- The forked fibers whose recorded site names a layer node: the runtime's layer builds. -/
def layerBuilds : List FiberId :=
  parked.fibers.filterMap fun f =>
    match f.origin with
    | .forked _ _ site =>
      match Node.at_ (.eff program.expandRefs) site with
      | some (.layer _) => some f.id
      | _ => none
    | .root => none

#guard layerBuilds.length = 2
#guard layerBuilds.all fun id => fiberDecl (nativeSignature table) program parked id == none

def naming (id : FiberId) : NativeDecision :=
  .answerAsync Api.root token (.ofExit (.success (Value.fiber id.value)))

-- today's admission also accepts it (the layer builds are live fibers)
#guard layerBuilds.all fun id => admit table parked (naming id) == none

-- the prototype admits a layer build at the top
#guard layerBuilds.all fun id => admitD program table parked (naming id) == none
-- and refuses it at any lower fiber type (the same machine, a `fiberOf nat never` row)
#guard layerBuilds.all fun id =>
  match admitD program [{ topRow with answer := .fiberOf .nat .never }] parked (naming id) with
  | some (.handleDecl _ _ ⟨[], .fiberDecl _ none _⟩) => true
  | _ => false

/-! ## (2) Handle consumers at `unknown`

Every checker rule that reads a handle, applied to a variable of type `unknown` (the host's
answer at the `unknown` row). Each must be refused for F12 to hold. -/

def unknownRow : Row := { topRow with answer := .unknown }
def ask (k : Api.Program) : Api.Program := .bind (.perform (.external 0) (.lit .unit)) k
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

def consumers : List (String × Api.Program) := [
  ("awaitFiber", ask (.awaitFiber (.var 0) .joinEffect)),
  ("interrupt", ask (.withFiber (.interrupt (.var 0)))),
  ("interruptScoped", ask (.withFiber (.interruptScoped (.var 0)))),
  ("awaitAll", ask (.withFiber (.awaitAll (.var 0)))),
  ("awaitNewChildren", ask (.withFiber (.awaitNewChildren (.var 0)))),
  ("setContext", ask (.withFiber (.setContext (.var 0)))),
  ("runIn", ask (.withFiber (.runIn (.var 0) (.var 0)))),
  ("forkIn", ask (.withFiber (.forkIn (.succeed (.lit .unit)) opts (.var 0)))),
  ("closeScope", ask (.bind (.exit (.succeed (.lit .unit)))
    (.withFiber (.closeScope (.var 0) (.var 1))))),
  ("refGet", ask (.perform .refGet (.var 0))),
  ("deferredAwait", ask (.perform .deferredAwait (.var 0)))]

#guard consumers.all fun (_, p) => Api.typeOf p [unknownRow] == none
-- the same consumers accept their proper types (the check is not vacuous): awaitFiber at a fiber
#guard (Api.typeOf (ask (.awaitFiber (.var 0) .joinEffect))
    [{ topRow with answer := .fiberOf .nat .never }]).isSome
-- refGet at the native cell spelling
#guard (Api.typeOf (ask (.perform .refGet (.var 0))) [{ topRow with answer := NativeOp.refTy }]).isSome

end Research.Pass.FiberSliceVerify.Top
