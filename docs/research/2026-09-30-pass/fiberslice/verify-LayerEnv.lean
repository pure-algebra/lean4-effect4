import Research.Pass.FiberSlice.Core

/-! Verifier probe (fiberslice): a fork inside a layer body, the layer provided under a binder.
The checker types a layer's effect body closed, at `[]` (`checkLayer` takes no environment;
the prototype's `envStep` sets `[]` at a layer's effect child, Core.lean:49-50). The runtime
resolves the body at a point derived from the providing site (`innerLayerAt`,
`constructionAt`, `Program/Compile.lean:715-747`), and `Point.child` keeps the environment
(`Compile.lean:80`), so the body runs in the enclosing environment. Variables are read by level
(`env[index]?`, `Machine/Term.lean:427`). Question: is the derived declaration of such a fork
what the fork returns, and what does the prototype do when a host names it?
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSliceVerify.LayerEnv
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice

def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩
/-- A free service key typed `nat` (type code 4), as in the seat's `Holes.lean`. -/
def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

/-- The layer body: bind 5, fork a child returning `var 0`, provide 7. Checked closed, `var 0`
is the body's own binder (`nat`). -/
def layerBody : Api.Program :=
  .bind (.succeed (.lit (.nat 5)))
    (.bind (.withFiber (.fork (.succeed (.var 0)) opts)) (.succeed (.lit (.nat 7))))

/-- The layer provided under a `string` binder; the program reads the service. -/
def program : Api.Program :=
  .bind (.succeed (.lit (.str "s")))
    (.provideLayer (.effect natKey layerBody) false (.service natKey))

#guard nativeServiceTy natKey = some .nat
#guard Api.typeOf program = some (EffTy.pure .nat)

def ran : Api.Inspection := Api.run program 1000

/-- Every forked fiber: id, site, derived declaration's answer, exit. -/
def forks (p : Api.Program) (m : NativeMachine) (table : RowTable := []) :
    List (FiberId × List Nat × Option Ty × Option ExitV) :=
  m.fibers.filterMap fun f =>
    match f.origin with
    | .forked _ _ site =>
      some (f.id, site, (fiberDecl (nativeSignature table) p m f.id).map (·.answer), f.exit)
    | .root => none

-- the root finishes with 7; one fork, inside the layer body, declared `nat` by the checker,
-- and it returned the *outer* binder's string: the body ran in the enclosing environment
#guard ran.exit == some (.success (.nat 7))
#guard (forks program ran.machine).map (fun x => (x.1, x.2.2.1)) = [(⟨1⟩, some .nat)]
#guard (forks program ran.machine).map (fun x => x.2.2.2) = [some (.success (.str "s"))]
-- so the seat's declaration-lane invariant fails here: the success does not fit its declaration
#guard (forks program ran.machine).all fun (id, _, _, ex) =>
  match ex, fiberDecl (nativeSignature []) program ran.machine id with
  | some (.success v), some d =>
    !fits (fiberDecl (nativeSignature []) program ran.machine) ran.machine.state.externals.allocated
      v d.answer
  | _, _ => false

/-! ### A host names that fiber at its declared type

The same layer, then the program asks a host for a `fiberOf nat never` and joins it. The host
names the layer-body fork. Its derived declaration is `nat`, so the prototype admits the reply,
and the `nat`-checked program finishes with the string. -/

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "verifier probe"

def table : RowTable := [fiberRow]

/-- Levels: `var 0` the outer string; inside the provided body `var 1` the service, `var 2` the
host's answer. -/
def askProgram : Api.Program :=
  .bind (.succeed (.lit (.str "s")))
    (.provideLayer (.effect natKey layerBody) false
      (.bind (.service natKey)
        (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 2) .joinEffect))))

#guard Api.typeOf askProgram table = some (EffTy.pure .nat)

def parked : NativeMachine := (Api.replay askProgram 1000 [Api.evaluate] [] table).machine

#guard requestOf parked Api.root 0 == some (.external 0, .unit)
#guard (forks askProgram parked table).map (fun x => (x.1, x.2.2.1, x.2.2.2)) =
  [(⟨1⟩, some .nat, some (.success (.str "s")))]

def answer : NativeDecision := .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1)))

-- both admissions accept: the declaration says `nat`
#guard admit table parked answer = none
#guard admitD askProgram table parked answer = none

-- the keyed session through the prototype: applied, and the `nat` program returns "s"
def header : Api.HostSession.Header := ⟨Api.HostSession.version, "probe", "probe", table⟩
def call : Api.HostSession.Call :=
  ⟨Api.HostSession.version, "probe", table, 0, Api.root, .external 0, .unit⟩
def reply : Api.HostSession.Reply :=
  ⟨Api.HostSession.version, "probe", 0, ⟨Api.root, 0⟩, .ofExit (.success (Value.fiber 1))⟩

def protoSession : Option (List Api.HostSession.Phase × Option ExitV) :=
  match Api.HostSession.start askProgram table "probe" header 1000 with
  | .error _ => none
  | .ok s0 =>
    let s1 := (Api.HostSession.advance s0 1000 Api.evaluate).session
    let s2 := (Api.HostSession.bindCall s1 call 0).session
    let r3 := submitD s2 reply
    let r4 := applyReplyD r3.session reply.key 1000
    let r5 := Api.HostSession.advance r4.session 1000 Api.flush
    some ([r3.phase, r4.phase, r5.phase], (r5.session.machine.fiber? Api.root).bind (·.exit))

#guard protoSession = some ([.preflight, .applied, .progressed], some (.success (.str "s")))

/-! ### Red control: the guards above can fail -/

/-- error: Expression
  decide
    (protoSession =
      some
        ([Api.HostSession.Phase.preflight, Api.HostSession.Phase.applied, Api.HostSession.Phase.progressed],
          some (Exit.success (Val.nat 7))))
did not evaluate to `true` -/
#guard_msgs in
#guard protoSession = some ([.preflight, .applied, .progressed], some (.success (.nat 7)))

end Research.Pass.FiberSliceVerify.LayerEnv
