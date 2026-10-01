import Research.Pass.FiberSlice.Core

/-! Task 1: the prototype on the live keyed session path. Finite checks, not proofs.
Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSlice.Live
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice
open Effect4.Api.HostSession (Session Header Call Reply Key Result Phase)

/-! ## 1. The live path: forged and honest replies

`Probe.lean` §2 of the host-answers evidence, driven through the prototype. A host row answers
`fiberOf nat never`; the program forks a child, asks the host for a fiber and joins it. -/

section LivePath

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "research probe"

def table : RowTable := [fiberRow]
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

/-- Fork a child returning `child`, ask the host for a fiber, join the fiber it names.
`var 1` is the host's answer (binder levels count from the outside). -/
def forkThenAsk (child : Term) : Api.Program :=
  .bind (.withFiber (.fork (.succeed child) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

def wrongProgram : Api.Program := forkThenAsk (.lit (.str "wrong"))
def rightProgram : Api.Program := forkThenAsk (.lit (.nat 7))

def header : Header := ⟨Api.HostSession.version, "probe", "probe", table⟩
def call : Call := ⟨Api.HostSession.version, "probe", table, 0, Api.root, .external 0, .unit⟩
def reply : Reply := ⟨Api.HostSession.version, "probe", 0, ⟨Api.root, 0⟩, .ofExit (.success (Value.fiber 1))⟩

/-- The session after start, evaluate and bind: the root parked on the host call. -/
def boundOf (program : Api.Program) : Option (Session program table) :=
  match Api.HostSession.start program table "probe" header 1000 with
  | .error _ => none
  | .ok s0 =>
    let r1 := Api.HostSession.advance s0 1000 Api.evaluate
    some (Api.HostSession.bindCall r1.session call 0).session

/-- Old route: submit, apply, flush; the phases and the root's exit. -/
def oldPath (program : Api.Program) : Option (List Phase × Option ExitV) :=
  (boundOf program).map fun s =>
    let r3 := Api.HostSession.submit s reply
    let r4 := Api.HostSession.applyReply r3.session reply.key 1000
    let r5 := Api.HostSession.advance r4.session 1000 Api.flush
    ([r3.phase, r4.phase, r5.phase], (r5.session.machine.fiber? Api.root).bind (·.exit))

/-- Prototype route: the same, with `submitD` and `applyReplyD`. -/
def newPath (program : Api.Program) : Option (List Phase × Option ExitV) :=
  (boundOf program).map fun s =>
    let r3 := submitD s reply
    let r4 := applyReplyD r3.session reply.key 1000
    let r5 := Api.HostSession.advance r4.session 1000 Api.flush
    ([r3.phase, r4.phase, r5.phase], (r5.session.machine.fiber? Api.root).bind (·.exit))

-- both programs check at `nat` and admit
#guard Api.typeOf wrongProgram table = some (EffTy.pure .nat)
#guard Api.typeOf rightProgram table = some (EffTy.pure .nat)

-- the old route: the forged reply is applied and the `nat` program finishes with a string
#guard (oldPath wrongProgram).map (·.1) = some [.preflight, .applied, .progressed]
#guard (oldPath wrongProgram).map (·.2) = some (some (.success (.str "wrong")))

-- the prototype: the forged reply is refused at submit; nothing is stored or applied
#guard (newPath wrongProgram).map (·.1) =
  some [.refused .envelope, .refused .noCall, .progressed]
#guard (newPath wrongProgram).map (·.2) = some none

-- the honest reply is applied and the program finishes with 7, on both routes
#guard (newPath rightProgram).map (·.1) = some [.preflight, .applied, .progressed]
#guard (newPath rightProgram).map (·.2) = some (some (.success (.nat 7)))
#guard (oldPath rightProgram) = (newPath rightProgram)

/-- The declaration the prototype reads for fiber 1, and the located refusal it reports. -/
def parkedMachine (program : Api.Program) : Option NativeMachine :=
  (boundOf program).map (·.machine)

#guard ((parkedMachine wrongProgram).bind fun m =>
    (fiberDecl (nativeSignature table) wrongProgram m ⟨1⟩).map (·.answer)) = some .string
#guard ((parkedMachine rightProgram).bind fun m =>
    (fiberDecl (nativeSignature table) rightProgram m ⟨1⟩).map (·.answer)) = some .nat
#guard ((parkedMachine wrongProgram).bind fun m =>
    (fiberDecl (nativeSignature table) wrongProgram m Api.root).map (·.answer)) = some .nat

-- the located refusal: at value path [], fiber 1 declared `string`, expected `fiberOf nat never`
#guard ((parkedMachine wrongProgram).map fun m =>
    admitD wrongProgram table m (.answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))))) =
  some (some (.handleDecl Api.root 0
    ⟨[], .fiberDecl ⟨1⟩ (some (EffTy.pure .string)) (.fiberOf .nat .never)⟩))
-- and the old admission accepts the same decision
#guard ((parkedMachine wrongProgram).map fun m =>
    admit table m (.answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))))) = some none

-- a handle to a fiber that does not exist is still `deadHandle` (liveness before declaration)
#guard ((parkedMachine rightProgram).map fun m =>
    admitD rightProgram table m (.answerAsync Api.root 0 (.ofExit (.success (Value.fiber 9))))) =
  some (some (.admit (.deadHandle Api.root 0)))

-- the tape route: `replayChecked` accepts the forged answer, `replayCheckedD` refuses it at 1
#guard (match Api.replayChecked wrongProgram 1000
    [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))), Api.flush] [] table with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.str "wrong")))
#guard (match replayCheckedD wrongProgram 1000
    [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))), Api.flush] [] table with
  | .inr (position, _, .handleDecl _ _ ⟨[], .fiberDecl ⟨1⟩ _ _⟩, _) => position == 1
  | _ => false)
#guard (match replayCheckedD rightProgram 1000
    [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))), Api.flush] [] table with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.nat 7)))

end LivePath

/-! ## 2. Nested positions: every gap of the old predicate, on the admission

One row per nesting, each answering a fiber of `nat` somewhere inside. Fiber 1 is a child the
program forked first; it returns `"wrong"` in the forged case and `7` in the honest one. The
old admission (`admit`) accepts both; the prototype refuses the forged one at the value path
of the handle and accepts the honest one. -/

section Nested

def rowAt (answer : Ty) : Row := { fiberRow with answer }

/-- Fork a child, then ask the host (the answer is `var 1`) and continue with `k`. -/
def forkAsk (child : Term) (k : Api.Program) : Api.Program :=
  .bind (.withFiber (.fork (.succeed child) opts)) (.bind (.perform (.external 0) (.lit .unit)) k)

def ap (a : String) (xs : List Term) : Term :=
  .app a (xs.foldr (fun t acc => .cons t acc) .nil)

/-- A nesting: the row's answer type, the continuation that uses the answer, the forged value,
and the value path the refusal must name. -/
structure Nesting where
  name : String
  answer : Ty
  k : Api.Program
  value : Val
  at_ : List Nat

def fNat : Ty := .fiberOf .nat .never

def nestings : List Nesting := [
  ⟨"fiber", fNat, .awaitFiber (.var 1) .joinEffect, Value.fiber 1, []⟩,
  ⟨"prod", .prod fNat .unit, .awaitFiber (ap "fst" [.var 1]) .joinEffect,
    .list [Value.fiber 1, .unit], [0]⟩,
  ⟨"option", .option fNat,
    .select (.var 1) .option (.succeed (.lit (.nat 0))) (.awaitFiber (.var 2) .joinEffect),
    .some (Value.fiber 1), [0]⟩,
  ⟨"list", .list fNat, .withFiber (.awaitAll (.var 1)), .list [Value.fiber 1], [0]⟩,
  ⟨"snapshot", .list fNat, .withFiber (.awaitAll (.var 1)),
    Value.fiberSnapshot (.list [Value.fiber 1]), [0, 0]⟩,
  ⟨"result", .except .never fNat, .succeed (.var 1), .ctor 1 [Value.fiber 1], [0]⟩,
  ⟨"exit", .exitOf fNat .never, .succeed (.var 1), Value.exitOk (Value.fiber 1), [0]⟩,
  ⟨"union", .union fNat .unit, .succeed (.var 1), Value.fiber 1, []⟩]

def programOf (x : Nesting) (child : Term) : Api.Program := forkAsk child x.k
def tableOf (x : Nesting) : RowTable := [rowAt x.answer]

/-- The machine after the root's first evaluation: the child forked and exited, the root
parked on the host call at token 0. -/
def parkedOf (x : Nesting) (child : Term) : NativeMachine :=
  (Api.replay (programOf x child) 1000 [Api.evaluate] [] (tableOf x)).machine

def decisionOf (x : Nesting) : NativeDecision :=
  .answerAsync Api.root 0 (.ofExit (.success x.value))

def oldVerdict (x : Nesting) (child : Term) : Option Refusal :=
  admit (tableOf x) (parkedOf x child) (decisionOf x)

def newVerdict (x : Nesting) (child : Term) : Option RefusalD :=
  admitD (programOf x child) (tableOf x) (parkedOf x child) (decisionOf x)

def wrongChild : Term := .lit (.str "wrong")
def rightChild : Term := .lit (.nat 7)

-- every nesting's program checks and parks at token 0 on the host row
#guard nestings.all fun x => (Api.typeOf (programOf x wrongChild) (tableOf x)).isSome
#guard nestings.all fun x => (Api.typeOf (programOf x rightChild) (tableOf x)).isSome
#guard nestings.all fun x =>
  requestOf (parkedOf x wrongChild) Api.root 0 == some (.external 0, .unit)

-- the old admission accepts every forged value, and every honest one
#guard nestings.all fun x => oldVerdict x wrongChild == none
#guard nestings.all fun x => oldVerdict x rightChild == none

-- the prototype refuses every forged value at its path, naming fiber 1 declared `string`
#guard nestings.all fun x => newVerdict x wrongChild ==
  some (.handleDecl Api.root 0 ⟨x.at_, .fiberDecl ⟨1⟩ (some (EffTy.pure .string)) fNat⟩)
-- and accepts every honest one
#guard nestings.all fun x => newVerdict x rightChild == none

/-- Through the whole live session: start, evaluate, bind, submit, apply, flush. -/
def sessionRun (x : Nesting) (child : Term) (useNew : Bool) :
    Option (List Phase × Option ExitV) :=
  let program := programOf x child
  let table := tableOf x
  let header : Header := ⟨Api.HostSession.version, "probe", "probe", table⟩
  let call : Call := ⟨Api.HostSession.version, "probe", table, 0, Api.root, .external 0, .unit⟩
  let reply : Reply := ⟨Api.HostSession.version, "probe", 0, ⟨Api.root, 0⟩, .ofExit (.success x.value)⟩
  match Api.HostSession.start program table "probe" header 1000 with
  | .error _ => none
  | .ok s0 =>
    let s1 := (Api.HostSession.advance s0 1000 Api.evaluate).session
    let s2 := (Api.HostSession.bindCall s1 call 0).session
    let r3 := if useNew then submitD s2 reply else Api.HostSession.submit s2 reply
    let r4 := if useNew then applyReplyD r3.session reply.key 1000
      else Api.HostSession.applyReply r3.session reply.key 1000
    let r5 := Api.HostSession.advance r4.session 1000 Api.flush
    some ([r3.phase, r4.phase, r5.phase], (r5.session.machine.fiber? Api.root).bind (·.exit))

-- old route, forged: every nesting is applied; the three that consume the fiber finish with
-- the string where `nat` was certified
#guard nestings.all fun x => (sessionRun x wrongChild false).map (·.1) ==
  some [.preflight, .applied, .progressed]
#guard (nestings.filter (·.name ∈ ["fiber", "prod", "option"])).all fun x =>
  (sessionRun x wrongChild false).map (·.2) == some (some (.success (.str "wrong")))
-- `awaitAll` over the forged list reports the string as an exit of a `nat` fiber
#guard (nestings.filter (·.name ∈ ["list", "snapshot"])).all fun x =>
  (sessionRun x wrongChild false).map (·.2) ==
    some (some (.success (.list [Value.exitOk (.str "wrong")])))
-- prototype route, forged: refused at submit, nothing applied
#guard nestings.all fun x => (sessionRun x wrongChild true).map (·.1) ==
  some [.refused .envelope, .refused .noCall, .progressed]
-- honest: both routes agree, and the consumers finish with 7
#guard nestings.all fun x => sessionRun x rightChild true == sessionRun x rightChild false
#guard (nestings.filter (·.name ∈ ["fiber", "prod", "option"])).all fun x =>
  (sessionRun x rightChild true).map (·.2) == some (some (.success (.nat 7)))

end Nested

/-! ## 3. Forks under binders: the environment at the site matters

`siteDecl` types a fork's body in the environment the checker reaches the site with. The path
probe's naive reading (empty environment) cannot type a body that reads a bound variable. Each
program below runs with no host; every forked fiber's recorded site is read back from the
machine and its declaration compared with the expected type. -/

section Binders

/-- The declaration the path probe used: the body typed in the empty environment. -/
def naiveSiteDecl (sig : Signature NativeOp) (root : NativeEff) (site : List Nat) : Option EffTy :=
  match Node.at_ (.eff root) site with
  | some (.action (.fork body _)) => effTy sig [] body
  | some (.action (.forkIn body _ _)) => effTy sig [] body
  | some (.action (.forkScoped body _)) => effTy sig [] body
  | some (.effs (.cons head _)) => effTy sig [] head
  | _ => none

structure Binder where
  name : String
  program : Api.Program
  /-- The expected answer column of every forked fiber, in fork order. -/
  answers : List Ty

def forkVar (i : Nat) : Api.Program := .withFiber (.fork (.succeed (.var i)) opts)

def binders : List Binder := [
  ⟨"bind", .bind (.succeed (.lit (.str "s"))) (forkVar 0), [.string]⟩,
  ⟨"catchCause", .catchCause (.fail (.lit (.nat 3))) (forkVar 0), [.causeOf .nat]⟩,
  ⟨"matchCause.value", .matchCause (.succeed (.lit (.str "v"))) (forkVar 0)
    (.succeed (.lit .unit)), [.string]⟩,
  ⟨"onExit", .bind (.onExit (.succeed (.lit (.nat 1))) (forkVar 0)) (.succeed (.lit .unit)),
    [.exitOf .nat .never]⟩,
  ⟨"gen.bindYield", .gen (.cons (.bindYield (.succeed (.lit (.nat 3))))
    (.cons (.bindYield (forkVar 0)) (.cons (.ret (.var 1)) .nil))), [.nat]⟩,
  ⟨"select.option", .select (ap "some" [.lit (.str "p")]) .option (.succeed (.lit .unit))
    (.bind (forkVar 0) (.succeed (.lit .unit))), [.string]⟩,
  ⟨"iterate", .iterate none (.lit (.nat 0)) (ap "lt" [.var 0, .lit (.nat 2)])
    (ap "succ" [.var 0]) (.var 0) (forkVar 0), [.nat, .nat]⟩,
  ⟨"scoped.forkScoped", .scoped (.withFiber (.forkScoped (.succeed (.lit (.str "x"))) opts)),
    [.string]⟩,
  -- the first entrant fails, so the second is launched too (site `[0, 0, 1]`)
  ⟨"raceAll", .withFiber (.raceAll (.cons (.fail (.lit (.nat 1)))
    (.cons (.succeed (.lit (.nat 2))) .nil))), [.never, .nat]⟩]

def runOf (b : Binder) : Api.Inspection := Api.run b.program 1000

/-- Every forked fiber of the run: its id and recorded site. -/
def forksOf (m : NativeMachine) : List (FiberId × List Nat) :=
  m.fibers.filterMap fun f =>
    match f.origin with
    | .forked _ _ site => some (f.id, site)
    | .root => none

def declsOf (b : Binder) : List (Option Ty) :=
  let m := (runOf b).machine
  (forksOf m).map fun (id, _) => (fiberDecl (nativeSignature []) b.program m id).map (·.answer)

def naiveDeclsOf (b : Binder) : List (Option Ty) :=
  (forksOf (runOf b).machine).map fun (_, site) =>
    (naiveSiteDecl (nativeSignature []) b.program site).map (·.answer)

-- every binder program checks, runs, and forks where expected
#guard binders.all fun b => Api.wellTyped b.program
-- the race's entrants are recorded at their list cells, the second one step down the spine
#guard (binders.find? (·.name == "raceAll")).map (fun b => (forksOf (runOf b).machine).map (·.2)) =
  some [[0, 0], [0, 0, 1]]
#guard binders.all fun b => (forksOf (runOf b).machine).length == b.answers.length
-- the derived declaration is the expected type at every fork
#guard binders.all fun b => declsOf b == b.answers.map some
-- the naive reading has no declaration where a bound variable is read
#guard (binders.filter (·.name ∈ ["bind", "catchCause", "matchCause.value", "onExit",
    "gen.bindYield", "select.option", "iterate"])).all fun b =>
  naiveDeclsOf b == b.answers.map fun _ => none
-- and agrees where the body is closed
#guard (binders.filter (·.name ∈ ["scoped.forkScoped", "raceAll"])).all fun b =>
  naiveDeclsOf b == declsOf b
-- every forked fiber that succeeded returned a value of its declared answer type
#guard binders.all fun b =>
  let m := (runOf b).machine
  (forksOf m).all fun (id, _) =>
    match (m.fiber? id).bind (·.exit), fiberDecl (nativeSignature []) b.program m id with
    | some (.success v), some d => fits (fiberDecl (nativeSignature []) b.program m)
        m.state.externals.allocated v d.answer
    | some (.failure _), some _ => true
    | none, some _ => true
    | _, none => false

end Binders

/-! ## 4. Red controls kept as fixtures

Each must fail exactly as recorded: the check is not vacuous. -/

section Red

/-- error: Expression
  decide (Option.map (fun x => x.snd) (newPath wrongProgram) = some (some (Exit.success (Val.str "wrong"))))
did not evaluate to `true` -/
#guard_msgs in
#guard (newPath wrongProgram).map (·.2) = some (some (.success (.str "wrong")))

/-- A registry that declares every fiber at the row's type accepts the forged reply: the
verdict rests on the derived declaration, not on the value's shape. -/
def lyingDecl : FiberId → Option EffTy := fun _ => some (EffTy.pure .nat)

#guard nestings.all fun x => (fitsAt lyingDecl [] [] x.value x.answer).isNone

/-- The naive registry refuses an honest reply naming a fiber forked under a binder: without
the site's environment the declaration is missing and read at the top. -/
def underBinder : Api.Program :=
  .bind (.succeed (.lit (.nat 5))) (.bind (forkVar 0)
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 2) .joinEffect)))

def underBinderParked : NativeMachine :=
  (Api.replay underBinder 1000 [Api.evaluate] [] table).machine

#guard Api.typeOf underBinder table = some (EffTy.pure .nat)
#guard (fiberDecl (nativeSignature table) underBinder underBinderParked ⟨1⟩).map (·.answer) =
  some .nat
#guard fitsAt (fiberDecl (nativeSignature table) underBinder underBinderParked) [] []
  (Value.fiber 1) fNat = none
#guard fitsAt (fun id => (underBinderParked.fiber? id).bind fun f =>
    match f.origin with
    | .forked _ _ site => naiveSiteDecl (nativeSignature table) underBinder site
    | .root => none) [] [] (Value.fiber 1) fNat =
  some ⟨[], .fiberDecl ⟨1⟩ none fNat⟩

end Red

end Research.Pass.FiberSlice.Live
