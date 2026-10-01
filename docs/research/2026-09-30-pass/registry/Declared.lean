import registry.Core
import Test.Program.ExitTypeLane

/-! Registry seat, task 3: every fiber's declared type, derived, and every exit checked
against it.

Research evidence outside the Test root. Base `be15b062`. Finite checks, not proofs.

The runs are the exit-type lane's (`Test/Program/ExitTypeLane.lean`): every program of
`lanePrograms` under each tape of `tapes`, with the lane's host replies. The lane checks the
root's exit only (`:15-16`); here every fiber of every final machine is classified by its
recorded origin, given a declared type by the registry (`fiberDecl`, `Core.lean`), and, when it
has exited, checked two ways:

* coarse: the lane's own `fits` (`Val.hasTy` at the run's external allocations, the cause
  judgment on the error column, no bad-shape or not-implemented defect);
* deep: `fitsB` with the registry itself as the fiber declarations, so a fiber handle inside an
  exit is checked against the declaration of the fiber it names.

Red controls: four wrong registries must fail the lane, and two wrong declaration tables read
inside `fitsB` must fail the deep check. The binder forms and layer cases of `Core.lean` run
too; four of their runs fail, all at the fork inside a layer body under an outer binder, which is
layer gap 1 (`LayerGap.lean`), a runtime defect the registry exposes rather than a registry
error. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.Registry.DeclaredCheck
open Effect4 Effect4.Machine Effect4.Program Research.Pass.Registry
open Test.Program.ExitTypeLane (tapes hostReplies lanePrograms fits badDefect)
open Test.Program.TypedCorpus (Entry)

/-- What made a fiber, as the registry reads it. -/
inductive FiberClass
  | root | sourceFork | raceEntrant | layerBuild | finalizer | unrecognized
deriving DecidableEq, Repr

def FiberClass.all : List FiberClass :=
  [.root, .sourceFork, .raceEntrant, .layerBuild, .finalizer, .unrecognized]

def classify (root : NEff) (f : Api.Fiber) : FiberClass :=
  match recordOf root f.id f.origin with
  | none => .root
  | some r =>
    match r.kind, Node.at_ (.eff root) r.site with
    | .finalizer, _ => .finalizer
    | .raceEntrant, some (.effs (.cons _ _)) => .raceEntrant
    | .action, some (.action _) => .sourceFork
    | .action, some (.layer _) => .layerBuild
    | _, _ => .unrecognized

/-- The deep check: `fitsB` on the answer and inside every typed failure. -/
def fitsDeep (decl : FiberId → Option EffTy) (ty : EffTy) (allocated : List String) :
    ExitV → Bool
  | .success value => fitsB decl allocated value ty.answer
  | .failure cause =>
    causeAdmits (fun value t => fitsB decl allocated value t) ty.error cause &&
      !(cause.reasons.any (badDefect ty))

/-- How many fiber handles a value holds, at any depth (snapshots included). -/
def fiberHandles : Val → Nat
  | .handle 1 _ => 1
  | .list xs => (xs.attach.map fun ⟨x, _⟩ => fiberHandles x).sum
  | .pair a b => fiberHandles a + fiberHandles b
  | .some a => fiberHandles a
  | .ctor _ args => (args.attach.map fun ⟨x, _⟩ => fiberHandles x).sum
  | _ => 0

/-- One fiber of one final machine. -/
structure FiberVerdict where
  cls : FiberClass
  declared : Bool
  exited : Bool
  coarse : Bool
  deep : Bool
  /-- It exited with a success value holding a fiber handle: the deep check read the
  registry for that handle. -/
  handles : Bool := false

/-- How a declaration table is built for one final machine. -/
abbrev DeclBuilder := Signature NativeOp → NEff → EffTy → Api.Machine → FiberId → Option EffTy

def verdictsWith (build : DeclBuilder) (e : Entry) (rootTy : EffTy) (tape : List Api.Decision) :
    List FiberVerdict :=
  let r := Api.replay e.program 4000 tape hostReplies e.table
  let root := e.program.expandRefs
  let sig := nativeSignature e.table
  let allocated := r.machine.state.externals.allocated
  let decl := build sig root rootTy r.machine
  r.machine.fibers.map fun f =>
    let d := decl f.id
    match f.exit, d with
    | some ex, some ty =>
      let holds := match ex with | .success value => 0 < fiberHandles value | .failure _ => false
      ⟨classify root f, true, true, fits ty allocated ex, fitsDeep decl ty allocated ex, holds⟩
    | some _, none => ⟨classify root f, false, true, false, false, false⟩
    | none, _ => ⟨classify root f, d.isSome, false, true, true, false⟩

/-- The run's name, tape and fiber verdicts. -/
def runsWith (build : DeclBuilder) (entries : List Entry) :
    List (String × String × List FiberVerdict) :=
  (entries.filterMap fun e => (Api.typeOf e.program e.table).map fun ty =>
    tapes.map fun (tn, t) => (e.name, tn, verdictsWith build e ty t)).flatten

def runs (entries : List Entry) : List (String × String × List FiberVerdict) :=
  runsWith fiberDecl entries

structure Tally where
  fibers : Nat := 0
  declared : Nat := 0
  exited : Nat := 0
  coarse : Nat := 0
  deep : Nat := 0
  handles : Nat := 0
deriving Repr

def tally (vs : List FiberVerdict) : Tally :=
  vs.foldl (fun t v =>
    { fibers := t.fibers + 1
      declared := t.declared + (if v.declared then 1 else 0)
      exited := t.exited + (if v.exited then 1 else 0)
      coarse := t.coarse + (if v.exited && v.coarse then 1 else 0)
      deep := t.deep + (if v.exited && v.deep then 1 else 0)
      handles := t.handles + (if v.handles then 1 else 0) }) {}

/-- A fiber the check fails: undeclared, or exited outside its declaration. -/
def FiberVerdict.bad (v : FiberVerdict) : Bool := !v.declared || (v.exited && !(v.coarse && v.deep))

def badOf (rs : List (String × String × List FiberVerdict)) : List String :=
  rs.flatMap fun (name, tn, vs) =>
    (vs.zipIdx.filter fun (v, _) => v.bad).map fun (v, i) => s!"{name}@{tn}#fiber{i}:{repr v.cls}"

def report (entries : List Entry) : IO Unit := do
  let rs := runs entries
  let all := rs.flatMap (·.2.2)
  IO.println s!"runs: {rs.length}; fibers: {all.length}"
  for c in FiberClass.all do
    let t := tally (all.filter (·.cls == c))
    IO.println s!"  {repr c}: fibers {t.fibers}, declared {t.declared}, exited {t.exited}, coarse fits {t.coarse}, deep fits {t.deep}, exits holding a fiber handle {t.handles}"
  let bad := badOf rs
  IO.println s!"violations: {bad.length} {bad.take 20}"
  unless bad.isEmpty do throw (IO.userError "registry lane: violations")

#eval report lanePrograms

/-! ## Red controls: wrong registries must fail the same lane -/

/-- Every fiber declared at the root program's type. -/
def rootForAll : DeclBuilder := fun _ _ rootTy m id => (m.fiber? id).map fun _ => rootTy

/-- Source forks typed at the empty environment, as path B's first probe did
(`PathProbes.lean:76-92`): right only for forks under no binder. -/
def emptyEnv : DeclBuilder := fun sig root rootTy m id =>
  (m.fiber? id).bind fun f =>
    match f.origin with
    | .root => some rootTy
    | origin => (recordOf root id origin).bind fun r =>
      match r.kind, Node.at_ (.eff root) r.site with
      | .action, some (.action (.fork body _)) => (Checker.check sig [] (r.site ++ [0]) body).toOption
      | .action, some (.action (.forkIn body _ _)) => (Checker.check sig [] (r.site ++ [0]) body).toOption
      | .action, some (.action (.forkScoped body _)) =>
        (Checker.check sig [] (r.site ++ [0]) body).toOption
      | .raceEntrant, some (.effs (.cons head _)) => (Checker.check sig [] (r.site ++ [0]) head).toOption
      | _, _ => r.declared sig root

/-- Finalizer daemons declared to answer nothing. -/
def finalizerNever : DeclBuilder := fun sig root rootTy m id =>
  (m.fiber? id).bind fun f =>
    match recordOf root id f.origin with
    | some ⟨_, _, _, _, .finalizer⟩ => some ⟨.never, .never, Env.Requirement.empty⟩
    | _ => fiberDecl sig root rootTy m id

/-- Layer builds declared at the context type instead of `unknown`. -/
def layerAsContext : DeclBuilder := fun sig root rootTy m id =>
  (fiberDecl sig root rootTy m id).map fun d =>
    match (m.fiber? id).bind fun f => recordOf root id f.origin with
    | some r =>
      match r.kind, Node.at_ (.eff root) r.site with
      | .action, some (.layer _) => { d with answer := Ty.context }
      | _, _ => d
    | none => d

def controls : List (String × DeclBuilder) :=
  [("rootForAll", rootForAll), ("emptyEnv", emptyEnv), ("finalizerNever", finalizerNever),
   ("layerAsContext", layerAsContext)]

#eval show IO Unit from do
  for (name, build) in controls do
    let bad := badOf (runsWith build lanePrograms)
    IO.println s!"control {name}: {bad.length} violations, e.g. {bad.take 3}"
    if bad.isEmpty then throw (IO.userError s!"control {name} caught nothing")

/-! ## Red controls for the deep check alone

The fiber's own declaration stays right; only the declarations `fitsB` reads for the handles
inside the exit are replaced. Counted over the exits that hold a fiber handle. -/

def deepFailures (inner : (FiberId → Option EffTy) → FiberId → Option EffTy) : Nat × Nat :=
  let counts := lanePrograms.filterMap fun e => (Api.typeOf e.program e.table).map fun rootTy =>
    tapes.map fun (_, tape) =>
      let r := Api.replay e.program 4000 tape hostReplies e.table
      let root := e.program.expandRefs
      let decl := fiberDecl (nativeSignature e.table) root rootTy r.machine
      let allocated := r.machine.state.externals.allocated
      r.machine.fibers.foldl (fun (acc : Nat × Nat) (f : Api.Fiber) =>
        match f.exit, decl f.id with
        | some (Exit.success value), some ty =>
          if 0 < fiberHandles value then
            (acc.1 + 1, acc.2 + (if fitsDeep (inner decl) ty allocated (Exit.success value) then 0 else 1))
          else acc
        | _, _ => acc) (0, 0)
  (counts.flatten.foldl (fun a b => (a.1 + b.1, a.2 + b.2)) (0, 0))

#eval show IO Unit from do
  let (held, noneFail) := deepFailures fun _ _ => none
  let (_, shiftFail) := deepFailures fun decl id => decl ⟨id.value + 1⟩
  let (_, rightFail) := deepFailures id
  IO.println s!"deep controls over {held} handle-holding exits: no registry fails {noneFail}, registry read at the next id fails {shiftFail}, the registry itself fails {rightFail}"
  unless noneFail > 0 && shiftFail > 0 && rightFail == 0 do
    throw (IO.userError "deep controls")

/-! ## The binder forms and layer cases, run

Each binder form of `Core.lean` and each layer case runs under every lane tape; every fiber is
declared, and every exit fits. The binder forms also check that the innermost fork's exit fits
the expected answer, which the declaration alone would not show. -/

open Research.Pass.Registry.Fixtures in
def fixtureEntries : List Entry :=
  (binderForms.map fun (name, program, _) => ({ name := name, program := program } : Entry)) ++
    (layerCases.map fun (name, program) => ({ name := name, program := program } : Entry))

#guard fixtureEntries.all fun e => Api.wellTyped e.program e.table
-- Every fixture fiber is declared and fits, except the fork inside a layer body under an outer
-- binder: the checker binds its level 0 to `"x"`, the runtime to the outer `9` (layer gap 1,
-- `LayerGap.lean`). The registry reports the checker's type; the runtime breaks it.
#guard badOf (runs fixtureEntries) =
  ["layer.effect resets@quiet#fiber1:Research.Pass.Registry.DeclaredCheck.FiberClass.sourceFork",
   "layer.effect resets@timers#fiber1:Research.Pass.Registry.DeclaredCheck.FiberClass.sourceFork",
   "layer.effect resets@interrupt#fiber1:Research.Pass.Registry.DeclaredCheck.FiberClass.sourceFork",
   "layer.effect resets@late-interrupt#fiber1:Research.Pass.Registry.DeclaredCheck.FiberClass.sourceFork"]
-- every layer case forks a layer build that fails or succeeds inside its declaration
#guard (runs fixtureEntries).any fun (_, _, vs) =>
  vs.any fun v => v.cls == .layerBuild && v.exited
#eval show IO Unit from do
  let all := (runs fixtureEntries).flatMap (·.2.2)
  for c in FiberClass.all do
    let t := tally (all.filter (·.cls == c))
    IO.println s!"fixtures {repr c}: fibers {t.fibers}, exited {t.exited}, fit {t.deep}"

/-! ## The boundary: a host names a fiber, under a binder

The forged-handle program of the host-answers probe (`2026-09-30-host-answers-evidence/Probe.lean`
§2), with the forked program reading a binder: the registry needs `staticEnvAt` to declare it,
and with it refuses the forged handle and accepts the honest one. -/

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

/-- Bind `first`, fork a child returning it, ask the host for a fiber, join the one it names. -/
def program (first : Term) : Api.Program :=
  .bind (.succeed first)
    (.bind (.withFiber (.fork (.succeed (.var 0)) opts))
      (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 2) .joinEffect)))

def wrongProgram : Api.Program := program (.lit (.str "wrong"))
def rightProgram : Api.Program := program (.lit (.nat 7))

def parkedOf (p : Api.Program) : Api.Machine := (Api.replay p 1000 [Api.evaluate] [] table).machine

def admitWith (build : DeclBuilder) (p : Api.Program) : Bool :=
  match Api.typeOf p table with
  | none => false
  | some rootTy =>
    fitsB (build (nativeSignature table) p.expandRefs rootTy (parkedOf p)) []
      (Value.fiber 1) (.fiberOf .nat .never)

#guard Api.typeOf wrongProgram table = some (EffTy.pure .nat)
#guard Api.typeOf rightProgram table = some (EffTy.pure .nat)
#guard ((parkedOf wrongProgram).fiber? ⟨1⟩).map (·.origin) = some (.forked ⟨0⟩ true [1, 0, 0])
-- today's shape check admits both
#guard Val.hasTy (Value.fiber 1) (.fiberOf .nat .never)
-- the registry refuses the forged handle and admits the honest one
#guard admitWith fiberDecl wrongProgram = false
#guard admitWith fiberDecl rightProgram = true
-- typed at the empty environment, the child has no declaration: the honest reply is refused too
#guard admitWith emptyEnv rightProgram = false

end Research.Pass.Registry.DeclaredCheck
