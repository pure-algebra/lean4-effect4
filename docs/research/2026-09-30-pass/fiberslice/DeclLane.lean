import Research.Pass.FiberSlice.Core
import Test.Program.ExitTypeLane
import Effect4.Program.Binders

/-! The declaration lane: every forked fiber of the exit-type lane's runs against its derived
declaration. `Test/Program/ExitTypeLane.lean` checks each run's root exit against the program's
checked type and says it does not look at forked fibers (`:14-15`). This lane reruns the same
programs under the same tapes and host replies and checks every fiber the run forked:
- a fork with a source site has a derived declaration (`fiberDecl`);
- a fork that exited with a success returned a value that fits its declaration, with the
  registry itself reading nested fiber handles (`fits`);
- a fork that failed has only typed failures its declared error admits (`causeAdmits`).
Forks the runtime makes for its own work are counted apart, by the node at their recorded site:
finalizer forks and races without a source Point record `[]` (`Machine/Fibers.lean:969`,
`:1864`); a layer build forked by `merge`/`mergeAll` records the layer's own path
(`Program/Compile.lean:1450-1455`), which names a layer node, never a fork or a race cell.
Finite evidence over a named corpus, not a proof. Research evidence, outside the Test root. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.FiberSlice.DeclLane
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice
open Test.Program.ExitTypeLane Test.Program.TypedCorpus

structure Tally where
  runs : Nat := 0
  forks : Nat := 0
  declared : Nat := 0
  noSite : Nat := 0
  layerBuilds : Nat := 0
  exited : Nat := 0
  violations : List String := []

/-- A site whose node is a source fork: a fork action or a race's list cell. -/
def sourceSite (root : NativeEff) (site : List Nat) : Bool :=
  match Node.at_ (.eff root.expandRefs) site with
  | some (.action (.fork _ _)) | some (.action (.forkIn _ _ _))
  | some (.action (.forkScoped _ _)) | some (.effs (.cons _ _)) => true
  | _ => false

/-- A site whose node is a layer: a layer build `merge`/`mergeAll` forked. -/
def layerSite (root : NativeEff) (site : List Nat) : Bool :=
  match Node.at_ (.eff root.expandRefs) site with
  | some (.layer _) => true
  | _ => false

/-- One run's forks against their declarations. -/
def checkRun (e : Entry) (tapeName : String) (tape : List Api.Decision) (t : Tally) : Tally :=
  let r := Api.replay e.program 4000 tape hostReplies e.table
  let m := r.machine
  let sig := nativeSignature e.table
  let decl := fiberDecl sig e.program m
  let allocated := m.state.externals.allocated
  m.fibers.foldl (init := { t with runs := t.runs + 1 }) fun t f =>
    match f.origin with
    | .root => t
    | .forked _ _ site =>
      let t := { t with forks := t.forks + 1 }
      match siteDecl sig e.program site with
      | none =>
        -- only a fork the runtime made for its own work may lack a declaration
        if site.isEmpty then { t with noSite := t.noSite + 1 }
        else if layerSite e.program site then { t with layerBuilds := t.layerBuilds + 1 }
        else { t with violations := (e.name ++ "@" ++ tapeName ++ ": no declaration at a source site") :: t.violations }
      | some d =>
        -- a declaration is read only at a source fork
        let t := if sourceSite e.program site then t
          else { t with violations := (e.name ++ "@" ++ tapeName ++ ": declaration off a source site") :: t.violations }
        let t := { t with declared := t.declared + 1 }
        match f.exit with
        | none => t
        | some (.success v) =>
          if fits decl allocated v d.answer then { t with exited := t.exited + 1 }
          else { t with violations := (e.name ++ "@" ++ tapeName ++ ": success outside declaration") :: t.violations }
        | some (.failure c) =>
          if causeAdmits (fun v ty => Val.hasTy v ty allocated) d.error c then { t with exited := t.exited + 1 }
          else { t with violations := (e.name ++ "@" ++ tapeName ++ ": failure outside declaration") :: t.violations }

/-- The binder level of the node at a path, from the generated binder table
(`Node.childLevel`, `Program/Binders.lean`, cut from `tools/Effect4Gen/binders.json`). -/
def levelAt : Node NativeOp → Nat → List Nat → Option Nat
  | _, n, [] => some n
  | node, n, i :: rest =>
    match node.child i with
    | some c => levelAt c (Node.childLevel n node i) rest
    | none => none

/-- `envAt` extends the environment exactly where the generated binder table says, at every
source fork site the lane reaches: its length is the site's binder level. -/
def arityAgrees (e : Entry) : Bool :=
  let r := Api.replay e.program 4000 [Api.evaluate, Api.flush] hostReplies e.table
  let root := e.program.expandRefs
  r.machine.fibers.all fun f =>
    match f.origin with
    | .forked _ _ site =>
      if sourceSite e.program site then
        (envAt (nativeSignature e.table) (.eff root) [] site).map List.length ==
          levelAt (.eff root) 0 site
      else true
    | .root => true

def lane : Tally :=
  lanePrograms.foldl (init := {}) fun t e =>
    if (Api.typeOf e.program e.table).isNone then t
    else tapes.foldl (init := t) fun t (tn, tape) => checkRun e tn tape t

#eval show IO Unit from do
  let t := lane
  unless t.violations.isEmpty do
    throw (IO.userError s!"declaration lane: violations {t.violations.take 20}")
  unless t.declared > 0 do throw (IO.userError "declaration lane: no declared fork was checked")
  IO.println s!"declaration lane: {lanePrograms.length} programs, {t.runs} runs, {t.forks} forks: {t.declared} source forks with a declaration, {t.layerBuilds} layer builds, {t.noSite} with no site; {t.exited} exited source forks checked, 0 violations"

#guard lanePrograms.all fun e => (Api.typeOf e.program e.table).isNone || arityAgrees e

/-! ## Control: a wrong declaration is caught

The same lane with every declaration's answer replaced by `never` must report violations (a
fork that succeeded cannot fit `never`). -/

def checkRunWrong (e : Entry) (tape : List Api.Decision) : Nat :=
  let r := Api.replay e.program 4000 tape hostReplies e.table
  let m := r.machine
  m.fibers.foldl (init := 0) fun n f =>
    match f.origin, f.exit with
    | .forked _ _ site, some (.success v) =>
      match siteDecl (nativeSignature e.table) e.program site with
      | some _ => if Val.hasTy v .never m.state.externals.allocated then n else n + 1
      | none => n
    | _, _ => n

#guard (lanePrograms.foldl (init := 0) fun n e =>
  n + checkRunWrong e [Api.evaluate, Api.flush]) > 0

end Research.Pass.FiberSlice.DeclLane
