import Tools.View.Program
import Tools.Code.Module
import Tools.View.Decision

/-!
# The frames of a run

Slice V2 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`). A built program
runs through its checked session (`Run`, `src/Effect4/Run/Basic.lean`), one control at a time
(`Run.controlOnce`), and each step draws one frame:

- **the program**, its lines and types, with the addresses where this step forked a fiber lit
  (`ForkRecord.site`);
- **the graph of fibers**: a node for each fiber, in the order of their identities, with its
  state; an edge from a parent to each child it forked; and an edge from a fiber to each fiber
  that waits on its exit (`Observer.resumeAwait`, `Observer.countdown`). An exit flows back to
  its waiter, so that edge is usually a back edge, routed up the right; a cycle of waits stands
  out as one.

A fiber whose state changed in the step is lit. The machine records no program address for a
running fiber (the plan's gap of V2), so the program shows where fibers were forked, not where
each one is.
-/

namespace Tools.View.Run

open Effect4 Effect4.Program Effect4.Machine Tools.View

/-- An exit in words. -/
def exitText {β ε δ ι α : Type} : Exit β ε δ ι α → String
  | .success _ => "exit: success"
  | .failure _ => "exit: failure"

/-- A fiber's state in words, from its exit, its finalizing exit, whether it runs, and its park. -/
def stateText {β ε δ ι α : Type} (exit finalizing : Option (Exit β ε δ ι α)) (running : Bool)
    (parked : Parked) : String :=
  match exit with
  | some e => exitText e
  | none =>
    if finalizing.isSome then "finalizing"
    else if running then "running"
    else match parked with
      | .withGuard _ => "parked"
      | .notParked => "suspended"

/-- The fibers that wait on a fiber's exit, from its observers. -/
def waiters (observers : List Observer) : List FiberId :=
  observers.filterMap fun
    | .resumeAwait w _ _ => some w
    | .countdown w _ => some w
    | _ => none

/-- **The graph of a machine's fibers**: one node for each fiber, in the order of their
identities; a fork edge from parent to child; an exit edge from a fiber to each of its waiters.
The fibers in `lit` are lit. -/
def fiberGraph (m : Api.Machine) (lit : List Nat) : Graph :=
  let fibers := m.fibers.mergeSort fun a b => a.id.value ≤ b.id.value
  let ids := fibers.map (·.id.value)
  let pos (id : Nat) : Option Nat := ids.findIdx? (· == id)
  let nodes := fibers.map fun f =>
    let site := (m.forks.find? (·.child == f.id)).map fun r => " · forked at " ++ Program.bracket r.site
    ({ key := s!"fiber {f.id.value}", line1 := s!"fiber {f.id.value}" ++ (site.getD ""),
       line2 := stateText f.exit f.finalizing f.running f.parked, lit := lit.contains f.id.value } : GNode)
  let forks := m.forks.filterMap fun r =>
    match pos r.parent.value, pos r.child.value with
    | some p, some c => some ({ key := s!"fork {r.parent.value} {r.child.value}", src := p, dst := c } : GEdge)
    | _, _ => none
  let exits := fibers.flatMap fun f =>
    (waiters f.observers).filterMap fun w =>
      match pos f.id.value, pos w.value with
      | some s, some d => some ({ key := s!"exit {f.id.value} {w.value}", src := s, dst := d } : GEdge)
      | _, _ => none
  { nodes := nodes.toArray, edges := (forks ++ exits).toArray }

/-- The state of each fiber, by identity, to tell which changed in a step. -/
def states (m : Api.Machine) : List (Nat × String) :=
  m.fibers.map fun f => (f.id.value, stateText f.exit f.finalizing f.running f.parked)

/-- The judgment of a run: its exit, or what is live. -/
def runText (s : Run) : String :=
  match s.exit with
  | some e => exitText e
  | none =>
    let live := (s.machine.fibers.filter (·.exit.isNone)).length
    s!"{live} {if live == 1 then "fiber" else "fibers"} live, {s.outstanding.length} calls outstanding"

/-- Static readings of this built program: source paths, checked lines and printed code.
The index prevents a preparation for another program or row table from reaching a frame. -/
structure Prepared (built : Api.Built) where
  lines : Array (List Nat × Line)
  code : Option CodePanel

/-- Read the checked source lines and code once, against the built program's exact table.
This reads source addresses, and assumes no connection to expanded call addresses. -/
def prepare (built : Api.Built) : Prepared built :=
  let session := EditSession.open (SigApp.ofTable built.table) { program := built.program }
  let page := Program.sessionPage session none "" "" "" ""
  let paths := (Program.lines built.program).map (·.path)
  { lines := (paths.zip page.lines.toList).toArray
    code := Program.codePanel built.program built.table }

/-- A planned control keeps the built program. Step of `prepared-run-view-agrees`.
Concept `initial-algebras-folds`. Consumer: `framesBuilt` retains its static readings. -/
theorem controlOnce_built (s : Run) : s.controlOnce.built = s.built := by
  unfold Effect4.Run.controlOnce
  split <;> rfl

/-- One frame reads its static lines from the preparation indexed by this run's built program.
The step's first fork site lights its descendants, as the existing frame does. -/
def framePrepared (name : String) (before : Option Run) (s : Run)
    (prepared : Prepared s.built) (what : String) : Page :=
  let oldForks := ((before.map (·.machine.forks)).getD [])
  let newForks := s.machine.forks.filter fun r => !oldForks.contains r
  let old := (before.map (states ·.machine)).getD []
  let changed := (states s.machine).filterMap fun (id, st) =>
    if old.lookup id == some st then none else some id
  let lit := newForks.head?.map (·.site)
  let lines := prepared.lines.map fun (path, line) =>
    if line.state == .refused then line
    else match lit with
      | some a => if a.isPrefixOf path then { line with state := .lit } else line
      | none => line
  { title := name ++ " · run · " ++ what
    judgment := runText s
    foot := s!"journal: {s.journal.length} rows"
    lines
    graph := some { title := "fibers", laid := (fiberGraph s.machine changed).layout }
    code := prepared.code }

/-- One frame prepares from the run itself, so no independent program can disagree with it. -/
def frame (name : String) (before : Option Run) (s : Run) (what : String) : Page :=
  framePrepared name before s (prepare s.built) what

/-- Frames of this built program, prepared once at its exact row table.
Controls retain the preparation because they retain the built program.
Host replies and clock advances remain the caller's choices. -/
def framesBuilt (name : String) (built : Api.Built) (most : Nat := 64) : List Page :=
  let s0 := Effect4.Run.open built "view"
  let prepared := prepare built
  let rec go (left : Nat) (s : Run) (cached : Prepared s.built) : List Page :=
    match left with
    | 0 => []
    | k + 1 =>
      match s.nextControl with
      | none => []
      | some d =>
        let s' := s.controlOnce
        let cached' : Prepared s'.built :=
          cast (congrArg Prepared (controlOnce_built s).symm) cached
        framePrepared name (some s) s' cached' (decisionText d) :: go k s' cached'
  let pages := framePrepared name none s0 prepared "open" :: go most s0 prepared
  let n := pages.length
  let gutter := pages.foldl (fun m g => max m (ownGutter g)) 0
  let pages := pages.map fun g => { g with gutter }
  let codeAt := pages.foldl (fun m g => max m (ownCodeAt g)) 0
  pages.zipIdx.map fun (g, i) => { g with place := s!"{i + 1} / {n}", codeAt }

/-- Frames of a program with no host row. Admission supplies the built program that binds
both the checked run and its static view. -/
def frames (name : String) (program : NativeEff) (most : Nat := 64) : Option (List Page) :=
  match Api.Author.Internal.finishBuild program {} [] with
  | .error _ => none
  | .ok built => some (framesBuilt name built most)

end Tools.View.Run
