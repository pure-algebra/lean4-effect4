import Tools.View.Program
import Tools.Code.Module
import Effect4.Run
import Effect4.Api.Author

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

/-- A control decision in words. -/
def decisionText : Api.Decision → String
  | .fire owner => s!"fire the dispatcher of fiber {owner.value}"
  | .flush => "flush"
  | .evaluate f => s!"evaluate fiber {f.value}"
  | .yieldVerdict f v => s!"fiber {f.value} yields: {v}"
  | .answerAsync f _ _ => s!"answer fiber {f.value}"
  | .interruptFrom .. => "interrupt"
  | .installMiddleware => "install middleware"
  | .advance millis => s!"advance the clock {millis.toNat} ms"

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

/-- One frame of a run: the program with the step's fork sites lit, and the graph of fibers with
the fibers whose state changed lit. -/
def frame (name : String) (program : NativeEff) (before : Option Run) (s : Run) (what : String) :
    Page :=
  let oldForks := ((before.map (·.machine.forks)).getD [])
  let newForks := s.machine.forks.filter fun r => !oldForks.contains r
  let old := (before.map (states ·.machine)).getD []
  let changed := (states s.machine).filterMap fun (id, st) =>
    if old.lookup id == some st then none else some id
  let session := EditSession.open {} { program }
  let lit := newForks.head?.map (·.site)
  let page := Program.sessionPage session lit (name ++ " · run · " ++ what) (runText s) ""
    s!"journal: {s.journal.length} rows"
  { page with
    graph := some { title := "fibers", laid := (fiberGraph s.machine changed).layout }
    code := Program.codePanel program [] }

/-- **The frames of a run** of a program with no host row: its opening, then one frame after each
control, until no control is planned or `most` controls have run. `none` when the program is not
admitted. -/
def frames (name : String) (program : NativeEff) (most : Nat := 64) : Option (List Page) :=
  match Api.Author.Internal.finishBuild program [] [] with
  | .error _ => none
  | .ok built =>
    let s0 := Effect4.Run.open built "view"
    let rec go : Nat → Run → List Page
      | 0, _ => []
      | k + 1, s =>
        match s.nextControl with
        | none => []
        | some d =>
          let s' := s.controlOnce
          frame name program (some s) s' (decisionText d) :: go k s'
    let pages := frame name program none s0 "open" :: go most s0
    let n := pages.length
    let gutter := pages.foldl (fun m g => max m (ownGutter g)) 0
    let pages := pages.map fun g => { g with gutter }
    let codeAt := pages.foldl (fun m g => max m (ownCodeAt g)) 0
    some (pages.zipIdx.map fun (g, i) => { g with place := s!"{i + 1} / {n}", codeAt })

end Tools.View.Run
