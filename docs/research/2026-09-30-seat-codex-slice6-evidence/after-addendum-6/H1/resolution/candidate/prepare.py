from pathlib import Path
import difflib, hashlib, json
repo=Path('/Users/pooks/Dev/lean4-effect4-slice6')
base=repo/'docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-6/H1/checked-source'
out=Path('/private/tmp/h1-halt-resolution')
paths=['src/Effect4/Laws/Program/Guard/Core.lean','src/Effect4/Laws/Program/Guard/RegistrationQueue.lean','src/Effect4/Laws/Program/Typed/Scheduler.lean','src/Effect4/Laws/Program/Typed/Assembly.lean']
for p in paths:
    target=out/p; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes((base/p).read_bytes())
p=paths[-1]; s=(out/p).read_text()
def replace(a,b):
    global s
    assert s.count(a)==1, (a[:100],s.count(a))
    s=s.replace(a,b)
replace('import Effect4.Laws.Program.Typed.Stack\n','import Effect4.Laws.Program.Typed.Stack\nimport Effect4.Laws.Machine.Lift\n')
replace('/-- Only the current-code premise is conditional. The stack still composes to the declared\nfiber type, and interrupt provenance is required on both sides of the terminal boundary. -/', '''/-- Current code is inert after a machine halt, while its finish is queued, or after its exit
has been published. Halting does not require an empty queue: some native halt paths retain it.
Only dispatch through the command loop reads this code; raw `driveStep` requires its explicit
not-halted premise in `StepPreserves`. -/
def CodeInert (m : RState) (commands : List RCmd) (position : Expect) : Prop :=
  m.stuck.isSome = true ∨ TerminalPosition m commands position

/-- Only the current-code premise is conditional. The stack still composes to the declared
fiber type, and interrupt provenance is required even when current code is inert. -/''')
replace('∃ tin, (¬ TerminalPosition m commands position → TypedProg root w tin saved.current) ∧','∃ tin, (¬ CodeInert m commands position → TypedProg root w tin saved.current) ∧')
replace('/-- All generated data clauses are unchanged. Only saved current code is conditional on its\nqueued or published exit; queued exit typing is still the unchanged `preds.exit` in `RCmdOk`. -/', '/-- All generated data clauses are unchanged. Only saved current code is conditional on\n`CodeInert`; queued exit typing is still the unchanged `preds.exit` in `RCmdOk`. -/')
replace('/-- One command keeps the typed state and the queue typed, at some later world. -/','''/-- One dispatched command keeps the typed state and queue typed at some later world.
The exact `m.stuck = none` dispatch premise is shared with `Machine.Lift.StepKeeps` and
`driveState`; it does not assert reachability or constrain the pending suffix. -/''')
replace('∀ w m rest, TypedState root rootTy w m (cmd :: rest) → QueueOk root w m (cmd :: rest) →','∀ w m rest, m.stuck = none → TypedState root rootTy w m (cmd :: rest) →\n    QueueOk root w m (cmd :: rest) →')
replace('/-! ## The capture lookup -/', '''/-- The eighteen command facts, once proved, provide exactly the existing generic loop
premise. This adapter proves no individual command fact and requires no reachability premise. -/
theorem stepKeeps_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command) :
    letI := termEvaluatorFor root.program
    Machine.Lift.StepKeeps hostOrder (interpR root.program)
      (fun w m commands => TypedState root rootTy w m commands ∧ QueueOk root w m commands) := by
  letI := termEvaluatorFor root.program
  intro w m command rest running typed
  exact steps command w m rest running typed.1 typed.2

/-- Conditional assembly lift through the actual command loop, including its halt boundary.
All eighteen `StepPreserves` facts remain hypotheses, not discharged obligations. -/
theorem driveState_typed_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command)
    (fuel : Nat) (w : World) (m : RState) (commands : List RCmd)
    (typed : TypedState root rootTy w m commands) (queue : QueueOk root w m commands) :
    letI := termEvaluatorFor root.program
    let result := driveState (interpR root.program) fuel m commands
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' result.1 result.2 ∧
      QueueOk root w' result.1 result.2 := by
  letI := termEvaluatorFor root.program
  exact Machine.Lift.driveState_lift hostOrder (interpR root.program)
    (fun w m commands => TypedState root rootTy w m commands ∧ QueueOk root w m commands)
    (stepKeeps_of_stepPreserves root rootTy steps) fuel w m commands ⟨typed, queue⟩

/-! ## The capture lookup -/''')
(out/p).write_text(s)
patch=[]; manifest=[]
for p in paths:
    old=(repo/p).read_text() if (repo/p).exists() else ''
    new=(out/p).read_text()
    patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p if old else '/dev/null',tofile='b/'+p))
    manifest.append({'path':p,'checked_source_sha256':hashlib.sha256((base/p).read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256((out/p).read_bytes()).hexdigest(),'live_sha256':hashlib.sha256((repo/p).read_bytes()).hexdigest() if (repo/p).exists() else None})
(out/'source.patch').write_text(''.join(patch))
(out/'source-map.json').write_text(json.dumps(manifest,indent=2)+'\n')
