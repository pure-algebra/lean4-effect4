from pathlib import Path
import difflib,hashlib,json,re
ROOT=Path('/Users/pooks/Dev/lean4-effect4-slice6')
BASE=ROOT/'docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/H1/candidate'
OUT=Path('/private/tmp/h1-addendum6')
paths=['src/Effect4/Laws/Program/Guard/Core.lean','src/Effect4/Laws/Program/Guard/RegistrationQueue.lean','src/Effect4/Laws/Program/Typed/Scheduler.lean','src/Effect4/Laws/Program/Typed/Assembly.lean','Test/Counterexamples/Machine/Semantics/ValueMembership.lean','Test/Counterexamples/Machine/Semantics/M6Capstone.lean']
def once(s,old,new):
 if s.count(old)!=1:raise RuntimeError((s.count(old),old[:120]))
 return s.replace(old,new,1)
for p in paths:
 text=(BASE/p).read_text()
 if p.endswith('/Assembly.lean'):
  anchor='/-- The active park and saved stack agree on what the declared token delivers. -/'
  block='''/-- A terminal fiber delivers the exit carried by its queued finish, or the exit already
published on that fiber. This finite boundary does not assert that an arbitrary queue is inert. -/
def TerminalFiber (m : RState) (commands : List RCmd) (id : FiberId) : Prop :=
  (∃ exit, .finish id exit ∈ commands) ∨
    ∃ fiber ∈ m.fibers, fiber.id = id ∧ fiber.exit.isSome = true

/-- The generated saved position retains its identity while its current code becomes inert. -/
def TerminalPosition (m : RState) (commands : List RCmd) : Expect → Prop
  | .root => TerminalFiber m commands Api.root
  | .fiber id => TerminalFiber m commands id
  | .hook _ => False

/-- Only the current-code premise is conditional. The stack still composes to the declared
fiber type, and interrupt provenance is required on both sides of the terminal boundary. -/
def SavedPosition (root : ProgramSource) (w : World) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ TerminalPosition m commands position → TypedProg root w tin saved.current) ∧
    StackAccepts (TypedProg root) FitsExit (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

/-- All generated data clauses are unchanged. Only saved current code is conditional on its
queued or published exit; queued exit typing is still the unchanged `preds.exit` in `RCmdOk`. -/
def statePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds World :=
  { preds root with SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      SavedPosition root w m commands position ty saved }

/-- A fully typed saved frame also satisfies the conditional current-code clause. -/
theorem savedPosition_of_saved (root : ProgramSource) (w : World) (m : RState)
    (commands : List RCmd) (position : Expect) (final : EffTy) (saved : RSaved)
    (typed : Contracts.SavedOk (TypedProg root) FitsExit (frameProtocols root) w final saved) :
    SavedPosition root w m commands position final saved := by
  obtain ⟨tin, code, stack, provenance⟩ := typed
  exact ⟨tin, fun _ => code, stack, provenance⟩

'''
  text=once(text,anchor,block+anchor)
  text=once(text,'def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop :=\n  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧',
   'def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)\n    (commands : List RCmd := []) : Prop :=\n  WorldValid rootTy w m ∧ RStateOk (statePreds root m commands) w m ∧')
  text=once(text,'theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)\n    (typed : TypedState root rootTy w m)',
   'theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)\n    (commands : List RCmd) (typed : TypedState root rootTy w m commands)')
  text=once(text,'∀ w m rest, TypedState root rootTy w m → QueueOk root w m (cmd :: rest) →',
   '∀ w m rest, TypedState root rootTy w m (cmd :: rest) → QueueOk root w m (cmd :: rest) →')
  text=once(text,"∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 ∧ QueueOk root w' r.1 r.2",
   "∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 r.2 ∧ QueueOk root w' r.1 r.2")
  text=once(text,'StepPreserves input/output carries them; arbitrary queues are still admitted by their own fact.',
   'StepPreserves input/output carries them. Its explicit queue controls the saved current-code\nclause; the empty queue remains the initialization and completed-run interface. Arbitrary queues\nare still admitted by their own fact, including generated typing for every carried finish.')
 if p.endswith('/ValueMembership.lean'):
  text=once(text,'      exact ⟨ty, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩',
   '      apply savedPosition_of_saved\n      exact ⟨ty, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩')
 if p.endswith('/M6Capstone.lean'):
  text=once(text,'      exact ⟨resultTy, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩',
   '      apply savedPosition_of_saved\n      exact ⟨resultTy, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩')
 dest=OUT/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text)
print('Prepared six candidate paths under',OUT,'without running Lean or writing the repository.')
