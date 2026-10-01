from pathlib import Path
import difflib
root = Path('/Users/pooks/Dev/lean4-effect4-slice6')
out = Path('/private/tmp/h1-candidate')
changed = []
def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'expected exactly one match, found {text.count(old)}: {old[:100]}')
    return text.replace(old, new, 1)
def save(rel, text):
    p = out / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    changed.append(rel)

rel = 'src/Effect4/Laws/Program/Guard/Core.lean'
s = (root / rel).read_text()
for old, new in [
('def taskKeys : Task EffName EffThunk Val Err Defect FiberId Ann → List GuardKey',
 'def taskKeys {Code : Type} : Task EffName EffThunk Val Err Defect FiberId Ann Code → List GuardKey'),
('def internalKeys (m : NativeMachine) : List GuardKey :=',
 'def internalKeys {Code Saved Event : Type}\n    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores Code Saved Event) :\n    List GuardKey :='),
('def InternalKeysBelow (m : NativeMachine) : Prop :=',
 'def InternalKeysBelow {Code Saved Event : Type}\n    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores Code Saved Event) : Prop :='),
('def bucketKeys (buckets : List NBucket) : List GuardKey :=',
 'def bucketKeys {Code : Type}\n    (buckets : List (Bucket EffName EffThunk Val Err Defect FiberId Ann Code)) : List GuardKey :='),
('def fiberKeys (fiber : NFiber) : List GuardKey :=',
 'def fiberKeys {Code Saved : Type}\n    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx Code Saved) : List GuardKey :='),
('def commandKeys : NCmd → List GuardKey',
 'def commandKeys {Code : Type} : Cmd EffName EffThunk Val Err Defect FiberId Ann Code → List GuardKey'),
('def ActiveAt (m : NativeMachine) (fiber : FiberId) : Prop :=',
 'def ActiveAt {Code Saved Event : Type}\n    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores Code Saved Event)\n    (fiber : FiberId) : Prop :='),
('def commandOwner (m : NativeMachine) : NCmd → Option FiberId',
 'def commandOwner {Code Saved Event : Type}\n    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores Code Saved Event) :\n    Cmd EffName EffThunk Val Err Defect FiberId Ann Code → Option FiberId'),
('def PendingShape (f : NFiber) : Prop :=',
 'def PendingShape {Code Saved : Type}\n    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx Code Saved) : Prop :=')]:
    s = replace_once(s, old, new)
save(rel, s)

# The native guard invariant includes this beside GuardQueue, not inside it.
rel = 'src/Effect4/Laws/Program/Guard/RegistrationQueue.lean'
s = (root / rel).read_text()
s = replace_once(s,
  'def RegistrationTail (command : NCmd) (rest : List NCmd) : Prop :=',
  'def RegistrationTail {Code : Type}\n    (command : Cmd EffName EffThunk Val Err Defect FiberId Ann Code)\n    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann Code)) : Prop :=')
s = replace_once(s,
  'def RegistrationQueue : List NCmd → Prop',
  'def RegistrationQueue {Code : Type} : List (Cmd EffName EffThunk Val Err Defect FiberId Ann Code) → Prop')
save(rel, s)

rel = 'src/Effect4/Laws/Program/Typed/Assembly.lean'
s = (root / rel).read_text()
s = replace_once(s, 'import Effect4.Laws.Program.Typed.State\n',
  'import Effect4.Laws.Program.Typed.State\nimport Effect4.Laws.Program.Typed.Scheduler\n')
s = replace_once(s, '''Two limits of the generated bundle are recorded rather than papered over: `PendingOk` receives
the enclosing position, not the fiber, so it can only say every pending token is declared for
some fiber; `RaceOk` says each race's host is parked at a declared token, and the race's result
type is the host's declared token type through `ResumeOk` on the resume it enqueues.''',
'''H1 adds the settled scheduler guards and observer-to-token payload connections. `PendingOk`
still receives no enclosing fiber, so `ObserverState.pendingOwner` supplies that correlation.
`RaceOk` owns every buffered race payload and finite unlaunched program. The reference code-site
scan remains explicitly OPEN (H1-RCODE-SITES); no continuation-wide approximation is claimed.
All eighteen command-preservation declarations remain obligations.''')
s = replace_once(s,
  '  RaceOk w _ races := ∀ r ∈ races, (w.Θ r.host r.token).isSome = true',
  '  RaceOk w _ races := ∀ r ∈ races, ∃ resultTy, RacePayload root w r resultTy')
a = s.index('/-- The typed state:')
b = s.index('/-- M6\'s reference runner', a)
s = s[:a] + '''/-- The active park and saved stack agree on what the declared token delivers. -/
def ActiveDelivery (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) FitsExit (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

/-- World validity, every generated typed position, active delivery, the settled native guard
conditions, and the exact observer/pending correlations. Internal key bounds live here so every
StepPreserves input/output carries them; arbitrary queues are still admitted by their own fact.
H1-RCODE-SITES is an explicit remaining condition, not an established invariant. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

/-- PendingOk supplies a declaration; WorldValid bounds all declarations. -/
theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (typed : TypedState root rootTy w m) (f : RFiber) (hf : f ∈ m.fibers)
    (p : Pending EffName Val Err Defect FiberId Ann) (hp : p ∈ f.pending) :
    p.token < m.nextToken := by
  obtain ⟨id, declared⟩ := (typed.2.1.c0 f hf).c1 p hp
  cases h : w.Θ id p.token with
  | none => rw [h] at declared; cases declared
  | some tokenTy => exact typed.1.tokenBound id p.token tokenTy h

''' + s[b:]
a = s.index('/-- The queued commands carry typed resumes.')
b = s.index('/-- One command keeps', a)
s = s[:a] + '''/-- Every queued command's generated content judgment, scheduler authority and keys, plus
observer and enrollment payload correlation. H1-RCODE-SITES remains OPEN for resume code:
there is intentionally no field claiming an unimplemented recursive reference scan. The direct
forbidden afterInterrupt race form is recorded separately and exactly. -/
structure QueueOk (root : ProgramSource) (w : World) (m : RState)
    (commands : List RCmd) : Prop where
  payload : ∀ command ∈ commands, RCmdOk (preds root) w command
  authority : ∀ command ∈ commands, CommandAuthorityR m command
  delivery : ∀ command ∈ commands, CommandDeliveryOk root w m command
  owners : (commands.filterMap (Guard.commandOwner m)).Nodup
  registration : Guard.RegistrationQueue.RegistrationQueue commands
  keys : ReservedKeysR m (commands.flatMap Guard.commandKeys)
  observer : ∀ source exit observer, .observe source exit observer ∈ commands →
    ObserverCommandOk root w m source exit observer
  enroll : ∀ race child, .enrollRace race child ∈ commands → EnrollRaceOk root w m race child
  noRaceAfterInterrupt : ∀ host yielding race,
    .afterInterrupt host yielding (.race race) ∉ commands

theorem QueueOk.fresh {root : ProgramSource} {w : World} {m : RState} {commands : List RCmd}
    (queue : QueueOk root w m commands) : QueueFresh m commands := queue.keys.below

''' + s[b:]
s = replace_once(s, 'QueueOk root w (cmd :: rest)', 'QueueOk root w m (cmd :: rest)')
s = replace_once(s, "QueueOk root w' r.2", "QueueOk root w' r.1 r.2")
save(rel,s)

# E's existing positive loaded-state builder needs precisely the new empty-state facts.
rel = 'Test/Counterexamples/Machine/Semantics/ValueMembership.lean'
s = (root / rel).read_text()
s = replace_once(s,
  '  refine ⟨initialWorld ty, initial_world_valid _ p 20 20 closed, ⟨?_, ?_, ?_⟩, ?_⟩',
  '  refine ⟨initialWorld ty, initial_world_valid _ p 20 20 closed, ⟨?_, ?_, ?_⟩,\n    ?_, schedulerState_load p 20 20, observerState_load (p : ProgramSource) _ 20 20,\n    registrationState_load (p : ProgramSource) _ 20 20 noMarker⟩')
s = replace_once(s,
  'theorem typedStateF_load (p : NativeEff) (ty : EffTy) (closed : ClosedEff ty)\n',
  'theorem typedStateF_load (p : NativeEff) (ty : EffTy) (closed : ClosedEff ty)\n    (noMarker : raceRegistrationR (denoteR p p (rootPoint 20)) = none)\n')
s = replace_once(s, 'typedStateF_load refProg _ ⟨rfl, rfl⟩ refProg_typedF',
  'typedStateF_load refProg _ ⟨rfl, rfl⟩ rfl refProg_typedF')
s = replace_once(s, 'typedStateF_load getProg _ ⟨rfl, rfl⟩ getProg_typedF',
  'typedStateF_load getProg _ ⟨rfl, rfl⟩ rfl getProg_typedF')
save(rel,s)

# The requested historical falsifiers and green controls belong in item B's existing file.
rel = 'Test/Counterexamples/Machine/Semantics/M6Capstone.lean'
s = (root / rel).read_text()
s = replace_once(s, 'import Effect4.Laws.Program.Typed.Assembly\n', 'import Effect4.Laws.Program.Typed.Assembly\nimport Effect4.Laws.Machine.Approximation\n')
s = replace_once(s, 'end Test.Counterexamples.Machine.Semantics.M6Capstone',
    (out / 'tests-fragment.lean').read_text() + '\n' + (out / 'observe-historical-fragment.lean').read_text() + '\n' + (out / 'early-historical-fragment.lean').read_text() + '\nend Test.Counterexamples.Machine.Semantics.M6Capstone')
save(rel, s)

# New module, deliberately assembled outside the repository.
changed.append('src/Effect4/Laws/Program/Typed/Scheduler.lean')
patch=[]
for rel in changed:
    before=(root/rel).read_text() if (root/rel).exists() else ''
    after=(out/rel).read_text()
    patch.extend(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),
        fromfile=('a/'+rel if (root/rel).exists() else '/dev/null'),tofile='b/'+rel))
(out/'implementation.patch').write_text(''.join(patch))
print('Prepared outside repository:', len(changed), 'files; patch bytes', len(''.join(patch)))
