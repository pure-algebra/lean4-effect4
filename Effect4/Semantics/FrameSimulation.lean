import Effects.Family
import Effects.Trace
import Effect4.Runtime.Runtime
import Effect4.Semantics.Denotation

/-!
# Semantics.FrameSimulation

Owner: the simulation between `Effects.interpret` and the rc.112 frame machine,
on the fragment a first-order flow signature can reach.

Packet D4 of `docs/research/2026-09-03-reification-plan.md`, specified in
`docs/research/2026-09-03-frame-simulation.md`. Fence A is in
`Effect4/Runtime/Runtime.lean`; this is fence B.

## What the theorem says, and what it does not

`compile_simulates` says: for a program `p` over a monomorphic first-order
signature, a handler `H` into `ExceptT (Cause Val Unit Unit Unit) (StateT St Id)`,
an answer tape that *is* what `H` answers along the run (`answersOf H p s0`), and
any fuel at or above `bound tape`, the frame machine started on `compile 0 p`
finishes with exactly the exit `interpret H p` computes.

The answers are **supplied, not computed**. `PrimInterp` is a record of pure
total functions (`Effect4/Runtime/Runtime.lean`), so the machine has nowhere to
put a handler's monad; the tape is the oracle. The content of the theorem is
therefore that the machine's *control flow* — which continuation runs, in which
order, with which exit — equals the algebra's, given agreeing answers. Anyone
reading it as "the frame machine computes `interpret`" is over-reading it. It is
the standard statement of a simulation modulo an effect oracle.

## The fragment, and what it excludes

`Program` has `pure` and `vis` and no bracket former, and `Handler.handle` takes
an operation and never a subcomputation. So `compile` emits exactly
`Prim.success` and `Prim.onSuccess (Prim.sync i) i`, and the continuation table
emits `Prim.success` and `Prim.failure`. `inFragment` is that closed shape, and
`compile_inFragment` / `tapeContA_inFragment` prove the compiled program and
every table answer stay inside it.

`onFailure`, `onSuccessAndFailure` and `onExit` are inside the *declared*
fragment of the packet but are **not reachable from `Program`**: there is no
algebraic former that compiles to them. `setInterruptible` appears only as the
frame `onExit`'s `ensure` pushes, and since no `onExit` is emitted it never
appears at all — which also means `FrameFiber.step_setInterruptible_not_evaluable`
(a `SetInterruptible` stepped as the current effect is a defect) is never
reached. `suspend`, `withFiber`, `yieldableError`, `iterator`, `exitFrame` and
`whileLoop` are outside by construction, and the mask combinators are never
entered because the machine never leaves `interruptible = true` with
`interruptedCause = none` (fence A).

## Two deviations from the research packet, recorded rather than hidden

1. **The tape carries outcomes, not bare answers.** The packet writes
   `tape : List Val`. That statement is *false*: a handler may fail at an
   operation, and a bare `List Val` cannot say where, so the machine has no way
   to fail and the two sides disagree on every failing run. `Answer` is the
   two-constructor outcome alphabet (`ok`, `failed`) and `Tape := List Answer`.
2. **`bound` is a function of the tape, not of the program.** The packet writes
   `bound p` with "the sup over the taken branch, discharged along the tape". The
   taken branch *is* the tape, so `bound tape = 2 * tape.length + 1` — two steps
   per performed operation and one to yield the exit. Under `hOracle` this is
   `bound (answersOf H p s0)`, which is a function of `p`, `H` and `s0`.

Empty annotations (`docs/research/2026-09-03-frame-simulation.md` section 5(b))
are **not** a hypothesis here and are not needed: the risk it names is
`Cause.combine`'s dedup of `Reason`s that differ only in their
`ReasonAnnotations`, and `Cause.combine` is reachable only through
`Exit.restoreAfterFinalizer` on an `onExit` arm, which this fragment never emits.
It stays a live hypothesis for the finalizer half.

## Dependency direction

This module sits **above** both `Effect4/Semantics/*` and
`Effect4/Runtime/Runtime.lean`: it imports the frame machine, which
`docs/ARCHITECTURE.md` places above Semantics. No other module under
`Effect4/Semantics/` imports it, so the established Runtime -> Semantics edge is
not reversed for any existing module, but the placement is a live ownership
question: if the merge prefers strict directory layering the module moves to
`Effect4/Runtime/FrameSimulation.lean` unchanged. Recorded in
`docs/FRAMES-DAG.md` and `test/contracts/frame-simulation.contract.md`.
-/

namespace Effect4.FrameSimulation

open Effects
open Effects.Trace (Val)

/-! ## The fragment's carriers

`ν := Nat` is a continuation-table index and `σ := Nat` an answer-tape
occurrence number, exactly as `docs/FRAMES-DAG.md` separation 4 demands: a
continuation is a *name*. The trap the separation exists to forbid is
`ν := Σ op, (S.Answer op -> Program S Val)`, which elaborates fine and silently
drops `DecidableEq` from `Prim ν ...`, turning every `frame-arm` census row from
a statement about frames into a statement about Lean functions. The `example`s
below are the gate: they fail to elaborate if the name alphabet is ever
instantiated at a function type. -/

/-- The fragment's cause carrier: user errors are `Val`, and defects, fiber ids
and annotations are `Unit`. -/
abbrev Err := Effect4.Cause Val Unit Unit Unit

/-- The fragment's exit carrier. -/
abbrev Res := Effect4.Exit Val Val Unit Unit Unit

/-- The compiled first-order program. -/
abbrev Code := Effect4.Prim Nat Nat Val Val Unit Unit Unit

/-- The frame machine at the fragment's instantiation. -/
abbrev Machine := Effect4.FrameFiber Nat Nat Val Val Unit Unit Unit

/-- The continuation table: the externally supplied meaning of every name. It
carries no `DecidableEq` and never enters `Code` or `Machine`. -/
abbrev Table := Effect4.PrimInterp Nat Nat Val Val Unit Unit Unit

/-- The algebra-side carrier that matches `Exit`: the error is a `Cause`, and the
state survives the failure. -/
abbrev Target (St : Type) := ExceptT Err (StateT St Id)

/-- Separation-4 gate: the compiled output keeps decidable equality. This fails
to elaborate if `ν` or `σ` is ever instantiated at a function type. -/
example : DecidableEq Code := inferInstance

/-- Separation-4 gate, for the machine state as well. -/
example : DecidableEq Machine := inferInstance

/-! ## The exit bijection -/

/-- The algebra's `Except` outcome as an `Exit`. -/
def exitOf {β : Type} {ε δ ι α : Type} : Except (Effect4.Cause ε δ ι α) β → Effect4.Exit β ε δ ι α
  | .ok value => Effect4.Exit.success value
  | .error cause => Effect4.Exit.failure cause

/-- An `Exit` as the algebra's `Except` outcome. -/
def exceptOf {β : Type} {ε δ ι α : Type} : Effect4.Exit β ε δ ι α → Except (Effect4.Cause ε δ ι α) β
  | Effect4.Exit.success value => .ok value
  | Effect4.Exit.failure cause => .error cause

/-- `exitOf` is injective on the nose. -/
theorem exceptOf_exitOf {β : Type} {ε δ ι α : Type}
    (outcome : Except (Effect4.Cause ε δ ι α) β) : exceptOf (exitOf outcome) = outcome := by
  cases outcome <;> rfl

/-- ... and surjective on the nose: the two carriers are the same data. -/
theorem exitOf_exceptOf {β : Type} {ε δ ι α : Type} (exit : Effect4.Exit β ε δ ι α) :
    exitOf (exceptOf exit) = exit := by
  cases exit <;> rfl

/-! ## The answer tape -/

/-- One entry of the answer tape: what the handler did at one performed
operation. The packet's `List Val` cannot express `failed`, and without it the
theorem is false on every failing run. -/
inductive Answer where
  /-- The handler answered. -/
  | ok (value : Val)
  /-- The handler failed, and no further operation runs. -/
  | failed (cause : Err)
deriving DecidableEq

/-- The oracle: one entry per performed operation, in order. -/
abbrev Tape := List Answer

/-- The value an entry carries; a failure carries none, and `residual` never
reads past one. -/
def Answer.value : Answer -> Val
  | Answer.ok value => value
  | Answer.failed _ => Val.unit

/-- The fuel a compiled program needs: two machine steps per performed operation
(push the `OnSuccess` frame, then run the `Sync` and pop it) and one to yield the
exit. DB-04 forbids the `forall fuel` form, so every statement below is
`bound tape <= fuel`. -/
def bound (tape : Tape) : Nat := 2 * tape.length + 1

section
variable {Ty : Type} {a : FlowAlphabet.{0, 0} Ty} {St : Type}

/-- The answers the handler gives along the run, in order, ending at the first
failure. This is the second structural recursion over `p`; `interpret` is the
first. -/
def answersOf (H : Handler (Flow.Sig a) (Target St)) :
    Program (Flow.Sig a) Val -> St -> Tape
  | .pure _, _ => []
  | .vis op k, s =>
    match (H.handle op).run.run s with
    | (.error cause, _) => [Answer.failed cause]
    | (.ok value, s') => Answer.ok value :: answersOf H (k value) s'

/-- The compilation. It is a plain structural recursion and depends on nothing
but the occurrence counter: `pure` is the exit, and a performed operation is the
`Sync` that reads the tape under the `OnSuccess` frame that names its
continuation. -/
def compile (i : Nat) : Program (Flow.Sig a) Val -> Code
  | .pure value => Effect4.Prim.success value
  | .vis _ _ => Effect4.Prim.onSuccess (Effect4.Prim.sync i) i

/-- The program that is left after a tape prefix has been answered. This is what
makes the continuation table a *table*: name `i` is the `i`-th occurrence, and
`residual root (tape.take i)` is the program it continues. -/
def residual : Program (Flow.Sig a) Val -> Tape -> Program (Flow.Sig a) Val
  | p, [] => p
  | .pure value, _ :: _ => .pure value
  | .vis _ k, entry :: rest => residual (k entry.value) rest

/-- The value the `i`-th `Sync` thunk produces. -/
def tapeSyncValue (tape : Tape) (i : Nat) : Val :=
  match tape[i]? with
  | some (Answer.ok value) => value
  | _ => Val.unit

/-- The `i`-th entry of the continuation table. A failed occurrence answers with
the cause; otherwise the residual program's continuation is applied to the
answer and compiled at the next occurrence. -/
def tapeContA (root : Program (Flow.Sig a) Val) (tape : Tape) (i : Nat) (value : Val) : Code :=
  match tape[i]? with
  | some (Answer.failed cause) => Effect4.Prim.failure cause
  | _ =>
    match residual root (tape.take i) with
    | .vis _ k => compile (i + 1) (k value)
    | .pure result => Effect4.Prim.success result

/-- The externally supplied meaning of every name, for one program and one tape.
Only `contA` and `syncValue` are reachable: `compile_inFragment` and
`tapeContA_inFragment` say the machine never steps a primitive that consults any
other field, so the inert fillers below are never observed. -/
def tapeInterp (root : Program (Flow.Sig a) Val) (tape : Tape) : Table where
  contA := tapeContA root tape
  contE := fun _ cause => Effect4.Prim.failure cause
  syncValue := tapeSyncValue tape
  suspendBody := fun _ => Effect4.Prim.failure Effect4.Cause.empty
  finalizerExit := fun _ _ => Effect4.Exit.success ()
  reifyExit := fun _ => Val.unit
  iterNext := fun _ _ => ([], Effect4.IterStep.done Val.unit)
  loopTest := fun _ _ => false
  loopBody := fun _ _ => Effect4.Prim.failure Effect4.Cause.empty
  loopStep := fun _ value => value
  loopDone := fun _ => Val.unit
  notImplemented := ()

end

/-! ## The fragment is closed -/

/-- The four shapes the compilation and its table can produce. Everything else —
`suspend`, `withFiber`, `yieldableError`, `iterator`, `exitFrame`, `onFailure`,
`onSuccessAndFailure`, `onExit`, `setInterruptible`, `whileLoop` — is refused. -/
def inFragment : Code -> Bool
  | Effect4.Prim.success _ => true
  | Effect4.Prim.failure _ => true
  | Effect4.Prim.sync _ => true
  | Effect4.Prim.onSuccess body _ => inFragment body
  | _ => false

section
variable {Ty : Type} {a : FlowAlphabet.{0, 0} Ty} {St : Type}

/-- The compilation lands in the fragment. -/
theorem compile_inFragment (i : Nat) (p : Program (Flow.Sig a) Val) :
    inFragment (compile i p) = true := by
  cases p <;> rfl

/-- Every table answer lands in the fragment, so no step of a compiled run ever
reaches a primitive outside it. -/
theorem tapeContA_inFragment (root : Program (Flow.Sig a) Val) (tape : Tape) (i : Nat)
    (value : Val) : inFragment (tapeContA root tape i value) = true := by
  unfold tapeContA
  split
  · rfl
  · split
    · exact compile_inFragment (i + 1) _
    · rfl

end

/-! ## Two fuel corollaries of fence A, in the `.fst` form the induction wants -/

private theorem run_step_fst (interp : Table) (self mid : Machine) (fuel : Nat)
    (h : (self.step interp).fst = Effect4.FrameStep.running mid) :
    (self.run interp (fuel + 1)).fst = (mid.run interp fuel).fst := by
  have hpair : self.step interp = (Effect4.FrameStep.running mid, (self.step interp).snd) := by
    rw [← h]
  rw [Effect4.FrameFiber.run_succ_running interp self mid fuel _ hpair]

private theorem run_add_running_fst (interp : Table) (self mid : Machine) (m n : Nat)
    (h : (self.run interp m).fst = Effect4.FrameStep.running mid) :
    (self.run interp (m + n)).fst = (mid.run interp n).fst := by
  have hpair : self.run interp m = (Effect4.FrameStep.running mid, (self.run interp m).snd) := by
    rw [← h]
  rw [Effect4.FrameFiber.run_add_running interp self mid m n _ hpair]

private theorem run_mono_fst (interp : Table) (self : Machine) (m n : Nat) (exit : Res)
    (hle : m <= n) (h : (self.run interp m).fst = Effect4.FrameStep.finished exit) :
    (self.run interp n).fst = Effect4.FrameStep.finished exit := by
  have hpair : self.run interp m = (Effect4.FrameStep.finished exit, (self.run interp m).snd) := by
    rw [← h]
  rw [Effect4.FrameFiber.run_mono interp self m n exit _ hle hpair]

/-! ## The two machine transitions the compiled shape uses

Both hold by `rfl`: the compiled shape leaves nothing for the interrupt half of
the machine to do, which is fence A's `step_preserves_uninterrupted` made
concrete on this fragment. -/

/-- Step one: the `OnSuccess` frame pushes itself and the `Sync` becomes
current. -/
theorem step_push (interp : Table) (i : Nat) (stack : List Code) (flag : Bool) :
    (Effect4.FrameFiber.mk (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i) stack flag none
        false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (Effect4.Prim.sync i)
          (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i :: stack) flag none false),
        [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i)]) := rfl

/-- Step two: the `Sync` produces the tape's answer, the pop finds the frame it
just pushed, and the named continuation becomes current under the original
stack. -/
theorem step_answer (interp : Table) (i : Nat) (stack : List Code) (flag : Bool) :
    ((Effect4.FrameFiber.mk (Effect4.Prim.sync i)
        (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i :: stack) flag none false).step
      interp).fst =
      Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contA i (interp.syncValue i)) stack flag none false) := rfl

/-! ## The algebra side -/

section
variable {Ty : Type} {a : FlowAlphabet.{0, 0} Ty} {St : Type}

/-- A pure program returns without touching the state. -/
theorem interpret_pure {E : Type} (H : Handler (Flow.Sig a) (ExceptT E (StateT St Id)))
    (value : Val) (s : St) :
    ((interpret H (Program.pure value)).run.run s) = (Except.ok value, s) := rfl

/-- One performed operation: the handler's failure is the run's failure, and its
answer feeds the continuation at the state it left. -/
theorem interpret_vis {E : Type} (H : Handler (Flow.Sig a) (ExceptT E (StateT St Id)))
    (op : (Flow.Sig a).Op)
    (k : (Flow.Sig a).Answer op -> Program (Flow.Sig a) Val) (s : St) :
    ((interpret H (Program.vis op k)).run.run s) =
      (match (H.handle op).run.run s with
        | (.error cause, s') => (Except.error cause, s')
        | (.ok value, s') => (interpret H (k value)).run.run s') := by
  show ((H.handle op >>= fun answer => interpret H (k answer)).run.run s) = _
  cases hx : (ExceptT.run (H.handle op)).run s with
  | mk outcome s' =>
    simp only [ExceptT.run, StateT.run] at hx
    cases outcome with
    | error cause =>
      simp [ExceptT.run, ExceptT.bind, ExceptT.mk, bind, StateT.run, StateT.bind,
        ExceptT.bindCont, pure, StateT.pure, hx]
    | ok value =>
      simp [ExceptT.run, ExceptT.bind, ExceptT.mk, bind, StateT.run, StateT.bind,
        ExceptT.bindCont, hx]

/-! ## Tape and residual bookkeeping -/

/-- Extending an answered prefix by one entry applies the residual program's
continuation to it. -/
theorem residual_append :
    forall (p : Program (Flow.Sig a) Val) (prefix' : Tape) (entry : Answer),
      residual p (prefix' ++ [entry]) =
        (match residual p prefix' with
          | .pure result => Program.pure result
          | .vis _ k => k entry.value) := by
  intro p prefix'
  induction prefix' generalizing p with
  | nil => intro entry; cases p <;> simp [residual]
  | cons head rest ih =>
    intro entry
    cases p with
    | pure result => simp [residual]
    | vis op k =>
      simp only [List.cons_append, residual]
      exact ih (k head.value) entry

end

private theorem drop_cons (tape : Tape) (i : Nat) (entry : Answer) (rest : Tape)
    (h : tape.drop i = entry :: rest) :
    tape[i]? = some entry /\ tape.drop (i + 1) = rest /\ i < tape.length := by
  refine ⟨?_, ?_, ?_⟩
  · have hgi : (tape.drop i)[0]? = tape[i + 0]? := List.getElem?_drop
    rw [h, Nat.add_zero] at hgi
    exact hgi.symm
  · have : (tape.drop i).drop 1 = tape.drop (i + 1) := by
      simp [List.drop_drop]
    rw [← this, h]
    rfl
  · cases Nat.lt_or_ge i tape.length with
    | inl hlt => exact hlt
    | inr hge =>
      rw [List.drop_eq_nil_of_le hge] at h
      simp at h

private theorem take_succ_of_get (tape : Tape) (i : Nat) (entry : Answer)
    (h : tape[i]? = some entry) : tape.take (i + 1) = tape.take i ++ [entry] := by
  rw [List.take_add_one, h]
  rfl

/-! ## The workhorse

A compiled program under an *arbitrary* stack suffix runs to its own exit in
`2 * (its own tape).length` steps and leaves the suffix untouched. The suffix is
what makes it an induction: the recursive call happens under the very same
stack, because the `OnSuccess` frame that the compiled operation pushes is the
only frame the compiled program ever adds and the pop that answers it removes it
again. -/

section
variable {Ty : Type} {a : FlowAlphabet.{0, 0} Ty} {St : Type}

theorem run_in_context (H : Handler (Flow.Sig a) (Target St))
    (root : Program (Flow.Sig a) Val) (tape : Tape) :
    forall (q : Program (Flow.Sig a) Val) (i : Nat) (s : St) (stack : List Code) (flag : Bool),
      residual root (tape.take i) = q ->
        tape.drop i = answersOf H q s ->
          ((Effect4.FrameFiber.mk (compile i q) stack flag none false).run (tapeInterp root tape)
              (2 * (answersOf H q s).length)).fst =
            Effect4.FrameStep.running
              (Effect4.FrameFiber.mk
                (Effect4.Prim.ofExit (exitOf ((interpret H q).run.run s).1)) stack flag none
                false) := by
  intro q
  induction q with
  | pure value => intro i s stack flag _ _; rfl
  | vis op k ih =>
    intro i s stack flag hres hsuf
    cases hx : (ExceptT.run (H.handle op)).run s with
    | mk outcome s' =>
      cases outcome with
      | error cause =>
        have hans : answersOf H (Program.vis op k) s = [Answer.failed cause] := by
          simp only [answersOf, hx]
        have hexit : ((interpret H (Program.vis op k)).run.run s).1 = Except.error cause := by
          rw [interpret_vis H op k s, hx]
        obtain ⟨hidx, _, _⟩ := drop_cons tape i (Answer.failed cause) [] (by rw [hsuf, hans])
        rw [hans, hexit]
        show ((Effect4.FrameFiber.mk (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i) stack flag
          none false).run (tapeInterp root tape) 2).fst = _
        rw [show (2 : Nat) = 0 + 1 + 1 from rfl,
          run_step_fst _ _ _ _ (congrArg Prod.fst (step_push (tapeInterp root tape) i stack flag)),
          run_step_fst _ _ _ _ (step_answer (tapeInterp root tape) i stack flag),
          Effect4.FrameFiber.run_zero]
        simp only [tapeInterp, tapeContA, tapeSyncValue, hidx, exitOf, Effect4.Prim.ofExit]
      | ok value =>
        have hans : answersOf H (Program.vis op k) s =
            Answer.ok value :: answersOf H (k value) s' := by
          simp only [answersOf, hx]
        have hexit : (interpret H (Program.vis op k)).run.run s =
            (interpret H (k value)).run.run s' := by
          rw [interpret_vis H op k s, hx]
        obtain ⟨hidx, hdrop, hlt⟩ :=
          drop_cons tape i (Answer.ok value) (answersOf H (k value) s') (by rw [hsuf, hans])
        have hres' : residual root (tape.take (i + 1)) = k value := by
          rw [take_succ_of_get tape i (Answer.ok value) hidx, residual_append, hres]
          rfl
        rw [hans, hexit]
        show ((Effect4.FrameFiber.mk (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i) stack flag
          none false).run (tapeInterp root tape)
            (2 * (Answer.ok value :: answersOf H (k value) s').length)).fst = _
        rw [show 2 * (Answer.ok value :: answersOf H (k value) s').length =
              2 * (answersOf H (k value) s').length + 1 + 1 by
            simp [List.length_cons]; omega,
          run_step_fst _ _ _ _ (congrArg Prod.fst (step_push (tapeInterp root tape) i stack flag)),
          run_step_fst _ _ _ _ (step_answer (tapeInterp root tape) i stack flag)]
        have hcont : (tapeInterp root tape).contA i ((tapeInterp root tape).syncValue i) =
            compile (i + 1) (k value) := by
          simp only [tapeInterp, tapeContA, tapeSyncValue, hidx, hres]
        rw [hcont]
        exact ih value (i + 1) s' stack flag hres' hdrop

/-! ## The theorem -/

/-- The frame machine simulates `interpret` on the compiled fragment, relative to
the answer tape.

`hOracle` is what makes the pure `PrimInterp` legitimate: `tape` is not any tape,
it is the one the handler produces along this run. `hfuel` is the DB-04 shape —
`forall fuel` is false, because exhausted fuel is a live frontier and not a
result, and `exists fuel` says nothing.

What this establishes: the machine's control flow equals the algebra's, and the
exit it yields is the exit `interpret` computes. What it does not establish: that
the machine computes the answers (it is handed them), anything about the host,
anything about interruption or concurrency (fence A proves the interrupt half is
inert here, which is not the same as modelling it), and anything about
finalizers, which `Program` cannot express. -/
theorem compile_simulates (H : Handler (Flow.Sig a) (Target St))
    (p : Program (Flow.Sig a) Val) (s0 : St) (tape : Tape) (fuel : Nat)
    (hOracle : answersOf H p s0 = tape) (hfuel : bound tape <= fuel) :
    (Effect4.FrameFiber.run (tapeInterp p tape) fuel
        (Effect4.FrameFiber.start (compile 0 p))).fst =
      Effect4.FrameStep.finished (exitOf ((interpret H p).run.run s0).1) := by
  have hmain := run_in_context H p tape p 0 s0 [] true (by simp [residual]) (by rw [hOracle]; rfl)
  rw [hOracle] at hmain
  refine run_mono_fst (tapeInterp p tape) _ (bound tape) fuel _ hfuel ?_
  show (Effect4.FrameFiber.run (tapeInterp p tape) (2 * tape.length + 1)
    (Effect4.FrameFiber.mk (compile 0 p) [] true none false)).fst = _
  rw [run_add_running_fst _ _ _ (2 * tape.length) 1 hmain]
  exact congrArg Prod.fst
    (Effect4.FrameFiber.run_succ_finished (tapeInterp p tape) _ 0 _ _
      (Effect4.FrameFiber.step_ofExit_finishes (tapeInterp p tape)
        (exitOf ((interpret H p).run.run s0).1)))

end

/-! ## The `Cause.fail` specialisation -/

section
variable {Ty : Type} {a : FlowAlphabet.{0, 0} Ty} {St : Type}

/-- A handler whose error is the raw user error, lifted into a one-reason cause.
This is the shape every existing lowering uses; the theorem is stated at `Cause`
because `Cause.fail` is not a bijection — a two-reason cause has no algebra-side
preimage — and a statement at the raw error would be strictly weaker. -/
def liftFail (H : Handler (Flow.Sig a) (ExceptT Val (StateT St Id))) :
    Handler (Flow.Sig a) (Target St) :=
  ⟨fun op => ExceptT.mk (fun s =>
    match (H.handle op).run.run s with
    | (.error error, s') => (Except.error (Effect4.Cause.fail error), s')
    | (.ok value, s') => (Except.ok value, s'))⟩

/-- The lift commutes with interpretation: the state is untouched and the error
is exactly the one-reason cause. -/
theorem run_liftFail (H : Handler (Flow.Sig a) (ExceptT Val (StateT St Id))) :
    forall (p : Program (Flow.Sig a) Val) (s : St),
      (interpret (liftFail H) p).run.run s =
        (match (interpret H p).run.run s with
          | (.ok value, s') => (Except.ok value, s')
          | (.error error, s') => (Except.error (Effect4.Cause.fail error), s')) := by
  intro p
  induction p with
  | pure value => intro s; rfl
  | vis op k ih =>
    intro s
    have hlift : ((liftFail H).handle op).run.run s =
        (match (H.handle op).run.run s with
          | (.error error, s') => (Except.error (Effect4.Cause.fail error), s')
          | (.ok value, s') => (Except.ok value, s')) := rfl
    rw [interpret_vis (liftFail H) op k s, interpret_vis H op k s, hlift]
    cases (ExceptT.run (H.handle op)).run s with
    | mk outcome s' =>
      cases outcome with
      | error error => rfl
      | ok value => exact ih value s'

/-- The `Cause.fail` corollary: the same theorem stated against a handler whose
error carrier is the raw user error. -/
theorem compile_simulates_fail (H : Handler (Flow.Sig a) (ExceptT Val (StateT St Id)))
    (p : Program (Flow.Sig a) Val) (s0 : St) (tape : Tape) (fuel : Nat)
    (hOracle : answersOf (liftFail H) p s0 = tape) (hfuel : bound tape <= fuel) :
    (Effect4.FrameFiber.run (tapeInterp p tape) fuel
        (Effect4.FrameFiber.start (compile 0 p))).fst =
      Effect4.FrameStep.finished
        (match ((interpret H p).run.run s0).1 with
          | .ok value => Effect4.Exit.success value
          | .error error => Effect4.Exit.failure (Effect4.Cause.fail error)) := by
  rw [compile_simulates (liftFail H) p s0 tape fuel hOracle hfuel, run_liftFail H p s0]
  cases hraw : (interpret H p).run.run s0 with
  | mk outcome s' => cases outcome <;> rfl

end

/-! ## The finalizer half

It landed: `Effect4/Semantics/RegionSimulation.lean`. `Program` has `pure` and
`vis` and no bracket former, and `Handler.handle` takes an operation and never
a subcomputation, so nothing above can state a finalizer; against the region
runner it is statable, and that module states it — `compileRegion` compiles an
admitted region flow into the frame machine in the shape
`Effect4/Target/TypeScript/RegionLower.lean` lowers to, `unwind_failure` and
`close_success` are the machine's finalizer half, and the instances are
`Effect4Test/Semantics/RegionSimulationContract.lean`.

The divergence this note used to be blocked on is settled. Packet D2 gave the
region runner a *merged* failure list in close order
(`Effect4.Flow.closeFrame_failure_merge`), so a failing release under a failing
body no longer keeps only the first failure, and the machine's
`Cause.combine bodyCause finalizerCause` and the runner's list are related by
the projection `RegionSimulation.failuresOfCause` rather than divergent.

The empty-annotation hypothesis of
`docs/research/2026-09-03-frame-simulation.md` section 5(b) did **not** become
live with it: `Cause.combine` is `Cause.dedup` of the concatenation and `dedup`
keeps the first occurrence, so the head of a merged cause is the head of the
body's cause whatever the annotations are, and `Exit.toOutcome` reads exactly
that head (`RegionSimulation.toOutcome_combine`). It stays live only for a
statement comparing whole causes rather than their wire projection.
-/

end Effect4.FrameSimulation
