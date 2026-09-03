/-
Contract packet: `test/contracts/frame-simulation.contract.md`

Packet D4 fence B. Every public declaration of
`Effect4/Semantics/FrameSimulation.lean` is frozen by an exact
`#check (@name : proposition)` ascription, so no weaker statement satisfies this
contract. Names are written fully qualified; this module deliberately does not
`open Effect4.FrameSimulation`, so a locally shadowed spelling cannot silently
satisfy an ascription.

The second half is a worked finite probe: a two-operation counter alphabet, one
succeeding run and one failing run, checked by `#guard`. The probe is what keeps
the theorem from being read as vacuous — it exhibits a machine run that really
does three operations, and the tightness guard shows `bound` is exact rather
than merely sufficient.

Packet source: `docs/research/2026-09-03-frame-simulation.md`.
-/

import Effect4.Semantics.FrameSimulation

set_option autoImplicit false

namespace Effect4Test.Semantics.FrameSimulationContract

/-! F0: the fragment's carriers.

`ν := Nat` is a continuation-table index and `σ := Nat` an answer-tape
occurrence number. `docs/FRAMES-DAG.md` separation 4 says a continuation is a
name; the two `DecidableEq` gates below are what stops the obvious wrong
compilation, `ν := Σ op, (S.Answer op → Program S Val)`, which elaborates fine
and silently drops decidable equality from the emitted `Prim`. -/

#check (@Effect4.Flow.Sig :
  {Ty : Type} → Effects.FlowAlphabet Ty → Effects.Signature)

#check (@Effect4.FrameSimulation.Err : Type)

#check (@Effect4.FrameSimulation.Res : Type)

#check (@Effect4.FrameSimulation.Code : Type)

#check (@Effect4.FrameSimulation.Machine : Type)

#check (@Effect4.FrameSimulation.Table : Type)

#check (@Effect4.FrameSimulation.Target : Type → Type → Type)

example : DecidableEq Effect4.FrameSimulation.Code := inferInstance

example : DecidableEq Effect4.FrameSimulation.Machine := inferInstance

/-! F1: the exit bijection.

The algebra-side monad that matches `Exit` is `ExceptT (Cause ε δ ι α) M` and
not `ExceptT ε M`, because `Exit` carries a `Cause` and a `Cause` is a list of
`Reason`s. At `Cause` the map is a bijection, proved both ways below; composed
with `Cause.fail` it is not, because a two-reason cause has no algebra-side
preimage. That is why the theorem is stated at `Cause` and the raw error is a
corollary. -/

#check (@Effect4.FrameSimulation.exitOf :
  {β ε δ ι α : Type} → Except (Effect4.Cause ε δ ι α) β → Effect4.Exit β ε δ ι α)

#check (@Effect4.FrameSimulation.exceptOf :
  {β ε δ ι α : Type} → Effect4.Exit β ε δ ι α → Except (Effect4.Cause ε δ ι α) β)

#check (@Effect4.FrameSimulation.exceptOf_exitOf :
  ∀ {β ε δ ι α : Type} (outcome : Except (Effect4.Cause ε δ ι α) β),
  Effect4.FrameSimulation.exceptOf (Effect4.FrameSimulation.exitOf outcome) = outcome)

#check (@Effect4.FrameSimulation.exitOf_exceptOf :
  ∀ {β ε δ ι α : Type} (exit : Effect4.Exit β ε δ ι α),
  Effect4.FrameSimulation.exitOf (Effect4.FrameSimulation.exceptOf exit) = exit)

/-! F2: the answer tape and the fuel bound.

The research packet writes `tape : List Val`. That is not statable: a handler
may fail at an operation, a bare `List Val` cannot record where, and the machine
then has no way to fail. `Answer` is the two-constructor outcome alphabet.
`bound tape = 2 * tape.length + 1` — two steps per performed operation and one to
yield the exit — and DB-04 forbids the `∀ fuel` form, so every statement below
carries `bound tape ≤ fuel`. -/

#check (@Effect4.FrameSimulation.Answer : Type)

#check (@Effect4.FrameSimulation.Answer.ok :
  Effects.Trace.Val → Effect4.FrameSimulation.Answer)

#check (@Effect4.FrameSimulation.Answer.failed :
  Effect4.FrameSimulation.Err → Effect4.FrameSimulation.Answer)

#check (@Effect4.FrameSimulation.Tape : Type)

#check (@Effect4.FrameSimulation.Answer.value :
  Effect4.FrameSimulation.Answer → Effects.Trace.Val)

#check (@Effect4.FrameSimulation.bound : Effect4.FrameSimulation.Tape → Nat)

/-! F3: the oracle, the compilation, and the continuation table.

`answersOf` is the second structural recursion over the program; `interpret` is
the first. `compile` depends on nothing but the occurrence counter, which is why
it is a plain structural recursion and why the σ-name of the `n`-th performed
operation is `n` on every path. `residual` is what makes the table a table:
name `i` continues the program left after the first `i` answers. -/

#check (@Effect4.FrameSimulation.answersOf :
  {Ty : Type} → {a : Effects.FlowAlphabet Ty} → {St : Type} →
  Effects.Handler (Effect4.Flow.Sig a) (Effect4.FrameSimulation.Target St) →
  Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val → St →
  Effect4.FrameSimulation.Tape)

#check (@Effect4.FrameSimulation.compile :
  {Ty : Type} → {a : Effects.FlowAlphabet Ty} → Nat →
  Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val →
  Effect4.FrameSimulation.Code)

#check (@Effect4.FrameSimulation.residual :
  {Ty : Type} → {a : Effects.FlowAlphabet Ty} →
  Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val →
  Effect4.FrameSimulation.Tape →
  Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val)

#check (@Effect4.FrameSimulation.tapeSyncValue :
  Effect4.FrameSimulation.Tape → Nat → Effects.Trace.Val)

#check (@Effect4.FrameSimulation.tapeContA :
  {Ty : Type} → {a : Effects.FlowAlphabet Ty} →
  Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val →
  Effect4.FrameSimulation.Tape → Nat → Effects.Trace.Val → Effect4.FrameSimulation.Code)

#check (@Effect4.FrameSimulation.tapeInterp :
  {Ty : Type} → {a : Effects.FlowAlphabet Ty} →
  Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val →
  Effect4.FrameSimulation.Tape → Effect4.FrameSimulation.Table)

/-! F4: the fragment is closed.

`Program` has `pure` and `vis` and no bracket former, and `Handler.handle` takes
an operation and never a subcomputation, so `onFailure`, `onSuccessAndFailure`
and `onExit` — inside the packet's declared fragment — are not reachable from the
algebra at all, and `setInterruptible` never appears because it is only ever the
frame `onExit`'s `ensure` pushes. These two theorems are the proof that the mask
combinators, `exitFrame`, `whileLoop` and `iterator` are never entered, rather
than an assumption that they are not. -/

#check (@Effect4.FrameSimulation.inFragment : Effect4.FrameSimulation.Code → Bool)

#check (@Effect4.FrameSimulation.compile_inFragment :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} (i : Nat)
  (p : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val),
  Effect4.FrameSimulation.inFragment (Effect4.FrameSimulation.compile i p) = Bool.true)

#check (@Effect4.FrameSimulation.tapeContA_inFragment :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty}
  (root : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val)
  (tape : Effect4.FrameSimulation.Tape) (i : Nat) (value : Effects.Trace.Val),
  Effect4.FrameSimulation.inFragment (Effect4.FrameSimulation.tapeContA root tape i value) =
  Bool.true)

/-! F5: the two machine transitions.

One performed operation is exactly two steps: the `OnSuccess` frame pushes
itself, then the `Sync` produces the tape's answer and the pop finds the frame it
just pushed. Both hold by `rfl` — which is fence A made concrete: on this
fragment the pop has no skip guard to fire and no deferred interrupt to
answer. -/

#check (@Effect4.FrameSimulation.step_push :
  ∀ (interp : Effect4.FrameSimulation.Table) (i : Nat)
  (stack : List Effect4.FrameSimulation.Code) (flag : Bool),
  Effect4.FrameFiber.step interp
    (Effect4.FrameFiber.mk (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i) stack flag
      Option.none Bool.false) =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (Effect4.Prim.sync i)
      (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i :: stack) flag Option.none Bool.false),
    [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i)]))

#check (@Effect4.FrameSimulation.step_answer :
  ∀ (interp : Effect4.FrameSimulation.Table) (i : Nat)
  (stack : List Effect4.FrameSimulation.Code) (flag : Bool),
  (Effect4.FrameFiber.step interp
    (Effect4.FrameFiber.mk (Effect4.Prim.sync i)
      (Effect4.Prim.onSuccess (Effect4.Prim.sync i) i :: stack) flag Option.none Bool.false)).fst =
  Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (interp.contA i (interp.syncValue i)) stack flag Option.none
      Bool.false))

/-! F6: the algebra side, and the residual bookkeeping. -/

#check (@Effect4.FrameSimulation.interpret_pure :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} {St E : Type}
  (H : Effects.Handler (Effect4.Flow.Sig a) (ExceptT E (StateT St Id)))
  (value : Effects.Trace.Val) (s : St),
  (Effects.interpret H (Effects.Program.pure value)).run.run s = (Except.ok value, s))

#check (@Effect4.FrameSimulation.interpret_vis :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} {St E : Type}
  (H : Effects.Handler (Effect4.Flow.Sig a) (ExceptT E (StateT St Id)))
  (op : (Effect4.Flow.Sig a).Op)
  (k : (Effect4.Flow.Sig a).Answer op →
    Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val) (s : St),
  (Effects.interpret H (Effects.Program.vis op k)).run.run s =
  match (H.handle op).run.run s with
  | (Except.error cause, s') => (Except.error cause, s')
  | (Except.ok value, s') => (Effects.interpret H (k value)).run.run s')

#check (@Effect4.FrameSimulation.residual_append :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty}
  (p : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val)
  (prefix' : Effect4.FrameSimulation.Tape) (entry : Effect4.FrameSimulation.Answer),
  Effect4.FrameSimulation.residual p (prefix' ++ [entry]) =
  match Effect4.FrameSimulation.residual p prefix' with
  | Effects.Program.pure result => Effects.Program.pure result
  | Effects.Program.vis _ k => k entry.value)

/-! F7: the workhorse.

A compiled body under an *arbitrary* stack suffix reaches its own exit in
`2 * (its own tape).length` steps and leaves the suffix untouched. The suffix is
what makes it an induction, because the `OnSuccess` frame a compiled operation
pushes is the only frame the compiled program ever adds and the pop that answers
it removes it again. -/

#check (@Effect4.FrameSimulation.run_in_context :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} {St : Type}
  (H : Effects.Handler (Effect4.Flow.Sig a) (Effect4.FrameSimulation.Target St))
  (root : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val)
  (tape : Effect4.FrameSimulation.Tape)
  (q : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val) (i : Nat) (s : St)
  (stack : List Effect4.FrameSimulation.Code) (flag : Bool),
  Effect4.FrameSimulation.residual root (List.take i tape) = q →
  List.drop i tape = Effect4.FrameSimulation.answersOf H q s →
  (Effect4.FrameFiber.run (Effect4.FrameSimulation.tapeInterp root tape)
    (2 * List.length (Effect4.FrameSimulation.answersOf H q s))
    (Effect4.FrameFiber.mk (Effect4.FrameSimulation.compile i q) stack flag Option.none
      Bool.false)).fst =
  Effect4.FrameStep.running
    (Effect4.FrameFiber.mk
      (Effect4.Prim.ofExit
        (Effect4.FrameSimulation.exitOf ((Effects.interpret H q).run.run s).fst))
      stack flag Option.none Bool.false))

/-! F8: the theorem, and its `Cause.fail` corollary.

`hOracle` is what makes the pure `PrimInterp` legitimate: the tape is not any
tape, it is the one the handler produces along this run. Quoting the theorem
without it is misquoting it. -/

#check (@Effect4.FrameSimulation.compile_simulates :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} {St : Type}
  (H : Effects.Handler (Effect4.Flow.Sig a) (Effect4.FrameSimulation.Target St))
  (p : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val) (s0 : St)
  (tape : Effect4.FrameSimulation.Tape) (fuel : Nat),
  Effect4.FrameSimulation.answersOf H p s0 = tape →
  Effect4.FrameSimulation.bound tape ≤ fuel →
  (Effect4.FrameFiber.run (Effect4.FrameSimulation.tapeInterp p tape) fuel
    (Effect4.FrameFiber.start (Effect4.FrameSimulation.compile 0 p))).fst =
  Effect4.FrameStep.finished
    (Effect4.FrameSimulation.exitOf ((Effects.interpret H p).run.run s0).fst))

#check (@Effect4.FrameSimulation.liftFail :
  {Ty : Type} → {a : Effects.FlowAlphabet Ty} → {St : Type} →
  Effects.Handler (Effect4.Flow.Sig a)
    (ExceptT Effects.Trace.Val (StateT St Id)) →
  Effects.Handler (Effect4.Flow.Sig a) (Effect4.FrameSimulation.Target St))

#check (@Effect4.FrameSimulation.run_liftFail :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} {St : Type}
  (H : Effects.Handler (Effect4.Flow.Sig a)
    (ExceptT Effects.Trace.Val (StateT St Id)))
  (p : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val) (s : St),
  (Effects.interpret (Effect4.FrameSimulation.liftFail H) p).run.run s =
  match (Effects.interpret H p).run.run s with
  | (Except.ok value, s') => (Except.ok value, s')
  | (Except.error error, s') => (Except.error (Effect4.Cause.fail error), s'))

#check (@Effect4.FrameSimulation.compile_simulates_fail :
  ∀ {Ty : Type} {a : Effects.FlowAlphabet Ty} {St : Type}
  (H : Effects.Handler (Effect4.Flow.Sig a)
    (ExceptT Effects.Trace.Val (StateT St Id)))
  (p : Effects.Program (Effect4.Flow.Sig a) Effects.Trace.Val) (s0 : St)
  (tape : Effect4.FrameSimulation.Tape) (fuel : Nat),
  Effect4.FrameSimulation.answersOf (Effect4.FrameSimulation.liftFail H) p s0 = tape →
  Effect4.FrameSimulation.bound tape ≤ fuel →
  (Effect4.FrameFiber.run (Effect4.FrameSimulation.tapeInterp p tape) fuel
    (Effect4.FrameFiber.start (Effect4.FrameSimulation.compile 0 p))).fst =
  Effect4.FrameStep.finished
    (match ((Effects.interpret H p).run.run s0).fst with
      | Except.ok value => Effect4.Exit.success value
      | Except.error error => Effect4.Exit.failure (Effect4.Cause.fail error)))

/-! F9: the worked finite probe.

A counter alphabet with two operations, and two runs of `add 3; add _; get` over
the state `10`: one that answers three times, and one whose second `add` fails.
The theorem is a universally quantified statement whose hypotheses are
satisfiable, so it cannot be vacuous, but a reader is entitled to see the
machine actually run. The last guard is the tightness receipt: one unit below
`bound` the run has *not* finished, which is a live DB-04 frontier and not a
result. -/

namespace Probe

inductive Ty where
  | nat
  /-- The spelling a `branch` test operand must carry (Flow v3). No term in
  this probe is a `branch`, so nothing here reads it; the alphabet still has to
  name a spelling, and naming `nat` would claim the counter's answers are
  boolean tests. -/
  | bool
  /-- The declared error spelling (Flow v3): the type a `performCatch` binds in
  its failure successor. This probe runs `Effects.Program`, not a checked flow,
  so its failures are `Effect4.Cause` values at the handler and no term reads
  this spelling either. -/
  | err
deriving DecidableEq

inductive Op where
  | get
  | add
deriving DecidableEq

def alphabet : Effects.FlowAlphabet Ty where
  id := ⟨0⟩
  Op := Op
  operationId
    | .get => ⟨0⟩
    | .add => ⟨1⟩
  lookup id := if id.value = 0 then some .get else if id.value = 1 then some .add else none
  requestTy := fun _ => Ty.nat
  answerTy := fun _ => Ty.nat
  errorTy := fun _ => some Ty.err
  boolTy := Ty.bool
  lookup_operationId := by intro op; cases op <;> rfl
  operationId_of_lookup := by
    intro id op h
    obtain ⟨v⟩ := id
    by_cases h0 : v = 0
    · subst h0; simp at h; subst h; rfl
    · by_cases h1 : v = 1
      · subst h1; simp at h; subst h; rfl
      · simp [h0, h1] at h

abbrev Sig := Effect4.Flow.Sig alphabet

/-- `get` reads the cell, `add n` adds and answers the new value, and `add 0`
fails. -/
def cell : Effects.Handler Sig (Effect4.FrameSimulation.Target Nat) :=
  ⟨fun op =>
    ExceptT.mk (fun s =>
      match op.1, op.2 with
      | Op.get, _ => (Except.ok (Effects.Trace.Val.nat s), s)
      | Op.add, Effects.Trace.Val.nat 0 =>
        (Except.error (Effect4.Cause.fail (Effects.Trace.Val.str "zero")), s)
      | Op.add, Effects.Trace.Val.nat n =>
        (Except.ok (Effects.Trace.Val.nat (s + n)), s + n)
      | Op.add, _ =>
        (Except.error (Effect4.Cause.fail (Effects.Trace.Val.str "bad")), s))⟩

/-- `add 3; add 4; get` -/
def program : Effects.Program Sig Effects.Trace.Val :=
  .vis (⟨Op.add, Effects.Trace.Val.nat 3⟩ : Sig.Op) (fun _ =>
    .vis (⟨Op.add, Effects.Trace.Val.nat 4⟩ : Sig.Op) (fun _ =>
      .vis (⟨Op.get, Effects.Trace.Val.unit⟩ : Sig.Op) (fun value => .pure value)))

/-- `add 3; add 0; get` — the second operation fails, so the third never runs. -/
def programFails : Effects.Program Sig Effects.Trace.Val :=
  .vis (⟨Op.add, Effects.Trace.Val.nat 3⟩ : Sig.Op) (fun _ =>
    .vis (⟨Op.add, Effects.Trace.Val.nat 0⟩ : Sig.Op) (fun _ =>
      .vis (⟨Op.get, Effects.Trace.Val.unit⟩ : Sig.Op) (fun value => .pure value)))

#guard (Effect4.FrameSimulation.answersOf cell program 10).length = 3

#guard Effect4.FrameSimulation.bound (Effect4.FrameSimulation.answersOf cell program 10) = 7

#guard (Effect4.FrameSimulation.answersOf cell programFails 10).length = 2

#guard Effect4.FrameSimulation.bound (Effect4.FrameSimulation.answersOf cell programFails 10) = 5

#guard Effect4.FrameSimulation.exitOf ((Effects.interpret cell program).run.run 10).1
  = Effect4.Exit.success (Effects.Trace.Val.nat 17)

#guard Effect4.FrameSimulation.exitOf ((Effects.interpret cell programFails).run.run 10).1
  = Effect4.Exit.failure (Effect4.Cause.fail (Effects.Trace.Val.str "zero"))

#guard Effect4.FrameSimulation.compile 0 program
  = Effect4.Prim.onSuccess (Effect4.Prim.sync 0) 0

#guard Effect4.FrameSimulation.inFragment (Effect4.FrameSimulation.compile 0 program) = true

#guard (Effect4.FrameFiber.run
    (Effect4.FrameSimulation.tapeInterp program
      (Effect4.FrameSimulation.answersOf cell program 10))
    (Effect4.FrameSimulation.bound (Effect4.FrameSimulation.answersOf cell program 10))
    (Effect4.FrameFiber.start (Effect4.FrameSimulation.compile 0 program))).fst
  = Effect4.FrameStep.finished
    (Effect4.FrameSimulation.exitOf ((Effects.interpret cell program).run.run 10).1)

#guard (Effect4.FrameFiber.run
    (Effect4.FrameSimulation.tapeInterp programFails
      (Effect4.FrameSimulation.answersOf cell programFails 10))
    (Effect4.FrameSimulation.bound (Effect4.FrameSimulation.answersOf cell programFails 10))
    (Effect4.FrameFiber.start (Effect4.FrameSimulation.compile 0 programFails))).fst
  = Effect4.FrameStep.finished
    (Effect4.FrameSimulation.exitOf ((Effects.interpret cell programFails).run.run 10).1)

#guard (Effect4.FrameFiber.run
    (Effect4.FrameSimulation.tapeInterp program
      (Effect4.FrameSimulation.answersOf cell program 10))
    (Effect4.FrameSimulation.bound (Effect4.FrameSimulation.answersOf cell program 10) - 1)
    (Effect4.FrameFiber.start (Effect4.FrameSimulation.compile 0 program))).fst
  ≠ Effect4.FrameStep.finished
    (Effect4.FrameSimulation.exitOf ((Effects.interpret cell program).run.run 10).1)

end Probe

end Effect4Test.Semantics.FrameSimulationContract
