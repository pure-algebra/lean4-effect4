import Effect4.Program.Denote
import Effects.Algebra.Sum

/-!
# Program.Sched — the term scheduler's signature (R1, amended for R2–R4 and P2)

Plan: `docs/research/2026-09-05-runtime-proof-graph.md` §3 (Layer R, the term scheduler);
worksheet: `docs/research/2026-09-05-slices-2-3-worksheets.md` (R1); strategy:
`docs/research/2026-09-05-tactics-cheatsheet-dag-strategy.md` REF/sig; the P2 phase model:
`docs/research/2026-09-06-p0-fable-record.md` §4. Battery:
`Test/Program/SchedContract.lean`; report: `Test/Program/SchedAxiomReport.lean`.

This module declares the signature the term scheduler's fibers speak: the store signature
`StoreSig` of `Denote.lean` beside a fiber signature `FiberSig`, one operation per
fiber-level arm of the machine's `evaluatePrim` (`src/Effect4/Machine/Fibers.lean`, the
`withFiber` arms, the join and async parks, the yield), alongside addressed scope/body
operations, the checkpoint operations and live frontiers, summed by
`Effects.Signature.sum`. Enclosing operations carry source points; `fork` and `mask` also
admit the two first-order synthesized `Body` shapes used by store finalization. Control
markers retain continuation boundaries across suspension. Four operations are the
checkpoints the pinned host counts and the frame machine spends where the term has no
store or fiber work of its own (P2, rows of the P0 record §2): `suspend` is the counted
step that returns code (`Suspend`, a decided `branch`, a yieldable error's failure, and
the wrapper the host puts in front of a generator and of a loop); `sync` is a pure
thunk's value delivered through the `answered` phase; `gen` and `loop` are the initial
entries of a generator and of a cursor loop, whose later iterations run inside the body's
delivery through the evaluator's saved slots, as the host's `Iterator` and `While` frames
do. No operation stores a semantic program or a function: `Eff` remains the only source
representation.

What is proved here is only the store half: the straight-line denotation injected on the
left of the sum has, under the summed handler, exactly the meaning `Denote.lean` gives it
(`meaning_via_rsig`, through the algebra's `interpret_inl`). The fiber operations have no
handler here on purpose: the term scheduler (`RuntimeR`, worksheet R3–R4) interprets
them as a state machine over the same decisions, bookkeeping and stores as the fiber
machine, not as a `Handler` into `StateT Stores Id`. `fiberRefusal` below answers every
fiber operation with a default answer and exists only so that the summed handler is total; no
theorem is stated over a program that performs a fiber operation.

Refused by name:
* `SCHED-FB-FIBER-HANDLER` — `fiberRefusal` is not a semantics of the fiber operations.
* `SCHED-FB-REFUSE` — `FiberOp.refuse` is the machine's refusal defect
  (`WithFiberAction.refuse`), carried so that `denoteR` can name it; its meaning is a
  failed exit, not a feature.
* `SCHED-FB-FRONTIER` — `frontier` is unfinished work. Its default answer exists only in
  the placeholder handler; the scheduler leaves it unanswered until the compile budget
  or the source choice is available, and `unsupported` names a source form the compile
  refuses.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-! ## The fiber signature -/

/-- Why a denotation cannot yet supply a result. None is an exit or a cause. -/
inductive FrontierReason
  | compileFuel
  | unansweredChoice
  | unsupported
deriving DecidableEq

/-- Addressed source bodies and the two synthesized bodies used by the stores.
`Stores.raceSettleProgram` and a scope's finalizer programs have no source point. A settled race's
masked cleanup is named by the race, so it interrupts the race's live set at cleanup
time (`internal/effect.ts:1510-1514`, D6a), never a winner-time list. -/
inductive Body
  | at_ (point : Point)
  | fin (name : FinName) (exit : ExitV)
  | raceCleanup (race : Nat)
deriving DecidableEq

/-- Continuation slots retained across suspension. These are control data, not
stored functions or a second program syntax. `onExit` runs its cleanup masked. -/
inductive GuardKind
  | onSuccess
  | onFailure
  | all
  | onExit (finalizerInterruptible : Bool)
deriving DecidableEq

/-- Fiber operations plus addressed bodies, checkpoints, control boundaries and live
frontiers. -/
inductive FiberOp : Type
  | fork (child : Body) (options : Supervision.ForkOptions)
  | forkIn (child : Point) (options : Supervision.ForkOptions) (scope : Nat) (key : Nat)
  | forkScoped (child : Point) (options : Supervision.ForkOptions) (key : Nat)
  | await (target : FiberId) (mode : Supervision.ObserverMode)
  | awaitAll (targets : List FiberId)
  | awaitAllFailFast (targets : List FiberId)
  | yieldNow (priority : Nat)
  | async (register : EffName) (request : Val)
  | interrupt (target : FiberId)
  /-- `fiberInterruptAs(target, who)` (`internal/effect.ts:871-884`): the program the public
  interrupt's entry returns (source-repairs §19, D6b). -/
  | interruptAs (target : FiberId) (who : FiberId)
  | interruptScoped (target : FiberId)
  | interruptAll (targets : List FiberId) (interruptor : Option FiberId)
  | mask (flag : Bool) (body : Body)
  | closeScope (scope : Nat) (exit : ExitV)
  /-- Atomic scoped entry around an eager addressed body. -/
  | scoped (body : Point)
  /-- Stateful callback glue, consumed during delivery after the scoped pop. -/
  | scopeExit (previous : Ctx) (scope : Nat) (exit : ExitV)
  | acquireRelease (acquire : Point) (release : Point)
  | raceAll (entrants : List Point)
  /-- The counted `Async` registration a race's entry returns (`internal/effect.ts:1493`,
  D6a): the term instance of `RunInterp.parkCode` at `ParkKind.race`. -/
  | raceRegister (race : Nat)
  | cancelRace (race : Nat)
  | getId
  | getContext
  | setContext (ctx : Ctx)
  | snapshotChildren
  | awaitNewChildren (snapshot : List FiberId)
  | runIn (target : FiberId) (scope : Nat) (key : Nat)
  | dropObservers (token : Nat)
  | refuse (cause : Cause Err Defect FiberId Ann)
  /-- The `Scope` service read (`Context.ts:423`; source-repairs §20): the ambient scope's
  handle, the first half of `forkScoped`'s `flatMap(scope, …)`. -/
  | ambientScope
  /-- `scopeCloseFinalizers`' counted `fnUntraced` suspend (`internal/effect.ts:1199-1208`,
  `:3806`; §20): the close of two or more finalizers, answering unit before its walk. -/
  | closeWalk (strategy : FinalizerStrategy) (order : List FinName) (exit : ExitV)
  /-- The walk's counted `Iterator` entry (`:1356-1372`; §20): the sequential generator from
  its first finalizer, or the parallel step. Answers the walk's exit. -/
  | closeIter (strategy : FinalizerStrategy) (order : List FinName) (exit : ExitV)
  | frontier (reason : FrontierReason) (at_ : Point)
  /-- `none` enters the body; `some exit` resumes outside its saved boundary. -/
  | guard_ (kind : GuardKind)
  | unguard (exit : ExitV)
  | finishFinalizer (exit : ExitV)
  /-- The counted checkpoint that returns its continuation's code (`Suspend`). -/
  | suspend (at_ : Point)
  /-- A pure thunk's value, delivered through the `answered` phase (`Sync`). -/
  | sync (value : Val)
  /-- A generator's initial entry (`Iterator[evaluate]`). -/
  | gen (at_ : Point)
  /-- A cursor loop's initial entry (`While[evaluate]`). -/
  | loop (at_ : Point) (cursor : Val)
  /-- The completed-exit view at a source callback's invocation. Resolved during
  code construction, with no host operation or scheduler command of its own. -/
  | construction
deriving DecidableEq

/-- Operations that deliver an exit answer directly with that exit, while value-returning
operations retain `Val`. R2's answer amendment is recorded in the packet; the scout's
claimed collision in `reifyExitVal` is false (`E4-SCHED-CE-002`). The generator and loop
entries answer with the generator's or the loop's exit. -/
abbrev FiberOp.answer : FiberOp → Type
  | .construction => List (FiberId × ExitV)
  | .guard_ _ => Option ExitV
  | .unguard _ | .finishFinalizer _ => ExitV
  | .scoped _ | .scopeExit _ _ _
  | .mask _ _ | .closeScope _ _ | .acquireRelease _ _ | .raceAll _ | .raceRegister _
  | .async _ _ | .forkScoped _ _ _ | .frontier _ _ | .gen _ | .loop _ _ | .closeIter _ _ _ => ExitV
  | .await _ .joinEffect => ExitV
  | _ => Val

/-- Only a total placeholder for the store-lift theorem; never a fiber semantics. -/
def FiberOp.defaultAnswer : (op : FiberOp) → op.answer
  | .construction => []
  | .guard_ _ => none
  | .unguard ex | .finishFinalizer ex => ex
  | .scoped _ | .scopeExit _ _ _
  | .mask _ _ | .closeScope _ _ | .acquireRelease _ _ | .raceAll _ | .raceRegister _
  | .async _ _ | .forkScoped _ _ _ | .frontier _ _ | .gen _ | .loop _ _ | .closeIter _ _ _ =>
    Exit.success Val.unit
  | .await _ .joinEffect => Exit.success Val.unit
  | .await _ .awaitValue => Val.unit
  | .fork _ _ | .forkIn _ _ _ _ | .awaitAll _ | .awaitAllFailFast _
  | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _ | .interruptAll _ _
  | .cancelRace _ | .getId | .getContext | .setContext _ | .snapshotChildren
  | .awaitNewChildren _ | .runIn _ _ _ | .dropObservers _ | .refuse _
  | .suspend _ | .sync _ | .ambientScope | .closeWalk _ _ _ => Val.unit

/-- The answer type is selected by the operation. -/
abbrev FiberSig : Effects.Signature.{0, 0} := ⟨FiberOp, FiberOp.answer⟩

/-- The term scheduler's signature: the stores on the left, the fibers on the right. -/
abbrev RSig : Effects.Signature.{0, 0} := Effects.Signature.sum StoreSig FiberSig

theorem RSig_op : RSig.Op = (SyncOp ⊕ FiberOp) := rfl

theorem RSig_answer_inl (o : SyncOp) : RSig.Answer (Sum.inl o) = Val := rfl

theorem RSig_answer_inr (o : FiberOp) : RSig.Answer (Sum.inr o) = o.answer := rfl

/-- The programs the term scheduler's fibers hold. -/
abbrev RProgram := Effects.Program RSig ExitV

/-- A store operation as a node of an `RSig` program: `perform` is the derived one-node
program, so a store step in a meaning is written `vis (.inl op) k`, never `.perform`. -/
theorem perform_inl_bind (op : SyncOp) (k : Val → RProgram) :
    Effects.Program.bind (Effects.Program.perform (S := RSig) (Sum.inl op)) k =
      Effects.Program.vis (Sum.inl op) k := rfl

/-! ## The store half, lifted -/

/-- Not a semantics (`SCHED-FB-FIBER-HANDLER`): the total placeholder for the right half. -/
def fiberRefusal : Effects.Handler FiberSig (StateT Stores Id) where
  handle op := fun s => (op.defaultAnswer, s)

/-- The store handler on the left, the placeholder on the right. -/
def rHandler : Effects.Handler RSig (StateT Stores Id) :=
  Effects.Handler.sum storeHandler fiberRefusal

theorem rHandler_inl (o : SyncOp) : rHandler.handle (Sum.inl o) = storeHandler.handle o := rfl

theorem rHandler_inr (o : FiberOp) : rHandler.handle (Sum.inr o) = fiberRefusal.handle o := rfl

/-- The straight-line denotation, injected on the left, means under the summed handler
exactly what it means under the store handler. -/
theorem interpret_inl_store {A : Type} (program : Effects.Program StoreSig A) :
    Effects.interpret rHandler (Effects.Program.inl program) =
      Effects.interpret storeHandler program :=
  Effects.interpret_inl storeHandler fiberRefusal program

/-- `meaning` recovered through `RSig`: the target `denoteR_straight` (worksheet R2) lands
on. -/
theorem meaning_via_rsig (e : NativeEff) (env : List Val) (s : Stores) :
    (Effects.interpret rHandler (Effects.Program.inl (denote e env))).run s =
      meaning e env s := by
  rw [interpret_inl_store]; rfl

end Effect4.Program.Sched
