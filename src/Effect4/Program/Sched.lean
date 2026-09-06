import Effect4.Program.Denote
import Effects.Algebra.Sum

/-!
# Program.Sched — the term scheduler's signature (R1, amended for R2)

Plan: `docs/research/2026-09-05-runtime-proof-graph.md` §3 (Layer R, the term scheduler);
worksheet: `docs/research/2026-09-05-slices-2-3-worksheets.md` (R1); strategy:
`docs/research/2026-09-05-tactics-cheatsheet-dag-strategy.md` REF/sig. Battery:
`Test/Program/SchedContract.lean`; report: `Test/Program/SchedAxiomReport.lean`.

This module declares the signature the term scheduler's fibers speak: the store signature
`StoreSig` of `Denote.lean` beside a fiber signature `FiberSig`, one operation per
fiber-level arm of the machine's `evaluatePrim` (`src/Effect4/Machine/Fibers.lean`, the
`withFiber` arms, the join and async parks, the yield), alongside addressed scope/body
operations and live frontiers, summed by `Effects.Signature.sum`.
Every operation that encloses a program (`fork`, `mask`, `scoped`, `acquireRelease`,
`raceAll`) carries a `Point`, an address into the root program with its environment, and
never a program: a program-valued operation parameter is not a positive inductive
definition (the graph note, core math §5), and it is also what the compile does, which
holds a compiled `Prim` at the same address.

What is proved here is only the store half: the straight-line denotation injected on the
left of the sum has, under the summed handler, exactly the meaning `Denote.lean` gives it
(`meaning_via_rsig`, through the algebra's `interpret_inl`). The fiber operations have no
handler here on purpose: the term scheduler (`Sched`, owed: worksheet R3–R4) interprets
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
  the placeholder handler; the later scheduler must leave it unanswered until the
  required unfolding, compile budget or source choice is available.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-! ## The fiber signature -/

/-- Why a bounded unfolding cannot yet supply a result. None is an exit or a cause. -/
inductive FrontierReason
  | compileFuel
  | unfoldingFuel
  | unansweredChoice
  | unsupported
deriving DecidableEq

/-- Residual control addresses in the existing root program; no second program syntax. -/
inductive ResumePoint
  | effect (point : Point)
  | generator (point : Point) (pc : List Nat) (env : List Val) (scanFuel : Nat)
  | loop (point : Point) (cursor : Val)
deriving DecidableEq

/-- Fiber operations plus addressed scope/body operations and bounded frontiers.
Enclosing operations carry a `Point`; a frontier also retains its residual control. -/
inductive FiberOp : Type
  | fork (child : Point) (options : Supervision.ForkOptions)
  | forkIn (child : Point) (options : Supervision.ForkOptions) (scope : Nat) (key : Nat)
  | forkScoped (child : Point) (options : Supervision.ForkOptions) (key : Nat)
  | await (target : FiberId) (mode : Supervision.ObserverMode)
  | awaitAll (targets : List FiberId)
  | awaitAllFailFast (targets : List FiberId)
  | yieldNow (priority : Nat)
  | async (register : EffName) (request : Val)
  | interrupt (target : FiberId)
  | interruptScoped (target : FiberId)
  | interruptAll (targets : List FiberId) (interruptor : Option FiberId)
  | mask (flag : Bool) (body : Point)
  | scoped (body : Point) (scope : Nat)
  | closeScope (scope : Nat) (exit : ExitV)
  | acquireRelease (acquire : Point) (release : Point)
  | raceAll (entrants : List Point)
  | cancelRace (race : Nat)
  | getId
  | getContext
  | setContext (ctx : Ctx)
  | snapshotChildren
  | awaitNewChildren (snapshot : List FiberId)
  | runIn (target : FiberId) (scope : Nat) (key : Nat)
  | dropObservers (token : Nat)
  | refuse (cause : Cause Err Defect FiberId Ann)
  | frontier (reason : FrontierReason) (resumeAt : ResumePoint)
deriving DecidableEq

/-- Operations that deliver an exit answer directly with that exit, while value-returning
operations retain `Val`. R2's answer amendment is recorded in the packet; the scout's
claimed collision in `reifyExitVal` is false (`E4-SCHED-CE-002`). -/
abbrev FiberOp.answer : FiberOp → Type
  | .mask _ _ | .scoped _ _ | .closeScope _ _ | .acquireRelease _ _ | .raceAll _
  | .async _ _ | .forkScoped _ _ _ | .frontier _ _ => ExitV
  | .await _ .joinEffect => ExitV
  | _ => Val

/-- Only a total placeholder for the store-lift theorem; never a fiber semantics. -/
def FiberOp.defaultAnswer : (op : FiberOp) → op.answer
  | .mask _ _ | .scoped _ _ | .closeScope _ _ | .acquireRelease _ _ | .raceAll _
  | .async _ _ | .forkScoped _ _ _ | .frontier _ _ => Exit.success Val.unit
  | .await _ .joinEffect => Exit.success Val.unit
  | .await _ .awaitValue => Val.unit
  | .fork _ _ | .forkIn _ _ _ _ | .awaitAll _ | .awaitAllFailFast _
  | .yieldNow _ | .interrupt _ | .interruptScoped _ | .interruptAll _ _
  | .cancelRace _ | .getId | .getContext | .setContext _ | .snapshotChildren
  | .awaitNewChildren _ | .runIn _ _ _ | .dropObservers _ | .refuse _ => Val.unit

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
