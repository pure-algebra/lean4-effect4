import Effect4.Laws.Program.Agreement.Machine
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Agreement
-- Finite probes: proposed arbitrary-budget rows-block-host/R6 extension.
def root : NativeEff := .succeed (.lit .unit)
def fr : NFiber := fiberOf (Prim.success Val.unit) [] true
def budgetCtx (b : Nat) : Ctx :=
  Ctx.withServices ((Env.Context.empty : Env.Ctx).addV Env.maxOpsKey (.nat b))
def lowFiber (b : Nat) : NRunFiber :=
  {fiberAt fr 0 with context := budgetCtx b, maxOpsBeforeYield := b}
def observeIter (b : Nat) (prevent : Bool := false) :=
  let it := iteration (interpOf root) (M fr Stores.empty 0 [] 0) {lowFiber b with preventYield := prevent} false
  (it.yielding, it.fiber.frame.stack.length, it.fiber.exit.isSome)
#eval [0,1,2].map fun b => (b, observeIter b)
#eval observeIter 0 true
#eval PlainFrame (Prim.setInterruptible false)
#eval (fr.uninterruptible.interruptibleRegion).1.stack.map PlainFrame
-- Start directly on the scheduler's low-budget primitive state.
def lowM (b : Nat) : Api.Machine := {M fr Stores.empty 0 [] 0 with fibers := [lowFiber b]}
def evaluated (b : Nat) : Api.Machine :=
  (driveState (interpOf root) 20 (lowM b) [Cmd.loop Api.root false]).1
def flushed (b rounds : Nat) := flushAllState (interpOf root) 100 rounds (evaluated b)
#eval [0,1,2].map fun b => (b, (flushed b 20).1.completedExits.length, (flushed b 20).2,
  ((flushed b 20).1.fibers.head?).map (fun f => (f.frame.stack.length, f.currentOpCount, f.maxOpsBeforeYield)))
#eval Env.budgetOf ((Env.Context.empty : Env.Ctx).addV Env.maxOpsKey (.nat 1))
#eval SigApp.serviceTy {} Env.maxOpsKey
-- Budget two after an existing scheduler yield: resume itself consumes count one.
def afterYield2 : Api.Machine :=
  {Myield fr Stores.empty 2 [] 0 with fibers :=
    [{parkedAt fr 2 0 with context := budgetCtx 2, maxOpsBeforeYield := 2}]}
#eval ((flushAllState (interpOf root) 100 20 afterYield2).1.completedExits.length,
  (flushAllState (interpOf root) 100 20 afterYield2).2,
  ((flushAllState (interpOf root) 100 20 afterYield2).1.fibers.head?).map (fun f => (f.frame.stack.length, f.currentOpCount)))
def poisonedCtx : Ctx := Ctx.withServices ((Env.Context.empty : Env.Ctx).addV Env.maxOpsKey (.nat 1))
#eval (externalValue Ty.context [] (Val.context poisonedCtx)).isSome
#eval (externalValue Ty.nat [] (Val.context poisonedCtx)).isSome
