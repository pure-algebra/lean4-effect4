import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.ValidatedBlocks
import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Library.Ref.Cache
import Effect4.Laws.Library.Queue.Ops
import Effect4.Laws.Library.Semaphore.Ops
import Effect4.Library.Queue.Defs
import Effect4.Library.Semaphore.Defs
import Test.Dogfood.Scenario.Todo.Cached
import ProofGraph.Plan

set_option autoImplicit false

namespace Effect4.Probes.ProcClose

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Denote
open Effect4.Run

-- 1. Plan status of the procedures and block-meaning proof graph at 3c9091ed7
#plan_status Effect4.Program.Typed.denotesTyped
#plan_status Effect4.Program.Typed.loadsTyped
#plan_status Effect4.Program.Typed.call_arm
#plan_status Effect4.Program.Typed.invoke_arm
#plan_status Effect4.Program.Typed.param_arm
#plan_status Effect4.Run.h9_blocks
#plan_status Effect4.Run.conforms_sat_blocks
#plan_status Effect4.Run.agrees_hostRun_blocks
#plan_status Effect4.Program.Denote.call_unfolds_at_limitB
#plan_status Effect4.Program.Denote.invoke_unfolds_at_limitB
#plan_status Effect4.Program.Denote.denoteBlockB_approx
#plan_status Effect4.Program.Agreement.hostRunBlockB_stable
#plan_status Effect4.Ref.Cache.cache_agrees
#plan_status Test.Dogfood.Scenario.Todo.Cached.cached_list_after_add

-- 2. Fragment membership of Queue and Semaphore definition blocks and individual bodies
def queueModule : Module NativeOp :=
  (Effect4.Queue.Definitions.make "numbers" .nat).module (succeed unit)

def semaphoreModule : Module NativeOp :=
  (Effect4.Semaphore.Definitions.make "permits").module (succeed unit)

def builtQueue? : Option NativeEff :=
  (Effect4.Api.Author.build queueModule).toOption.map (·.program)

def builtSemaphore? : Option NativeEff :=
  (Effect4.Api.Author.build semaphoreModule).toOption.map (·.program)

-- Both definition blocks build and pass the module checker, yet lie outside `BlockRows`:
#guard builtQueue?.isSome
#guard builtSemaphore?.isSome
#guard builtQueue?.map (BlockRows []) = some false
#guard builtSemaphore?.map (BlockRows []) = some false

-- Individual bodies of Queue.Definitions (take, offer, poll, size):
-- Only `size` (index 3) belongs to `BodyRows`; `take` (0), `offer` (1), and `poll` (2) do not.
#guard builtQueue?.map (fun p => (bodiesOf p).map (BodyRows [])) =
  some [false, false, false, true]

-- Individual bodies of Semaphore.Definitions (take, release, takeIfAvailable):
-- Only `takeIfAvailable` (index 2) belongs to `BodyRows`; `take` (0) and `release` (1) do not.
#guard builtSemaphore?.map (fun p => (bodiesOf p).map (BodyRows [])) =
  some [false, false, true]

-- 3. Budget probe on syntactic inlining (G7) vs semantic frame unfolding (invoke_unfolds_at_limitB)
-- In `denoteBlockB`:
--   * `denoteBlockB_call` steps `.perform (.call j) r` at budget `k + 1` to `body` at budget `k`.
--   * `denoteBlockB_invoke` steps `.invoke j r args` at budget `k + 1` to `body` at budget `k`,
--     while folding `args` into `ParamTreeB` closures at the caller's budget `k + 1`.
-- Consequently, syntactic inlining of `invoke` matches neither budget `k` nor budget `k + 1`
-- by equality; instead it obeys the two-sided approximation sandwich:
--   `denoteBlockB k (inline) ⊑ denoteBlockB (k + 1) (invoke) ⊑ denoteBlockB (k + 1) (inline)`.

-- Def 0: returns 42
def body0 : NativeEff := .succeed (.lit (.nat 42))

-- Def 1: calls Def 0 (requires budget >= 1)
def body1 : NativeEff := .perform (.call 0) (.lit .unit)

-- Def 2: higher-order pass-through (invokes param 0)
def body2 : NativeEff := .perform (.param 0) (.lit .unit)

-- Def 3: outer higher-order definition that passes its param 0 to Def 2
def body3 : NativeEff := .invoke 2 (.lit .unit) (.cons (.perform (.param 0) (.lit .unit)) .nil)

-- Def 4: calls Def 0 before invoking param 0
def body4 : NativeEff :=
  .bind (.perform (.call 0) (.lit .unit)) (.perform (.param 0) (.lit .unit))

def nestedBodies : List NativeEff := [body0, body1, body2, body3, body4]

-- Control A (budget k is too small for inlined args):
-- Un-inlined invocation: invoke 3 unit [perform (call 1) unit]
def uninlinedInvoke : NativeEff :=
  .invoke 3 (.lit .unit) (.cons (.perform (.call 1) (.lit .unit)) .nil)

def inlinedBody3 : NativeEff :=
  .bind (.succeed (.lit .unit))
    (.invoke 2 (.lit .unit)
      (.cons (.bind (.succeed (.lit .unit)) (.perform (.call 1) (.lit .unit))) .nil))

-- Control B (budget k + 1 is too large for inlined body):
-- Un-inlined invocation: invoke 4 unit [succeed 99]
def uninlinedInvoke4 : NativeEff :=
  .invoke 4 (.lit .unit) (.cons (.succeed (.lit (.nat 99))) .nil)

def inlinedBody4 : NativeEff :=
  .bind (.succeed (.lit .unit))
    (.bind (.perform (.call 0) (.lit .unit))
      (.bind (.succeed (.lit .unit)) (.succeed (.lit (.nat 99)))))

def trivialHost : Effects.Comodel (RowSig []) Unit where
  answer op := nomatch op

-- Control A at k = 1: `uninlinedInvoke` at budget k + 1 = 2 succeeds, while `inlinedBody3` at budget k = 1 cuts:
#guard hostRunBlockB trivialHost nestedBodies 2 [] uninlinedInvoke emptyCtx [] Stores.empty () =
  some (some (.success (.nat 42)), (Stores.empty, ()))
#guard hostRunBlockB trivialHost nestedBodies 1 [] inlinedBody3 emptyCtx [] Stores.empty () =
  some (none, (Stores.empty, ()))
#guard hostRunBlockB trivialHost nestedBodies 2 [] inlinedBody3 emptyCtx [] Stores.empty () =
  some (some (.success (.nat 42)), (Stores.empty, ()))

-- Control B at k = 0: `uninlinedInvoke4` at budget k + 1 = 1 cuts, while `inlinedBody4` at budget k + 1 = 1 succeeds:
#guard hostRunBlockB trivialHost nestedBodies 1 [] uninlinedInvoke4 emptyCtx [] Stores.empty () =
  some (none, (Stores.empty, ()))
#guard hostRunBlockB trivialHost nestedBodies 1 [] inlinedBody4 emptyCtx [] Stores.empty () =
  some (some (.success (.nat 99)), (Stores.empty, ()))
#guard hostRunBlockB trivialHost nestedBodies 2 [] uninlinedInvoke4 emptyCtx [] Stores.empty () =
  some (some (.success (.nat 99)), (Stores.empty, ()))

end Effect4.Probes.ProcClose
