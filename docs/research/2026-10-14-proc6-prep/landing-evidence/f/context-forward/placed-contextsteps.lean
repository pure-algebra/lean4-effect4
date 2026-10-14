import Effect4.Laws.Program.Agreement.Segment
import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Auto.Semantics

/-!
# Context brackets of the hosted local run

Concept: translation-simulation. Claim: rows-block-host, requirement R6.
Consumers: the context arms of `CompilesBlk`.
Reach: every invocation context, mask flag and final exit of one fiber.
These brackets establish neither scheduler progress nor host conformance.
-/
set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- Step of rows-block-host/R6; consumer: the context bracket.
The body restores its original mask before the restoring finalizer runs. -/
def contextBodyStack (u : Env.ContextUpdate) (q : Point) (old : Ctx)
    (K : List NCode) (i : Bool) : List NCode :=
  (if i then [Prim.setInterruptible false] else []) ++
    (if updateKeepsIdentity u old.services then maskStack i K else
      Prim.onExit (Prim.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old) false ::
        maskStack i K)

/-- Step of rows-block-host/R6; consumer: `compilesBlk_provideService` and
`compilesBlk_provideContext`. The entrance changes only context and control frames. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal contextBracket_enter {table : RowTable} (root : NativeEff) (u : Env.ContextUpdate)
    (q : Point) (old : Ctx) (K : List NCode) (i : Bool) (s : Stores) :
    ∃ c, ReachesQ (table := table) root c
      (fiberOf (updateContextAt u (.program q)) K i) s
      (fiberOf (resolve root q) (contextBodyStack u q old K i) i) s
      old (provided u old)

/-- Step of rows-block-host/R6; consumer: the context arms' final-frame composition.
The restoring finalizer returns both success and failure to the invocation context. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal contextBracket_leave {table : RowTable} (root : NativeEff) (u : Env.ContextUpdate)
    (q : Point) (old : Ctx) (K : List NCode) (i : Bool) (s : Stores) (ex : ExitV) :
    ∃ c, ReachesQ (table := table) root c
      (fiberOf (Prim.ofExit ex) (contextBodyStack u q old K i) i) s
      (fiberOf (Prim.ofExit ex) K i) s (provided u old) old

end Effect4.Program.Agreement
