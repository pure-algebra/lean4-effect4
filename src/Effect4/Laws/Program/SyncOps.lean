import Effect4.Program.Native
import Aesop

/-!
# The source rows' store operations, split once

`NativeOp.syncOpOf` (`src/Effect4/Program/Native.lean`) is split here, upstream of every law
module that splits it. Its case split and the auxiliary match equations it needs are declared in
this module. Two modules that each split it would each declare them, and a module that imports
both refuses the duplicate (`NativeScope` and `Typed/Denotation`, 2026-10-12).

Placement: concept `residual-program-typing`, the store operation a source row asks for.
Consumers: `SourceScope.opAt_origin` (`Laws/Program/NativeScope.lean`), and through it the
source ownership of a native operation.
-/

set_option autoImplicit false

namespace Effect4.Program.SourceScope

open Effect4 Effect4.Machine Effect4.Program

/-- A source row cannot synthesize a captured finalizer registration. -/
theorem source_no_scopeAdd (row : NativeOp) (env : List Val) (value : Val)
    (scope : Nat) (fin : FinName) : row.syncOpOf env value ≠ some (.scopeAdd scope fin) := by
  fun_cases NativeOp.syncOpOf row env value
  all_goals aesop

end Effect4.Program.SourceScope
