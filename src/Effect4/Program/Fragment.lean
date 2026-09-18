import Effect4.Program.Native

/-!
# Program.Fragment — executable membership in the proved program fragment

`Straight` is shared by computed admission and the separate denotation proofs.
It retains its original namespace and accepted constructors. Membership alone
asserts neither typing nor execution safety; those require admission and the
corresponding theorems in the Laws graph.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- The straight-line fragment: one fiber, no park, no fork, no loop, no tape. A `perform`
is in the fragment exactly when its row is a `sync` row. Every constructor is named (no
wildcard arm), so a constructor added to `Eff` is a missing case here until it is classified
(row 35, the fragment by exclusion). -/
def Straight : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .sync _ => true
  | .suspend b => Straight b
  | .perform op _ =>
    match (NativeOp.row op).kind with
    | .sync => true
    | _ => false
  | .bind a b => Straight a && Straight b
  | .select _ _ a b => Straight a && Straight b
  | .exit b => Straight b
  | .catchCause b h => Straight b && Straight h
  | .matchCause b v c => Straight b && Straight v && Straight c
  | .onExit b f => Straight b && Straight f
  | .gen _ => false
  | .uninterruptible _ => false
  | .interruptible _ => false
  | .yieldNow _ => false
  | .awaitFiber _ _ => false
  | .withFiber _ => false
  | .scoped _ => false
  | .acquireRelease _ _ => false
  | .provideLayer _ _ _ => false
  | .service _ => false
  | .provideService _ _ _ => false
  | .catchIf _ _ _ => false
  | .iterate _ _ _ _ _ _ => false

end Effect4.Program.Denote
