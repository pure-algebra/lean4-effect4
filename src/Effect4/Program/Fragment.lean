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
is in the fragment exactly when its row is a `sync` row. -/
def Straight : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .yieldError _ => true
  | .sync _ => true
  | .suspend b => Straight b
  | .perform op _ =>
    match (NativeOp.row op).kind with
    | .sync => true
    | _ => false
  | .bind a b => Straight a && Straight b
  | .branch _ a b => Straight a && Straight b
  | .select _ _ a b => Straight a && Straight b
  | .exit b => Straight b
  | .catchCause b h => Straight b && Straight h
  | .matchCause b v c => Straight b && Straight v && Straight c
  | .onExit b f => Straight b && Straight f
  | _ => false

end Effect4.Program.Denote
