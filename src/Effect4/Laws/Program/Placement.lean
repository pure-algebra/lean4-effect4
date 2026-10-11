import Effect4.Program.NodeLenses
import Effect4.Program.Native

/-!
# Static paths for control linearity

Placement: scope-lifetime-finalization, R11.
These predicates serve the proposed control-linearity claim.
Consumers: the two crews' static acquisition facts and the control-linearity goals.
They classify stored syntax. A true predicate alone establishes no execution count,
progress, finalization or host observation. Decisions rows 254 and 275 bound the consumers.
-/

namespace Effect4.Program

/-- Whether a node runs its child at this index at most once each time the node itself runs.
Excluded: an `iterate`'s body, a `whileTrue`'s statements, the definition bodies and the
invocation arguments (each can run many times per run of the node), and the layers (a memo
build is shared). -/
def onceChild : Node NativeOp → Nat → Bool
  | .eff (.suspend _), 0 => true
  | .eff (.bind _ _), _ => true
  | .eff (.gen _), 0 => true
  | .eff (.catchCause _ _), _ => true
  | .eff (.matchCause _ _ _), _ => true
  | .eff (.onExit _ _), _ => true
  | .eff (.exit _), 0 => true
  | .eff (.uninterruptible _), 0 => true
  | .eff (.interruptible _), 0 => true
  | .eff (.withFiber _), 0 => true
  | .eff (.scoped _), 0 => true
  | .eff (.acquireRelease _ _), _ => true
  | .eff (.provideLayer _ _ _), 1 => true
  | .eff (.provideService _ _ _), 0 => true
  | .eff (.catchIf _ _ _), _ => true
  | .eff (.select _ _ _ _), _ => true
  | .eff (.restore _ _), 0 => true
  | .eff (.defs _ _ _ _), 1 => true
  | .action (.fork _ _), 0 => true
  | .action (.forkIn _ _ _), 0 => true
  | .action (.forkScoped _ _), 0 => true
  | .action (.raceAll _), 0 => true
  | .effs (.cons _ _), _ => true
  | .stmts (.cons _ _), _ => true
  | .stmt (.bindYield _), 0 => true
  | .stmt (.yieldDiscard _), 0 => true
  | .stmt (.ifElse _ _ _), _ => true
  | _, _ => false

/-- **A once-placed node.** Every step of its path from the root is a once step, as required by the proposed
control-linearity claim. A static, decidable test of the program tree. -/
def OncePlaced : Node NativeOp → List Nat → Bool
  | _, [] => true
  | n, i :: rest =>
    onceChild n i &&
      match n.child i with
      | some c => OncePlaced c rest
      | none => false

/-- A node once-placed below a fork's program: the walk starts at the node at `site`, the
program that a fiber forked there runs. -/
def OncePlacedBelow (root : Node NativeOp) (site : List Nat) (q : List Nat) : Bool :=
  site.isPrefixOf q &&
    match root.at_ site with
    | some n => OncePlaced n (q.drop site.length)
    | none => false

end Effect4.Program
