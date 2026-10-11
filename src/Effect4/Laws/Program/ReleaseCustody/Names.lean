import Effect4.Laws.Program.ReleaseCustody

/-!
Concept: scope-lifetime-finalization, R11, at most once per registered source identity.
Question: residual-name projection used by the command custody clause of `Workers.Assertions.releases_step`.
Reach: the existing first-order ProgName, Name and ActionName syntax.
Limit: the projection proves no command preservation or source uniqueness by itself.
Unlock: stored finalizer programs and their wrappers retain credits before interpretation.
The structural equations follow existing recursive program slots; no program representation is added.
Lean rejects executable use of ProgName.rec; the receipt records the matcher exemption proposal.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Names
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.ReleaseCustody

/-- Credits in every stored program constructor, folded through its recursive program slots.
Consumer: `Control.currentCredits` and the structural stored-program interpretation law. -/
def progCredits (q : List Nat) : ProgName → Nat
  | .syncOp (.scopeAdd _ fin) => credit q fin
  | .intoDeferred body _ => progCredits q body
  | .intoBody body _ => progCredits q body
  | .finalizerOf fin _ => credit q fin
  | .onExitOf body fin _ => progCredits q body + credit q fin
  | .seqOf first second => progCredits q first + progCredits q second
  | .forkThen child _ _ => progCredits q child
  | .forkOnly child _ => progCredits q child
  | .forkInScope child _ _ => progCredits q child
  | .forkScopedOf child _ => progCredits q child
  | .awaitAllNew body => progCredits q body
  | .closeWalk _ order _ => orderCredits q order
  | _ => 0

/-- The two store continuations that retain another program retain its credits.
Consumer: `Control.currentCredits` and `Control.futureCredits`. -/
def contCredits (q : List Nat) : Name → Nat
  | .seq next => progCredits q next
  | .snapshotThen body => progCredits q body
  | _ => 0

/-- Forks and masked bodies retain their stored programs until the action transfers them.
Consumer: `Control.currentCredits`. -/
def actionCredits (q : List Nat) : ActionName → Nat
  | .fork program _ => progCredits q program
  | .forkIn program _ _ => progCredits q program
  | .forkScoped program _ => progCredits q program
  | .setInterruptible body _ => progCredits q body
  | .closePar order _ => orderCredits q order
  | _ => 0

end Effect4.Program.ReleaseCustody.Names
