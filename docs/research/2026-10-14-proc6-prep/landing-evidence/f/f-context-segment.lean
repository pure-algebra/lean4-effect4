import Effect4.Laws.Program.Agreement.Segment

/-!
# Receipt-conditioned context segments

Concept: translation-simulation. Claim: rows-block-host, requirement R6.
The consumer is the hosted decision proof in Agreement/Hosted.lean.
The fragment admits plain hooks, one root and quiet stores at every context.
An actual command receipt supplies completion. These laws supply no progress bound.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-- A completed segment's three forms retain its actual context and observation.
Only the completed exit omits context from its local observation. -/
def ContextSegOwes (root : NativeEff) (table : RowTable) (fr : NFiber) (s : Stores)
    (ctx : Ctx) (result : Api.Machine) : Prop :=
  (∃ ex s' fr' k tr nt ctx', result = Mexit root ex fr' s' k tr nt ctx' ∧ Quiet s' ∧
    (∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r : σ),
      ∃ c, localRunC host root c fr s r ctx = some (.exit ex s' r))) ∨
  (∃ cur K i s' k tr nt ctx', result = Mcall (fiberOf cur K i) s' k tr nt ctx' ∧
    IsCall cur = true ∧ PlainStack K ∧ Quiet s' ∧
    ∃ c, ReachesQ (table := table) root c fr s (fiberOf cur K i) s' ctx ctx') ∨
  (∃ cur K i s' k tr nt ctx', result = Myield (fiberOf cur K i) s' k tr nt ctx' ∧
    PlainCode cur = true ∧ PlainStack K ∧ Quiet s' ∧
    ∃ c, ReachesQ (table := table) root c fr s (fiberOf cur K i) s' ctx ctx')

/-- The actual receipt, including the machine's refusal alternative, closes a segment.
Plain hooks rule out that refusal alternative in the conclusion.
Consumer: hosted evaluate, flush and answer; rows-block-host/R6. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal drive_seg_receipt (root : NativeEff) (hroot : PlainHooks root)
    (fuel : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) (ctx : Ctx) (d : Bool)
    (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hd : d = true → (∀ t, cur ≠ Prim.sync t) ∧ IsCall cur = false)
    (hreceipt : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel (M (fiberOf cur K i) s k tr nt ctx)
      [cmdOf d, Cmd.drainDue]) = true) :
    ∃ result, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] = (result, []) ∧
      ContextSegOwes root table (fiberOf cur K i) s ctx result

end Effect4.Program.Agreement
