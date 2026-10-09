import Effect4.Laws.Program.Folds.Straight
import Effect4.Laws.Program.Folds.Looped
import Effect4.Laws.Program.Folds.DenoteRows

/-! Independent retained predicate definitions from git:1f4ee194.
The agreement checks use fold uniqueness and algebra equality, without a pairwise induction.
Placement: initial-algebras-folds, hom-eq-cata-eff, compatibility helpers for the R8 fragments.
They assert only predicate equality, not execution agreement or host conformance. -/

namespace FragmentBaseline
open Effect4 Effect4.Machine Effect4.Program

def Straight : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .sync _ => true
  | .suspend b => Straight b
  | .perform op _ =>
    match op.kind with
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
  -- a restore site sets the fiber's mask when its saved bit is true: outside, as the two masks
  | .restore _ _ => false
  -- a definition block's invocations run a body on the invoking fiber (decisions row 328)
  | .defs _ _ _ => false


def Looped : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .sync _ => true
  | .perform op _ =>
    match op.kind with
    | .sync => true
    | _ => false
  | .iterate _ _ _ _ _ body => Looped body
  | .suspend b => Looped b
  | .bind a b => Looped a && Looped b
  | .select _ _ a b => Looped a && Looped b
  | .exit b => Looped b
  | .catchCause b h => Looped b && Looped h
  | .matchCause b v c => Looped b && Looped v && Looped c
  | .onExit b f => Looped b && Looped f
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
  | .restore _ _ => false
  -- a definition block's invocations hop into a body (decisions row 328)
  | .defs _ _ _ => false



def dataRow (table : RowTable) (i : Nat) : Bool :=
  match externalRow table i with
  | some row => match row.answer with
    | .handle _ => false
    | _ => true
  | none => false

/-- **Straight-line plus host rows on one fiber** (DI-69): `Straight`, with one more admitted
leaf, a `perform` of a host row of the table. Every constructor is named (decisions row 35). -/
def StraightRows (table : RowTable) : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .sync _ => true
  | .suspend b => StraightRows table b
  | .perform op _ =>
    match op with
    | .external i => dataRow table i
    | _ => match op.kind with
      | .sync => true
      | _ => false
  | .bind a b => StraightRows table a && StraightRows table b
  | .select _ _ a b => StraightRows table a && StraightRows table b
  | .exit b => StraightRows table b
  | .catchCause b h => StraightRows table b && StraightRows table h
  | .catchIf _ b h => StraightRows table b && StraightRows table h
  | .matchCause b v c => StraightRows table b && StraightRows table v && StraightRows table c
  | .onExit b f => StraightRows table b && StraightRows table f
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
  | .iterate _ _ _ _ _ _ => false
  | .restore _ _ => false
  -- a definition block's invocations hop into a body (decisions row 328)
  | .defs _ _ _ => false



fold_of FragmentBaseline.Straight
fold_of FragmentBaseline.Looped
fold_of FragmentBaseline.StraightRows (family := Effect4.Program.Eff)

-- Same algebra fields, not only agreement on the finite examples.
theorem straight_unchanged (e : NativeEff) : Straight e = Denote.Straight e := by
  rw [Straight.eq_cata, Denote.Straight.eq_cata]
  rfl

theorem looped_unchanged (e : NativeEff) : Looped e = Denote.Looped e := by
  rw [Looped.eq_cata, Denote.Looped.eq_cata]
  rfl

theorem rows_unchanged (table : RowTable) (e : NativeEff) :
    StraightRows table e = Denote.StraightRows table e := by
  rw [StraightRows.eq_cata, Denote.StraightRows.eq_cata]
  rfl

#print axioms straight_unchanged
#print axioms looped_unchanged
#print axioms rows_unchanged
#print axioms Effect4.Program.Denote.Straight.eq_cata
#print axioms Effect4.Program.Denote.Looped.eq_cata
#print axioms Effect4.Program.Denote.StraightRows.eq_cata

end FragmentBaseline
