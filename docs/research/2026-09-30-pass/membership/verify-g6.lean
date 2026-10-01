import Effect4.Laws.Program.Typed.Assembly

/-!
# Verifier probe: what G6 costs, concretely

Adversarial verifier of seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. The seat's G6
(`Gaps.lean:347-361`) separates the judgments on the native spelling `Ref.Ref<number>`, and its
D2 reads the consequence: under `StrongValue`, M6 cannot type a native `Ref.get` reached through
a variable. Here that reading is made concrete. At a checked point whose environment holds a
cell declared `bool`, D13 source admission (`PointTyped`) holds, because `StrongValue` at
`Ref.Ref<number>` never looks at the declaration; yet the loaded code of that point has no
`TypedProg` at the checker's type. So the bridge M6 needs from checker admission to program
typing (for a forked or scoped body) fails under `StrongValue`. Under the seat's `Fits` the
premise itself fails at this world (`g6_refused`).
-/

set_option autoImplicit false

namespace Research.Pass.Membership.VerifyG6
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

abbrev W := Effect4.Program.Typed.World

/-- `Ref.make(5).flatMap(r => Ref.get(r))`; its node at `[1]` reads `r`. -/
def getProg : NativeEff := .bind (.perform .refMake (.lit (.nat 5))) (.perform .refGet (.var 0))
def readNode : NativeEff := .perform .refGet (.var 0)

/-- The read's point, its environment holding cell 0. -/
def pt : Point := { (rootPoint 20) with path := [1], env := [Val.cell ⟨0⟩] }

/-- Cell 0 declared at `bool`, holding `true`. -/
def wBool : W :=
  { ids := [], state := { Stores.empty with refs := [.bool true] },
    Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .bool, Θ := fun _ _ => none }

theorem wBool_zero : wBool.Ρ ⟨0⟩ = some .bool :=
  insert_here (fun _ : RefKey => (none : Option Ty)) ⟨0⟩ Ty.bool

theorem read_checks :
    Checker.check (nativeSignature []) [.handle NativeOp.refTarget] [1] readNode =
      .ok (EffTy.pure .nat) := by decide +kernel

/-- `StrongValue` at the native spelling accepts the cell whatever its declaration. -/
theorem cell_strong : StrongValue wBool (.handle NativeOp.refTarget) (Val.cell ⟨0⟩) := by
  refine ⟨rfl, (fun _ ctx hctx => nomatch hctx), (fun k hk => ?_)⟩
  rw [Val.keys_cell, List.mem_singleton] at hk
  subst hk
  exact Nat.zero_lt_one

/-- Checker admission of the read holds at `wBool`. -/
theorem point_typed : PointTyped (getProg : ProgramSource) wBool pt (EffTy.pure .nat) := by
  refine ⟨readNode, [.handle NativeOp.refTarget], rfl, read_checks, rfl, ?_⟩
  intro i ty v hty hv
  cases i with
  | zero =>
    change some (Ty.handle NativeOp.refTarget) = some ty at hty
    change some (Val.cell ⟨0⟩) = some v at hv
    cases hty
    cases hv
    exact cell_strong
  | succ j =>
    change ([] : List Ty)[j]? = some ty at hty
    rw [List.getElem?_nil] at hty
    cases hty

theorem read_code :
    denoteR getProg readNode pt = .vis (.inl (.refGet ⟨0⟩)) fun v => .pure (.success v) := rfl

/-- **The bridge fails**: admitted by the checker, untypable as a program. -/
theorem admitted_but_untypable :
    PointTyped (getProg : ProgramSource) wBool pt (EffTy.pure .nat) ∧
      ¬ TypedProg (getProg : ProgramSource) wBool (EffTy.pure .nat) (denoteR getProg readNode pt) := by
  refine ⟨point_typed, fun h => ?_⟩
  rw [read_code] at h
  obtain ⟨_, _, next⟩ := TypedProg.store_inv h
  have post : (Ψ_S (getProg : ProgramSource)).post wBool (.refGet ⟨0⟩) () (Val.bool true) :=
    ⟨.bool, wBool_zero, strongValue_bool_true wBool⟩
  have hex := TypedProg.pure_inv (next wBool (leHost_refl wBool) _ post)
  exact Bool.noConfusion hex.1

/-- Red control: at a world declaring cell 0 at `nat`, the same read is typed. -/
def wNat : W :=
  { ids := [], state := { Stores.empty with refs := [.nat 7] },
    Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .nat, Θ := fun _ _ => none }

theorem wNat_zero : wNat.Ρ ⟨0⟩ = some .nat :=
  insert_here (fun _ : RefKey => (none : Option Ty)) ⟨0⟩ Ty.nat

theorem read_typed_nat :
    TypedProg (getProg : ProgramSource) wNat (EffTy.pure .nat) (denoteR getProg readNode pt) := by
  rw [read_code]
  refine TypedProg.store (cert := ()) ⟨.nat, wNat_zero⟩ ?_
  intro w' hle ans hpost
  obtain ⟨ty, hty, hv⟩ := hpost
  have hsame : w'.Ρ ⟨0⟩ = some .nat := hle.1.2.2.2.1 _ _ wNat_zero
  change w'.Ρ ⟨0⟩ = some ty at hty
  rw [hsame] at hty
  cases hty
  exact TypedProg.pure (strongExit_success w' _ ans hv)

#print axioms read_checks
#print axioms cell_strong
#print axioms point_typed
#print axioms read_code
#print axioms admitted_but_untypable
#print axioms wBool_zero
#print axioms wNat_zero
#print axioms read_typed_nat

end Research.Pass.Membership.VerifyG6
