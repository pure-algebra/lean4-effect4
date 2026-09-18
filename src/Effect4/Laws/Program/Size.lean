import Effect4.Program.LayerView

/-!
# Laws.Program.Size — the size of a program, by a fold

One measure for every whole-program fold that reasons by "the children are smaller": the node
count `sizeAlg` (one more than the children, by the generic layer function), the lemma that a
child listed by the view is smaller (`size_child_lt`), and that a node counts itself
(`size_pos`). A law about a fold is then one generic node step under strong induction on the
count, and no constructor is named. Used by the printer's completeness
(`Laws/Codegen/PrintReadable.lean`) and the supervision table (`Laws/Api/Supervision.lean`).
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- One more than the children: the size of a node by the generic layer function. -/
def sizeLayer : (fam : EffFam) → String → List (ArgF Op (fun _ => Nat)) → Nat
  | _, _, args => 1 + (args.map fun a => match a with | .child _ k => k | _ => 0).sum

def sizeAlg : EffAlgebra Op (fun _ => Nat) := EffAlgebra.ofLayer sizeLayer

theorem sizeLayer_eq (fam : EffFam) (ctor : String) (args : List (ArgF Op (fun _ => Nat))) :
    sizeLayer fam ctor args =
      1 + (args.map fun a => match a with | .child _ k => k | _ => 0).sum := rfl

theorem le_sum_of_mem : ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ l.sum
  | [], _, h => by cases h
  | b :: rest, a, h => by
    have ih := le_sum_of_mem rest a
    simp only [List.mem_cons, List.sum_cons] at h ⊢
    rcases h with rfl | h
    · omega
    · have := ih h; omega

/-- Every node counts at least itself. -/
theorem size_pos (fam : EffFam) (e : EffSelfCarrier Op fam) : 0 < cataFam sizeAlg fam e := by
  have hb := cata_build sizeLayer fam (view fam e).1 (view fam e).2 e (build_view fam e)
  rw [show sizeAlg = EffAlgebra.ofLayer sizeLayer from rfl, hb, sizeLayer_eq]
  omega

/-- A child is smaller than its node. -/
theorem size_child_lt (fam : EffFam) (e : EffSelfCarrier Op fam) (fam' : EffFam)
    (c : EffSelfCarrier Op fam') (h : ArgF.child fam' c ∈ (view fam e).2) :
    cataFam sizeAlg fam' c < cataFam sizeAlg fam e := by
  have hb := cata_build sizeLayer fam (view fam e).1 (view fam e).2 e (build_view fam e)
  rw [show sizeAlg = EffAlgebra.ofLayer sizeLayer from rfl, hb, sizeLayer_eq]
  have hmem : cataFam (EffAlgebra.ofLayer sizeLayer) fam' c ∈
      ((view fam e).2.map (ArgF.fold (EffAlgebra.ofLayer sizeLayer))).map
        (fun a : ArgF Op (fun _ => Nat) => match a with | .child _ k => k | _ => 0) := by
    rw [List.map_map]
    exact List.mem_map.mpr ⟨.child fam' c, h, rfl⟩
  have := le_sum_of_mem _ _ hmem
  omega

end Effect4.Program
