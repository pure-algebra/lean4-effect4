import Effect4.Codegen.PrintTyped
import Effect4.Laws.Program.Typing.Call
import Effect4.Laws.Program.Typing.Focus

/-!
# Laws.Codegen.PrintTyped — the typed print is the print while the guards stand

The typed print's slice P2a (`docs/research/2026-10-07-typed-print-design.md`, the addendum).
At the empty annotation the typed print is the print, by the uniqueness of the fold
(`printTypedAt_none`). While the guards stand, the annotation answers nothing at any address
(`typeArgsAt_none`): a typed call's guarded match answers. So the typed print of every program
is its print, byte for byte (`printTyped_eq_print`).
-/

set_option autoImplicit false

namespace Effect4.Codegen.Templates

open Effect4.Program

variable {Op : Type}

/-- The plain print at every address is a homomorphism into the typed print's algebra at the
empty annotation: each field is its definition. A step of `printTypedAt_none`, the claim
`typed-print-connector`. -/
def noneHom (sig : Signature Op) : EffHom (typedAlg sig (fun _ => none)) := by
  refine'
    { f_eff := fun e _ => cata_eff (printAlg sig) e
      f_stmt := fun s _ => cata_stmt (printAlg sig) s
      f_stmts := fun s _ => cata_stmts (printAlg sig) s
      f_effs := fun s _ => cata_effs (printAlg sig) s
      f_action := fun a _ => cata_action (printAlg sig) a
      f_layer := fun l _ => cata_layer (printAlg sig) l
      f_layers := fun l _ => cata_layers (printAlg sig) l
      .. }
  all_goals (intros; rfl)

/-- **At the empty annotation the typed print is the print**, at every program and environment
length, by the uniqueness of the fold (`hom_eq_cata_eff`). A step of `printTyped_eq_print`; it
says nothing at an annotation that answers. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem printTypedAt_none (sig : Signature Op) (n : Nat) (e : Eff Op) :
    printTypedAt sig (fun _ => none) n e = print sig n e := by
  unfold printTypedAt
  rw [← hom_eq_cata_eff (noneHom sig) e]
  rfl

end Effect4.Codegen.Templates

namespace Effect4.Program

variable {Op : Type}

/-- **While the guards stand, the annotation answers nothing**: at a typed call the row check
answers, so the guarded match answers (`checkRow_rowBindings`), and no binding is a join. A
step of `printTyped_eq_print`. It is false after UNGUARD, where the checker types a call at a
join. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem typeArgsAt_none (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    typeArgsAt s env0 p path = none := by
  unfold typeArgsAt
  cases hf : focusAt s env0 p path with
  | none => rfl
  | some focus =>
    obtain ⟨-, typed⟩ := focusAt_typed hf
    simp only [Option.bind_some]
    split
    · rename_i op request hprogram
      rw [hprogram] at typed
      cases typed with
      | perform hdom hterm hrow =>
        rw [hterm, Option.bind_some]
        obtain ⟨σ, hσ, -, -⟩ := checkRow_rowBindings (Effect4.Laws.Auto.toOption_eq_some.mp hrow)
        rw [hσ]
    · rfl

/-- **The typed print of every program is its print**, byte for byte, while the guards stand:
no call prints a type argument it did not print before. The pointer of the claim
`typed-print-connector`. Its consumer is UNGUARD, which removes the guards and leaves this as
the connector under no join. It does not say that tsgo accepts a printed call. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem printTyped_eq_print (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    printTyped s env0 p = print s env0.length p := by
  unfold printTyped
  rw [show typeArgsAt s env0 p = fun _ => none from funext (typeArgsAt_none s env0 p)]
  exact Effect4.Codegen.Templates.printTypedAt_none s env0.length p

end Effect4.Program
