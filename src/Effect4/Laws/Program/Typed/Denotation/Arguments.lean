import Effect4.Laws.Program.Typed.Denotation.Terms
import Effect4.Laws.Program.Typed.StackCertificates
/-!
# Actual invoke argument certificates

Concept: residual-program-typing, R4, denote-typed.
The existing argument-site proof uses one certificate policy through the actual checkEffs clauses.
Its unit adapter keeps the old private argSites_typed statement.
Its ambient adapter issues requirement coverage at actual invocation birth.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
theorem argument_certificates {root : ProgramSource} {w : World} {env : List Ty}
    {vals : List Val} {base : List Nat} {stack : List (List ArgSite)}
    (policy : ParamDecl → EffTy → Prop)
    (henv : EnvTyped w env vals) (hstack : StackCertificates root w policy stack (scopeParams root.program base)) :
    ∀ (qs : List ParamDecl) (args : Effs NativeOp) (spine : List Nat) (T : EffTy),
      (∀ x, spine <+: x → scopeParams root.program x = scopeParams root.program base) →
      Node.at_ (.eff root.program) spine = some (.effs args) →
      qs.length = (effsRounds (Node.eff root.program)
        (List.range ((root.program.refSites []).length + 1)) args).toList.length →
      Checker.checkEffs (root.scopeSig base) env spine qs
          (effsRounds (Node.eff root.program)
            (List.range ((root.program.refSites []).length + 1)) args) = .ok T →
      (∀ parameter type, parameter.admits type = true →
        Row.Subset type.requires T.requires → policy parameter type) →
      ∀ (j : Nat) (q : ParamDecl), qs[j]? = some q →
        ∃ (site : ArgSite) (arg : NativeEff) (env' : List Ty) (t : EffTy),
          (argSitesAt spine vals args)[j]? = some site ∧
          Node.at_ (.eff root.program) site.path = some (.eff arg) ∧
          Checker.check (root.scopeSig site.path) (env' ++ [q.request.normalize]) site.path
            (Eff.expandIn root.program arg) = .ok t ∧
          policy q t ∧ EnvTyped w env' site.env ∧
          StackCertificates root w policy stack (scopeParams root.program site.path)
  | [], _, _, _, _, _, _, _, _, _, _, hq => by
    rw [List.getElem?_nil] at hq
    cases hq
  | _ :: _, .nil, _, _, _, _, hlen, _, _, _, _, _ => by
    rw [effsRounds_nil] at hlen
    exact absurd hlen (Nat.succ_ne_zero _)
  | q :: qs, .cons h t, spine, T, hscope, hat, hlen, hc, producer, j, q', hq => by
    rw [effsRounds_cons] at hc hlen
    obtain ⟨H, R, hch, hadm, hct, rfl⟩ := Checker.inv_effs_slot _ _ _ _ _ _ _ _ hc
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
      subst hq
      have hsite : scopeParams root.program (spine ++ [0]) = scopeParams root.program base :=
        hscope _ (List.prefix_append _ _)
      refine ⟨{ path := spine ++ [0], env := vals }, h, env, H, rfl, node_at_child hat rfl, ?_,
        producer q H hadm (Row.subset_union_left _ _), henv, ?_⟩
      · show Checker.check (root.scopeSig (spine ++ [0])) _ _ _ = _
        unfold ProgramSource.scopeSig
        rw [hsite]
        exact hch
      · show StackCertificates root w policy stack (scopeParams root.program (spine ++ [0]))
        rw [hsite]
        exact hstack
    | succ j =>
      simp only [List.getElem?_cons_succ] at hq
      exact argument_certificates policy henv hstack qs t (spine ++ [1]) R
        (fun x hx => hscope x ((List.prefix_append _ _).trans hx)) (node_at_child hat rfl)
        (Nat.succ.inj hlen) hct (fun parameter type admitted bound =>
          producer parameter type admitted (Row.subset_trans bound (Row.subset_union_right _ _))) j q' hq


/-- Actual checkEffs argument birth issues the ambient row annotation from the caller's
coverage. Consumer: ambient invoke and parameter execution in the original M5 source proof. -/
theorem ambient_argument_birth {root : ProgramSource} {w : World} {env : List Ty}
    {vals : List Val} {base : List Nat} {stack : List (List ArgSite)} {available : Env.Requirement}
    (values : EnvTyped w env vals)
    (saved : AmbientStackTyped root w available (scopeParams root.program base) stack)
    (parameters : List ParamDecl) (arguments : Effs NativeOp) (path : List Nat) (result : EffTy)
    (scope : ∀ x, path <+: x → scopeParams root.program x = scopeParams root.program base)
    (node : Node.at_ (.eff root.program) path = some (.effs arguments))
    (count : parameters.length = (effsRounds (Node.eff root.program)
      (List.range ((root.program.refSites []).length + 1)) arguments).toList.length)
    (checked : Checker.checkEffs (root.scopeSig base) env path parameters
      (effsRounds (Node.eff root.program) (List.range ((root.program.refSites []).length + 1)) arguments) =
        .ok result) (coverage : Row.Subset result.requires available) :
    AmbientStackTyped root w available parameters (argSitesAt path vals arguments :: stack) :=
  argument_certificates (fun parameter type =>
    parameter.admits type = true ∧ Row.Subset type.requires available)
    values saved parameters arguments path result scope node count checked
    (fun _ _ admitted required => ⟨admitted, Row.subset_trans required coverage⟩)
end Effect4.Program.Typed
