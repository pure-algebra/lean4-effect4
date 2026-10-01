import Effect4.Laws.Program.Typed.Residual

/-!
# Verifier probe: the seat's `OldMono` proofs close the ledger's own obligations

Adversarial verifier of seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. `OldMono.lean:19-113`
is copied verbatim below (namespace renamed only). `#obligation_proved` then elaborates each
proof against the proposition the ledger reads from `M3bWorld.strongValue_mono` and
`M3bWorld.strongExit_mono` (`Typed/Residual.lean:424-428`), the tree's own check. The red control
shows the same elaboration refuses the wrong proof.
-/

set_option autoImplicit false

namespace Research.Pass.Membership.VerifyOldMono
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

abbrev W := Effect4.Program.Typed.World

theorem isSome_extends {K A : Type} {t1 t2 : K → Option A} (ht : TableExtends t1 t2) {k : K}
    (h : (t1 k).isSome = true) : (t2 k).isSome = true := by
  cases hs : t1 k with
  | none => rw [hs] at h; cases h
  | some a => rw [ht k a hs]; rfl

theorem handlesLive_mono {w w' : W} (ordered : w.leHost w') {v : Val} (h : HandlesLive w v) :
    HandlesLive w' v := by
  intro k hk
  have hk' := h k hk
  cases k with
  | cell key => exact Nat.lt_of_lt_of_le hk' ordered.1.1.2.1
  | promise key => exact Nat.lt_of_lt_of_le hk' ordered.1.1.2.2.1
  | fiber id => exact isSome_extends ordered.1.2.1 hk'
  | scope _ => trivial
  | memoMap _ => trivial
  | external _ => trivial

theorem servicesOk_mono {w w' : W} (ordered : w.leHost w') {services : Env.Ctx}
    (h : ServicesOk w services) : ServicesOk w' services :=
  fun key sv sty hget hty =>
    ⟨valueOk_mono w w' sty sv ordered (h key sv sty hget hty).1,
      handlesLive_mono ordered (h key sv sty hget hty).2⟩

theorem handlesFit_mono {w w' : W} (ordered : w.leHost w') :
    ∀ (ty : Ty) (v : Val), HandlesFit w v ty → HandlesFit w' v ty := by
  intro ty
  induction ty with
  | refOf t _ =>
    intro v h key hk
    exact ordered.1.2.2.2.1 key t (h key hk)
  | deferredOf a e _ _ =>
    intro v h key hk
    exact ordered.1.2.2.1 key (a, e) (h key hk)
  | fiberOf a e _ _ =>
    intro v h id hid
    obtain ⟨fty, hs, ha, he⟩ := h id hid
    exact ⟨fty, ordered.1.2.1 id fty hs, ha, he⟩
  | prod a b iha ihb =>
    intro v h
    simp only [HandlesFit] at h ⊢
    split at h
    · exact ⟨iha _ h.1, ihb _ h.2⟩
    · trivial
  | option a ih =>
    intro v h
    simp only [HandlesFit] at h ⊢
    split at h
    · exact ih _ h
    · trivial
  | list a ih =>
    intro v h
    simp only [HandlesFit] at h ⊢
    split at h
    · exact fun x hx => ih x (h x hx)
    · trivial
  | union l r ihl ihr =>
    intro v h
    exact h.imp (ihl v) (ihr v)
  | unknown => intro v h; exact handlesLive_mono ordered h
  | handle s =>
    intro v h hs ctx hctx
    exact servicesOk_mono ordered (h hs ctx hctx)
  | never => intro v _; trivial
  | unit => intro v _; trivial
  | nat => intro v _; trivial
  | int => intro v _; trivial
  | string => intro v _; trivial
  | bool => intro v _; trivial
  | except e a _ _ => intro v _; trivial
  | exitOf a e _ _ => intro v _; trivial
  | causeOf e _ => intro v _; trivial
  | lit _ => intro v _; trivial
  | var _ => intro v _; trivial

/-- The declared obligation `M3bWorld.strongValue_mono`, proved for the old judgment. -/
theorem strongValue_mono (w w' : W) (ty : Ty) (v : Val) (ordered : w.leHost w')
    (h : StrongValue w ty v) : StrongValue w' ty v :=
  ⟨valueOk_mono w w' ty v ordered h.1, handlesFit_mono ordered ty v h.2.1,
    handlesLive_mono ordered h.2.2⟩

/-- The declared obligation `M3bWorld.strongExit_mono`, proved for the old judgment. -/
theorem strongExit_mono (w w' : W) (ty : EffTy) (ex : ExitV) (ordered : w.leHost w')
    (h : StrongExit w ty ex) : StrongExit w' ty ex := by
  refine ⟨exitFits_mono w w' ty ex ordered h.1, fun v hv => ?_, fun c hc => ?_⟩
  · exact strongValue_mono w w' _ v ordered (h.2.1 v hv)
  · intro r hr
    have hr' := h.2.2 c hc r hr
    cases r with
    | fail e ann =>
      obtain ⟨v, hv, hs⟩ := hr'
      exact ⟨v, hv, strongValue_mono w w' _ v ordered hs⟩
    | die _ _ => trivial
    | interrupt _ _ => trivial


#print axioms isSome_extends
#print axioms handlesLive_mono
#print axioms servicesOk_mono
#print axioms handlesFit_mono
#print axioms strongValue_mono
#print axioms strongExit_mono

end Research.Pass.Membership.VerifyOldMono

#obligation_proved Effect4.Program.Typed.M3bWorld.strongValue_mono :=
  @Research.Pass.Membership.VerifyOldMono.strongValue_mono
#obligation_proved Effect4.Program.Typed.M3bWorld.strongExit_mono :=
  @Research.Pass.Membership.VerifyOldMono.strongExit_mono

#print axioms Effect4.Program.Typed.M3bWorld.strongValue_mono.checked
#print axioms Effect4.Program.Typed.M3bWorld.strongExit_mono.checked

/- Red control: the exit proof does not elaborate against the value obligation. -/
open Lean Meta Elab Command in
#eval show CommandElabM Unit from liftTermElabM do
  let info ← getConstInfo ``Effect4.Program.Typed.M3bWorld.strongValue_mono
  let prop ← forallTelescope info.type fun xs body => do
    unless body.isAppOfArity ``ProofGraph.Obligation 1 do throwError "not an obligation"
    mkForallFVars xs body.appArg!
  let good ← getConstInfo ``Research.Pass.Membership.VerifyOldMono.strongValue_mono
  let bad ← getConstInfo ``Research.Pass.Membership.VerifyOldMono.strongExit_mono
  unless ← isDefEq good.type prop do throwError "the value proof does not match"
  if ← isDefEq bad.type prop then throwError "control failed: the exit proof matched"
  logInfo m!"red control: strongExit_mono's type is refused where strongValue_mono's is accepted"
