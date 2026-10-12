import Effect4.Laws.Program.Typed.Residual

/-!
# Shared typed-stack certificate policies

Concept: residual-program-typing, R4, denote-typed.
The ambient M5 input uses the existing stack certificate fold with a requirement-row policy.
The existing unit StackTyped and PointTyped interfaces remain unchanged.
The actual invoke producer supplies this evidence from checkEffs before parameter execution.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- One certificate fold transports every policy implication.
Consumer: ambient stack erasure and available-row extension in the M5 source proof. -/
theorem StackCertificates.policy_map (root : ProgramSource) (world : World)
    {before after : ParamDecl → EffTy → Prop}
    (maps : ∀ parameter type, before parameter type → after parameter type)
    (stack : List (List ArgSite)) : ∀ declarations,
    StackCertificates root world before stack declarations →
      StackCertificates root world after stack declarations := by
  induction stack with
  | nil => intro declarations typed; exact typed
  | cons sites stack ih =>
    intro declarations typed index parameter found
    obtain ⟨site, program, environment, type, here, node, checked, admitted, values, rest⟩ :=
      typed index parameter found
    exact ⟨site, program, environment, type, here, node, checked,
      maps parameter type admitted, values, ih _ rest⟩


/-- The shared stack fold transports actual environment membership to a later world.
Consumer: suspended source callbacks and captured parameter inputs in ambient M5. -/
theorem StackCertificates.mono {w w' : World} (ordered : w.leHost w')
    (root : ProgramSource) (policy : ParamDecl → EffTy → Prop) (stack : List (List ArgSite)) :
    ∀ declarations, StackCertificates root w policy stack declarations →
      StackCertificates root w' policy stack declarations := by
  induction stack with
  | nil => intro declarations typed; exact typed
  | cons sites stack ih =>
    intro declarations typed index parameter found
    obtain ⟨site, program, environment, type, here, node, checked, admitted, values, rest⟩ :=
      typed index parameter found
    exact ⟨site, program, environment, type, here, node, checked, admitted,
      envTyped_mono ordered values, ih _ rest⟩

/-- Ambient stack evidence retains the unchanged unit stack judgment.
Consumer: the original value and view typing producers used by source admission. -/
theorem ambientStackTyped_erases {root : ProgramSource} {w : World} {available : Env.Requirement}
    {declarations : List ParamDecl} {stack : List (List ArgSite)}
    (typed : AmbientStackTyped root w available declarations stack) :
    StackTyped root w declarations stack :=
  StackCertificates.policy_map root w (fun _ _ admitted => admitted.1) stack declarations typed

/-- Ambient stack evidence survives world growth through the same certificate fold.
Consumer: actual completed-view construction after suspension or a saved source callback. -/
theorem ambientStackTyped_mono {root : ProgramSource} {w w' : World} (ordered : w.leHost w')
    {available : Env.Requirement} {declarations : List ParamDecl} {stack : List (List ArgSite)}
    (typed : AmbientStackTyped root w available declarations stack) :
    AmbientStackTyped root w' available declarations stack :=
  StackCertificates.mono ordered root _ stack declarations typed

/-- Enlarging the available row retains every actual passed-program requirement.
Consumer: source providers preserve the captured argument stack while extending its context. -/
theorem ambientStackTyped_widen {root : ProgramSource} {w : World}
    {available later : Env.Requirement} (bound : Row.Subset available later)
    {declarations : List ParamDecl} {stack : List (List ArgSite)}
    (typed : AmbientStackTyped root w available declarations stack) :
    AmbientStackTyped root w later declarations stack :=
  StackCertificates.policy_map root w (fun _ _ admitted =>
    ⟨admitted.1, Row.subset_trans admitted.2 bound⟩) stack declarations typed

/-- With no parameters in scope the shared fold constrains no argument.
Consumer: the unchanged closed M5 load constructs its actual entry input. -/
theorem ambientStackTyped_nil (root : ProgramSource) (w : World) (available : Env.Requirement)
    (stack : List (List ArgSite)) : AmbientStackTyped root w available [] stack := by
  cases stack with
  | nil => rfl
  | cons sites rest =>
    intro index parameter absent
    rw [List.getElem?_nil] at absent
    exact nomatch absent

/-- The refined point input transports its existing fields and shared stack annotation.
Consumer: actual saved callback and child-source entries in ambient M5. -/
theorem ambientPointTyped_mono {root : ProgramSource} {w w' : World} (ordered : w.leHost w')
    {available : Env.Requirement} {point : Point} {type : EffTy}
    (typed : AmbientPointTyped root w available point type) :
    AmbientPointTyped root w' available point type :=
  ⟨pointTyped_mono ordered typed.1, ambientStackTyped_mono ordered typed.2⟩

/-- The same point input admits a larger available row without changing its type certificate.
Consumer: actual provider installed-map coverage in the ambient source denotation proof. -/
theorem ambientPointTyped_widen {root : ProgramSource} {w : World}
    {available later : Env.Requirement} (bound : Row.Subset available later)
    {point : Point} {type : EffTy} (typed : AmbientPointTyped root w available point type) :
    AmbientPointTyped root w later point type :=
  ⟨typed.1, ambientStackTyped_widen bound typed.2⟩

end Effect4.Program.Typed
