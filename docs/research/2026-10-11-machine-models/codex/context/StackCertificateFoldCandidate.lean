import Effect4.Laws.Program.Typed.Denotation.Terms
set_option autoImplicit false
namespace Test.StackCertificateFoldCandidate
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- Placement: residual-program-typing, R4, denote-typed. Consumer: the ambient parameter-call
input and its unit erasure. This candidate factors one existing stack clause into a list fold. -/
def certificates (root : ProgramSource) (world : Typed.World)
    (policy : ParamDecl → EffTy → Prop) (stack : List (List ArgSite)) : List ParamDecl → Prop :=
  stack.foldr (fun (sites : List ArgSite) (rest : List ParamDecl → Prop) (declarations : List ParamDecl) =>
    ∀ (index : Nat) (parameter : ParamDecl), declarations[index]? = some parameter →
      ∃ (site : ArgSite) (program : NativeEff) (environment : List Ty) (type : EffTy), sites[index]? = some site ∧
        Node.at_ (.eff root.program) site.path = some (.eff program) ∧
        Checker.check (root.scopeSig site.path) (environment ++ [parameter.request.normalize])
          site.path (Eff.expandIn root.program program) = .ok type ∧
        policy parameter type ∧ EnvTyped world environment site.env ∧
        rest (scopeParams root.program site.path)) (fun declarations => declarations = [])

/-- Placement: the unit specialization has exactly the existing stack meaning. Consumer:
unchanged StackTyped callers if this candidate replaces its recursive definition. -/
theorem unit_agreement (root : ProgramSource) (world : Typed.World)
    (stack : List (List ArgSite)) : ∀ declarations,
    certificates root world (fun parameter type => parameter.admits type = true) stack declarations ↔
      StackTyped root world declarations stack := by
  induction stack with
  | nil => intro declarations; rfl
  | cons sites stack ih =>
    intro declarations
    constructor
    · intro typed index parameter found
      obtain ⟨site, program, environment, type, here, node, checked, admitted, values, rest⟩ :=
        typed index parameter found
      exact ⟨site, program, environment, type, here, node, checked, admitted, values,
        (ih _).mp rest⟩
    · intro typed index parameter found
      obtain ⟨site, program, environment, type, here, node, checked, admitted, values, rest⟩ :=
        typed index parameter found
      exact ⟨site, program, environment, type, here, node, checked, admitted, values,
        (ih _).mpr rest⟩

/-- Placement: one fold transports every certificate policy implication. Consumer: ambient
row erasure, without a second typed-stack recursion. -/
theorem policy_map (root : ProgramSource) (world : Typed.World)
    {before after : ParamDecl → EffTy → Prop}
    (maps : ∀ parameter type, before parameter type → after parameter type)
    (stack : List (List ArgSite)) : ∀ declarations,
    certificates root world before stack declarations →
      certificates root world after stack declarations := by
  induction stack with
  | nil => intro declarations typed; exact typed
  | cons sites stack ih =>
    intro declarations typed index parameter found
    obtain ⟨site, program, environment, type, here, node, checked, admitted, values, rest⟩ :=
      typed index parameter found
    exact ⟨site, program, environment, type, here, node, checked,
      maps parameter type admitted, values, ih _ rest⟩

/-- Placement: the ambient policy retains the actual passed-program requirement. Consumer:
parameter execution after the checkEffs birth producer establishes this annotation. -/
def ambientPolicy (available : Env.Requirement) (parameter : ParamDecl) (type : EffTy) : Prop :=
  parameter.admits type = true ∧ Row.Subset type.requires available

/-- Placement: the stronger ambient input erases to the unchanged unit stack predicate.
Consumer: existing value, view and higher-order type-only producers. -/
theorem ambient_erases (root : ProgramSource) (world : Typed.World) (available : Env.Requirement)
    {stack : List (List ArgSite)} {declarations : List ParamDecl}
    (typed : certificates root world (ambientPolicy available) stack declarations) :
    StackTyped root world declarations stack :=
  (unit_agreement root world stack declarations).mp
    (policy_map root world (fun _ _ admitted => admitted.1) stack declarations typed)

/-- Placement: ambient row widening follows the same certificate fold. Consumer: provider
installed-map extension before execution of a captured parameter. -/
theorem ambient_widen (root : ProgramSource) (world : Typed.World)
    {available later : Env.Requirement} (bound : Row.Subset available later)
    {stack : List (List ArgSite)} {declarations : List ParamDecl}
    (typed : certificates root world (ambientPolicy available) stack declarations) :
    certificates root world (ambientPolicy later) stack declarations :=
  policy_map root world (fun _ _ admitted => ⟨admitted.1, Row.subset_trans admitted.2 bound⟩)
    stack declarations typed

/-- Placement: empty parameter scope carries any stack, as in stackTyped_nil. Consumer:
closed source entry, where no passed program has entered. -/
theorem empty_scope (root : ProgramSource) (world : Typed.World) (policy : ParamDecl → EffTy → Prop)
    (stack : List (List ArgSite)) : certificates root world policy stack [] := by
  cases stack with
  | nil => rfl
  | cons sites rest =>
    intro index parameter absent
    rw [List.getElem?_nil] at absent
    exact nomatch absent

/-- Placement: the ambient point input refines the existing PointTyped relation with the
same stack fold. This candidate retains the PointTyped definition literally unchanged. -/
def pointCertificate (root : ProgramSource) (world : Typed.World)
    (policy : ParamDecl → EffTy → Prop) (point : Point) (type : EffTy) : Prop :=
  PointTyped root world point type ∧
    certificates root world policy point.params (scopeParams root.program point.path)

/-- Placement: the unit refinement adds no premise to the existing public point relation.
Consumer: unchanged higher-order source callers and the ambient M5 input adapter. -/
theorem point_unit_agreement (root : ProgramSource) (world : Typed.World) (point : Point) (type : EffTy) :
    pointCertificate root world (fun parameter type => parameter.admits type = true) point type ↔
      PointTyped root world point type := by
  constructor
  · intro typed
    exact typed.1
  · intro typed
    obtain ⟨program, environment, node, checked, values, completed, stack⟩ := typed
    exact ⟨⟨program, environment, node, checked, values, completed, stack⟩,
      (unit_agreement root world _ _).mpr stack⟩

end Test.StackCertificateFoldCandidate
