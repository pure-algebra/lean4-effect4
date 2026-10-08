import Effect4.Modules.Step
import Aesop

/-!
# Structural interpretation requirements

These helpers serve step-language-sound and step-language-typed, requirements R10 and R4.
The reading and typing proofs split one conjunction at each node.
The public feature-based premises convert once at the boundary.
Scope alignment changes under a fold; the identity capability remains the same.
These propositions establish no evaluation, typing, allocation, or host behavior alone.
-/

set_option autoImplicit false
namespace Effect4.Modules.Step
open Effect4.Program Effect4.Program.Authoring Effect4.Schema

mutual
/-- Structural premises transfer along implications of the two primitive obligations. -/
theorem requirements_mono {P Q R S : Prop} (scope : P → R) (identity : Q → S) :
    ∀ {Γ : List Ty} {t : Ty} (e : Step Γ t), e.Requirements P Q → e.Requirements R S
  | _, _, .var _, _ => trivial
  | _, _, .bool _, _ => trivial
  | _, _, .nat _, _ => trivial
  | _, _, .unit, _ => trivial
  | _, _, .nil, _ => trivial
  | _, _, .none, _ => trivial
  | _, _, .not a, h => requirements_mono scope identity a h
  | _, _, .isZero a, h => requirements_mono scope identity a h
  | _, _, .fst a, h => requirements_mono scope identity a h
  | _, _, .snd a, h => requirements_mono scope identity a h
  | _, _, .some a, h => requirements_mono scope identity a h
  | _, _, .get a _, h => requirements_mono scope identity a h
  | _, _, .emptyLike a, h => requirements_mono scope identity a h
  | _, _, .len a, h => requirements_mono scope identity a h
  | _, _, .head a, h => requirements_mono scope identity a h
  | _, _, .and a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .or a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .add a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .sub a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .lt a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .eq a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .pair a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .tuple2 a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .set a _ b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .snoc a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .append a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .take a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .drop a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .cons a b, h => ⟨requirements_mono scope identity a h.1, requirements_mono scope identity b h.2⟩
  | _, _, .ite a b c, h => ⟨requirements_mono scope identity a h.1,
    requirements_mono scope identity b h.2.1, requirements_mono scope identity c h.2.2⟩
  | _, _, .tuple3 a b c, h => ⟨requirements_mono scope identity a h.1,
    requirements_mono scope identity b h.2.1, requirements_mono scope identity c h.2.2⟩
  | _, _, .fold xs init body, h => ⟨scope h.1, requirements_mono scope identity xs h.2.1,
    requirements_mono scope identity init h.2.2.1, requirements_mono scope identity body h.2.2.2⟩
  | _, _, .record fields, h => requirements_fields_mono scope identity fields h
  | _, _, .sameDeferred a b, h => ⟨identity h.1,
    requirements_mono scope identity a h.2.1, requirements_mono scope identity b h.2.2⟩

/-- The required-field half of structural premise transfer. -/
theorem requirements_fields_mono {P Q R S : Prop} (scope : P → R) (identity : Q → S) :
    ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs),
    FieldResults.All (fun {_} value => value) fs (cataFields (requirementsAlg P Q) fields) →
    FieldResults.All (fun {_} value => value) fs (cataFields (requirementsAlg R S) fields)
  | _, _, .nil, _ => trivial
  | _, _, .cons _ value rest, h => ⟨requirements_mono scope identity value h.1,
    requirements_fields_mono scope identity rest h.2⟩
end

mutual
/-- The structural conjunction requires precisely the features that occur in the step. -/
theorem requirements_features {P Q : Prop} : ∀ {Γ : List Ty} {t : Ty} (e : Step Γ t),
    e.Requirements P Q ↔ ((e.binds = true → P) ∧ (e.compares = true → Q))
  | _, _, .var _ => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .bool _ => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .nat _ => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .unit => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .nil => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .none => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .not a => requirements_features a
  | _, _, .isZero a => requirements_features a
  | _, _, .fst a => requirements_features a
  | _, _, .snd a => requirements_features a
  | _, _, .some a => requirements_features a
  | _, _, .get a _ => requirements_features a
  | _, _, .emptyLike a => requirements_features a
  | _, _, .len a => requirements_features a
  | _, _, .head a => requirements_features a
  | _, _, .and a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .or a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .add a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .sub a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .lt a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .eq a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .pair a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .tuple2 a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .set a _ b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .snoc a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .append a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .take a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .drop a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .cons a b => by
    change (a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ ((a.compares || b.compares) = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .ite a b c => by
    change (a.Requirements P Q ∧ b.Requirements P Q ∧ c.Requirements P Q) ↔
      ((((a.binds || b.binds) || c.binds) = true → P) ∧ (((a.compares || b.compares) || c.compares) = true → Q))
    rw [requirements_features a, requirements_features b, requirements_features c]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .tuple3 a b c => by
    change (a.Requirements P Q ∧ b.Requirements P Q ∧ c.Requirements P Q) ↔
      (((a.binds || (b.binds || c.binds)) = true → P) ∧ ((a.compares || (b.compares || c.compares)) = true → Q))
    rw [requirements_features a, requirements_features b, requirements_features c]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .fold xs init body => by
    change (P ∧ xs.Requirements P Q ∧ init.Requirements P Q ∧ body.Requirements P Q) ↔
      ((true = true → P) ∧ ((xs.compares || init.compares || body.compares) = true → Q))
    rw [requirements_features xs, requirements_features init, requirements_features body]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .sameDeferred a b => by
    change (Q ∧ a.Requirements P Q ∧ b.Requirements P Q) ↔
      (((a.binds || b.binds) = true → P) ∧ (true = true → Q))
    rw [requirements_features a, requirements_features b]
    simp only [Bool.or_eq_true]
    aesop
  | _, _, .record fields => requirements_fields_features fields

/-- The required-field half of feature completeness for structural premises. -/
theorem requirements_fields_features {P Q : Prop} :
    ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs),
    FieldResults.All (fun {_} value => value) fs (cataFields (requirementsAlg P Q) fields) ↔
      (((Step.record fields).binds = true → P) ∧ ((Step.record fields).compares = true → Q))
  | _, _, .nil => ⟨fun _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩, fun _ => trivial⟩
  | _, _, .cons _ value rest => by
    change (value.Requirements P Q ∧ FieldResults.All (fun {_} x => x) _
      (cataFields (requirementsAlg P Q) rest)) ↔
      (((value.binds || (Step.record rest).binds) = true → P) ∧
        ((value.compares || (Step.record rest).compares) = true → Q))
    rw [requirements_features value, requirements_fields_features rest]
    simp only [Bool.or_eq_true]
    aesop
end

/-- Convert the two public feature premises once, at the reading boundary. -/
theorem requirements_of_facts {Γ : List Ty} {t : Ty} {L : Model.Leaves}
    (e : Step Γ t) {env : Env} {length : Nat} (scope : e.ScopeFacts env length)
    (identity : e.IdentityFacts L) :
    e.Requirements (length = env.names.length) (Nonempty (DeferredIdentity L)) := by
  apply (requirements_features e).mpr
  constructor
  · intro occurs
    unfold ScopeFacts at scope
    rw [occurs] at scope
    exact scope
  · intro occurs
    unfold IdentityFacts at identity
    rw [occurs] at identity
    exact identity

/-- Typing needs the scope premise but no interpretation capability. -/
theorem requirements_of_scope {Γ : List Ty} {t : Ty} (e : Step Γ t)
    {env : Env} {length : Nat} (scope : e.ScopeFacts env length) :
    e.Requirements (length = env.names.length) True := by
  apply (requirements_features e).mpr
  constructor
  · intro occurs
    unfold ScopeFacts at scope
    rw [occurs] at scope
    exact scope
  · intro _
    trivial

end Effect4.Modules.Step
