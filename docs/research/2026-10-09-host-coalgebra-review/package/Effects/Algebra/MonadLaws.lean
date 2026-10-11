/-!
# Minimal monad equation bundles

These propositions let sharp theorems require only the equations their proofs
consume. The ordinary public theorems continue to accept `LawfulMonad`.
-/

/-
`autoImplicit` and `relaxedAutoImplicit` are off for the `Effects` library
(`lakefile.toml`) and are restored here, for these nine modules only.

`generated/algebra-parity.tsv` is a byte-identical receipt of every constant
these modules compile, compared against the lean4-effect4 commit they were
moved from — universe *parameter names* and full `pp.all` types included.
Binding `S`, `A` and their universes explicitly renames `u_1`/`u_2` and can
reorder a declaration's implicit binders, which breaks that receipt against a
commit that cannot be regenerated. The frozen v0.1.0 surface is worth more
here than the hygiene, and the parity gate is what enforces the trade:
`./scripts/check-algebra-parity.sh` fails the moment one of these files
changes shape. Every module outside `Effects/Algebra/` is bound explicitly.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Effects

/-- Left-unit equation for a monad. -/
abbrev LeftUnit (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A B : Type u} (value : A) (next : A → M B),
    (pure value : M A) >>= next = next value

/-- Right-unit equation for a monad. -/
abbrev RightUnit (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A : Type u} (value : M A),
    value >>= (fun result => (pure result : M A)) = value

/-- Associativity equation for a monad. -/
abbrev BindAssoc (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A B C : Type u} (value : M A) (next : A → M B) (last : B → M C),
    (value >>= next) >>= last = value >>= fun result => next result >>= last

theorem leftUnit_of_lawful {M : Type u → Type v}
    [Monad M] [LawfulMonad M] : LeftUnit M :=
  fun value next => pure_bind value next

theorem rightUnit_of_lawful {M : Type u → Type v}
    [Monad M] [LawfulMonad M] : RightUnit M :=
  fun value => bind_pure value

theorem bindAssoc_of_lawful {M : Type u → Type v}
    [Monad M] [LawfulMonad M] : BindAssoc M :=
  fun value next last => bind_assoc value next last

end Effects
