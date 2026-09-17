import Effect4.Api
import Effect4.Program.Authoring.Sugar
import Effect4.Codegen.Diagnostics

/-!
# Blame contract — the refusal is located and named (DI-86)

`Api.explain` (`src/Effect4/Api.lean`) projects the one checker: the path of the deepest node
whose own rule refuses, and that rule's reason (`TypeReason`, `Program/Typing/Blame.lean`).
The pins walk a refusal down through `bind`, `suspend`, `catchCause`, `select` and a generator
body, and the law `Api.explain_none_iff` is what makes the projection the checker's rather
than a second checker. `Api.check` and `Api.author` (DI-85) answer the certificate or that
refusal: a refused program never comes back without a reason.
-/

set_option autoImplicit false

namespace Test.Program.BlameContract

open Effect4 Effect4.Program Effect4.Api Effect4.Program.Authoring

/-- The root fails at a type the error alphabet does not admit. -/
def refused : Api.Program := .fail (.lit (.bool true))

#guard Api.wellTyped refused = false
#guard Api.explain refused = some ⟨[], .errorNotAdmitted .bool⟩
#guard Api.blame refused = some []

/-! ## The path follows the checker's environment -/

#guard Api.blame (.bind (.succeed (.lit (.nat 1))) refused) = some [1]
#guard Api.blame (.catchCause (.suspend refused) (.succeed (.lit .unit))) = some [0, 0]
#guard Api.blame (.catchCause (.succeed (.lit .unit)) refused) = some [1]
#guard Api.blame (.select (.lit (.bool true)) .bool (.succeed (.lit .unit)) refused) = some [1]
#guard Api.blame (.onExit (.succeed (.lit .unit)) (.bind refused (.succeed (.lit .unit)))) = some [1, 0]

/-! ## The reason is the node's own rule -/

#guard Api.explain (.succeed (.var 0)) = some ⟨[], .term (.var 0)⟩
#guard Api.explain (.select (.lit (.nat 1)) .bool (.succeed (.lit .unit)) (.succeed (.lit .unit)))
  = some ⟨[], .predicateNotBool .nat⟩
#guard match Api.explain (.perform .refGet (.lit (.nat 1))) with
  | some ⟨[], .requestNotSubtype _ _ _⟩ => true
  | _ => false
#guard Api.explain (.gen (.cons (.ret (.lit .unit)) (.cons (.bindYield (.succeed (.lit .unit))) .nil)))
  = some ⟨[0, 0], .returnNotLast⟩
#guard Api.explain (.gen (.cons .breakLoop .nil)) = some ⟨[0, 0], .breakOutsideLoop⟩
#guard Api.explain (.provideLayer (.mergeAll .nil) false (.succeed (.lit .unit)))
  = some ⟨[0, 0], .mergeAllEmpty⟩
-- A reference with no preceding target is refused at the root, before typing.
#guard Api.explain (.provideLayer (.ref [0]) false (.succeed (.lit .unit)))
  = some ⟨[], .referencesIllFormed⟩

/-! ## A typed program has no refusal -/

def typed : Api.Program := .bind (.perform .refMake (.lit (.nat 1))) (.perform .refGet (.var 0))

#guard Api.wellTyped typed
#guard Api.explain typed = none
#guard Api.blame typed = none

/-! ## Certificate first: `check` and `author` -/

#guard (Api.check typed).toOption.map (·.ty.answer) = some .nat
#guard (Api.check typed).toOption.map (fun t => (t.run).exit) = some (some (.success (.nat 1)))
#guard (Api.check typed).toOption.map (·.runSync) = some (.success (.nat 1))
-- A certificate has no decidable equality; a refusal is compared as data.
def refusalOf {table : RowTable} : Except TypeRefusal (Api.Typed table) → Option TypeRefusal
  | .error r => some r
  | .ok _ => none

def authorRefusalOf {table : RowTable} : Except Api.AuthorRefusal (Api.Typed table) → Option Api.AuthorRefusal
  | .error r => some r
  | .ok _ => none

#guard refusalOf (Api.check refused) = some ⟨[], .errorNotAdmitted .bool⟩
#guard refusalOf (Api.check (.bind (.succeed (.lit (.nat 1))) refused)) = some ⟨[1], .errorNotAdmitted .bool⟩

-- One call from a named source: a scope refusal names the unbound name at its path, a typing
-- refusal is the checker's, and a typed source runs.
#guard (Api.author (bind "r" (Ref.make (nat 1)) (Ref.get (var "r")))).toOption.map (·.runSync)
  = some (.success (.nat 1))
#guard authorRefusalOf (Api.author (Ref.get (var "r"))) = some (.scope ⟨[], .unbound "r"⟩)
#guard authorRefusalOf (Api.author (bind "r" (Ref.make (nat 1)) (Authoring.fail (bool true))))
  = some (.typing ⟨[1], .errorNotAdmitted .bool⟩)

/-! ## The host's codes for a reason (Codegen/Diagnostics.lean) -/

#guard TypeReason.head (.errorNotAdmitted .bool) = "errorNotAdmitted"
#guard Effect4.Codegen.codesOf .pinned (.term (.var 0)) = [2304]
#guard Effect4.Codegen.codesOf .pinned (.errorNotAdmitted .bool) = []
#guard Effect4.Codegen.codesOf .pinned .breakOutsideLoop = [1107]
#guard (Effect4.Codegen.codesOf { exactOptionalPropertyTypes := false } (.valueNotSubtype ⟨⟨0⟩, ⟨0⟩⟩ .nat .string)).contains 2375 = false
#guard (Effect4.Codegen.HostConfig.pinned.tsconfig ["programs"]).startsWith "{\n  \"compilerOptions\": {"

#print axioms Effect4.Api.explain_none_iff
#print axioms Effect4.Api.check
#print axioms Effect4.Api.author
#print axioms Effect4.Program.explain_none_iff

end Test.Program.BlameContract
