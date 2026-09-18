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

/-! ## A red control for every reason (scout F, 2026-09-17)

Ten of the twenty-four reasons had no test that produces them; three belong to `select` and
`iterate`, and `initialNotCursor` to DI-91's stated annotation. One program each, the smallest
that reaches the rule. -/

private def unitP : Api.Program := .succeed (.lit .unit)

#guard Api.explain (.select (.lit (.nat 1)) .option unitP unitP)
  = some ⟨[], .notSelectable .option .nat⟩
#guard Api.explain (.iterate none (.lit (.nat 0)) (.lit (.bool false)) (.lit (.bool true))
    (.lit .unit) unitP) = some ⟨[], .stepNotCursor .bool .nat⟩
#guard Api.explain (.iterate (some .string) (.lit (.nat 0)) (.lit (.bool false)) (.var 0)
    (.lit .unit) unitP) = some ⟨[], .initialNotCursor .nat .string⟩
#guard Api.explain (.bind (.withFiber .snapshotChildren)
    (.withFiber (.interruptAll (.var 0) (some (.lit (.bool true))))))
  = some ⟨[1, 0], .natExpected .bool⟩
#guard Api.explain (.withFiber (.setContext (.lit (.nat 1)))) = some ⟨[0], .contextExpected .nat⟩
#guard Api.explain (.withFiber (.awaitNewChildren (.lit (.nat 1))))
  = some ⟨[0], .snapshotExpected .nat⟩
#guard Api.explain (.service ⟨⟨99⟩, ⟨99⟩⟩) = some ⟨[], .serviceUnknown ⟨⟨99⟩, ⟨99⟩⟩⟩
#guard Api.explain (.provideLayer (.succeed ⟨⟨4⟩, ⟨4⟩⟩ (.str "x")) false unitP)
  = some ⟨[0], .literalOutsideAlphabet (.str "x")⟩
#guard (Api.explain (.perform (.external 3) (.lit .unit))).map (·.reason.head)
  = some "outsideDomain"
-- A reference that reaches the walker is `layerReference`. Through `Api.explain` an ill-formed
-- one is caught at the root first, and a well-formed one is expanded away, so the walker's own
-- arm is reached only on the unexpanded tree (`Program.explain`, the check's refusal).
#guard Api.explain (.provideLayer (.ref [0]) false unitP) = some ⟨[], .referencesIllFormed⟩
#guard Effect4.Program.explain (nativeSignature []) [] (.provideLayer (.ref [0]) false unitP)
  = some ⟨[0], .layerReference [0]⟩

end Test.Program.BlameContract
