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
-- A reference with no preceding target is refused at its site, before typing, with its fault.
#guard Api.explain (.provideLayer (.ref [0]) false (.succeed (.lit .unit)))
  = some ⟨[0], .referenceIllFormed [0] .notBefore⟩

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
-- one is caught at its site first, and a well-formed one is expanded away, so the walker's own
-- arm is reached only on the unexpanded tree (`Program.explain`, the check's refusal).
#guard Api.explain (.provideLayer (.ref [0]) false unitP)
  = some ⟨[0], .referenceIllFormed [0] .notBefore⟩
#guard Effect4.Program.explain (nativeSignature []) [] (.provideLayer (.ref [0]) false unitP)
  = some ⟨[0], .layerReference [0]⟩

#guard Effect4.Codegen.codesOf {}
    (.instantiatedFormation "Db.get" ⟨["row", "answer"], .map .nat .string, .mapKey⟩) = []

/-! ## Error payloads, refused by name (decisions row 120)

A record failure is admitted at a required literal `_tag` with payload-admissible fields. Two
reasons name what is refused: a field no payload admits (ruling (a)), with its path through
nested records, and a class that already has another rc.112 spelling (ruling (c)). A record with
no literal tag keeps `errorNotAdmitted`. -/

/-- `fail` of a record, from authored source. -/
def failRecord (fields : List (String × Bool × Ty)) (values : List (String × TermSrc)) :
    Src NativeOp :=
  Authoring.fail (record fields values)

def withUnknown : List (String × Bool × Ty) := [("_tag", false, .lit "E"), ("cause", false, .unknown)]
def nestedUnknown : List (String × Bool × Ty) :=
  [("_tag", false, .lit "E"), ("meta", false, .record [("owner", false, .unknown)])]
def messageOnly : List (String × Bool × Ty) := [("_tag", false, .lit "E"), ("message", false, .string)]
def tagOnly : List (String × Bool × Ty) := [("_tag", false, .lit "E")]
def untagged : List (String × Bool × Ty) := [("code", false, .nat)]

-- ruling (a): `cause: unknown` is refused by name, at its path and its type
#guard authorRefusalOf (Api.author (failRecord withUnknown [("_tag", str "E"), ("cause", nat 1)])) =
  some (.typing ⟨[], .errorPayloadField (.record withUnknown) ["cause"] .unknown⟩)
-- through a nested record, the path names the inner field
#guard authorRefusalOf (Api.author (failRecord nestedUnknown
    [("_tag", str "E"), ("meta", record [("owner", false, .unknown)] [("owner", nat 1)])])) =
  some (.typing ⟨[], .errorPayloadField (.record nestedUnknown) ["meta", "owner"] .unknown⟩)
-- ruling (c): a message-only class is the pair, a no-field class the literal
#guard authorRefusalOf (Api.author (failRecord messageOnly [("_tag", str "E"), ("message", str "m")])) =
  some (.typing ⟨[], .errorSpelling (.record messageOnly) (.prod (.lit "E") .string)⟩)
#guard authorRefusalOf (Api.author (failRecord tagOnly [("_tag", str "E")])) =
  some (.typing ⟨[], .errorSpelling (.record tagOnly) (.lit "E")⟩)
-- no literal tag (ruling (b)): the error type is not admitted, as before
#guard authorRefusalOf (Api.author (failRecord untagged [("code", nat 1)])) =
  some (.typing ⟨[], .errorNotAdmitted (.record untagged)⟩)
-- green controls: a message beside another field is a payload, and the pair spelling stays
#guard (Api.author (failRecord [("_tag", false, .lit "E"), ("message", false, .string),
    ("id", false, .nat)] [("_tag", str "E"), ("message", str "m"), ("id", nat 1)])).toOption.isSome
#guard (Api.author (Authoring.fail (app "pair" [str "E", str "m"]))).toOption.isSome
#guard TypeReason.head (.errorPayloadField .unknown [] .unknown) = "errorPayloadField"
#guard TypeReason.head (.errorSpelling .unknown .unknown) = "errorSpelling"
#guard Effect4.Codegen.codesOf .pinned (.errorPayloadField .unknown [] .unknown) = []
#guard Effect4.Codegen.codesOf .pinned (.errorSpelling .unknown .unknown) = []

end Test.Program.BlameContract
