import Effect4.Codegen.Schema

/-!
Generate the TypeScript differential fixture from Lean-owned representations.

The expected Boolean is evaluated by `Representation.fieldAdmissible`; the
rendered value is emitted by the production Schema target.  TypeScript then
compares that result with Effect's pinned `SchemaRepresentation.fromJson`
decoder, so neither the witness nor the expected answer is duplicated by hand.
-/

namespace Effect4Harness.SchemaAnnotations

open Effect4

private structure AdmissionCase where
  name : String
  representation : Representation

private def cases : List AdmissionCase :=
  [ { name := "E4-SCHEMA-CE-033"
      representation :=
        .objects none
          [ .filter
              ⟨"effect/test", .null, some [.reference ⟨""⟩]⟩
              none false ]
          [] [] }
  , { name := "nonempty-string-control"
      representation := .string none [] } ]

private def boolSource (value : Bool) : String :=
  if value then "true" else "false"

private def caseSource (test : AdmissionCase) : String :=
  "  {\n" ++
  "    name: \"" ++ test.name ++ "\",\n" ++
  "    representation: " ++
    Effect4.Codegen.Schema.representationSource test.representation ++ ",\n" ++
  "    leanFieldAdmissible: " ++
    boolSource test.representation.fieldAdmissible ++ "\n" ++
  "  }"

private def fixture : String :=
  "import { Schema, SchemaRepresentation } from \"effect\"\n\n" ++
  "const effectFieldAdmissible = (representation: Schema.Json): boolean => {\n" ++
  "  try {\n" ++
  "    SchemaRepresentation.fromJson({ representation, references: {} })\n" ++
  "    return true\n" ++
  "  } catch {\n" ++
  "    return false\n" ++
  "  }\n" ++
  "}\n\n" ++
  "const cases: ReadonlyArray<{\n" ++
  "  readonly name: string\n" ++
  "  readonly representation: Schema.Json\n" ++
  "  readonly leanFieldAdmissible: boolean\n" ++
  "}> = [\n" ++
  String.intercalate ",\n" (cases.map caseSource) ++ "\n]\n\n" ++
  "for (const test of cases) {\n" ++
  "  const effectResult = effectFieldAdmissible(test.representation)\n" ++
  "  if (effectResult !== test.leanFieldAdmissible) {\n" ++
  "    throw new Error(`${test.name}: Lean=${test.leanFieldAdmissible} Effect=${effectResult}`)\n" ++
  "  }\n" ++
  "}\n\n" ++
  "console.log(\"schema field admission: generated Lean results agree with Effect\")\n"

#eval IO.print fixture

end Effect4Harness.SchemaAnnotations
