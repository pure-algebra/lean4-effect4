# Repaired annotation allowlist: bounded static review

**Verdict: accept the new policy for the report's stated structural observation.** No remaining concrete annotation counterexample or accepted-position validation bypass was found. This is static source review, not a general preservation proof or a new execution receipt.

Production source pinned to `c007d0eff6b0e6961c0097c61afda88f12aa9dc3`; all vendor line references below are at that commit under `vendor/effect-4.0.0-rc.112/src/`. No compiler, runtime, installation, UI, repository edit, or other-agent interaction was used.

- Probe: `/private/tmp/gemini-effect-schema-scout-2026-10-01/DefinitiveSchemaProbe.lean`, SHA-256 `8ec101489fdbb8bb763e37bcad812cc8ce1ca96278bb2daad41250ea41c3f4e8`.
- Report: `/Users/pooks/.codex/attachments/da455883-f2f0-4132-8801-abb8f6829006/Pasted text.txt`, SHA-256 `4ce95d559dc8263ef4e41743a386a26c3d5ad5136b5100cdab50b4b9b3953784`.

## The eight allowed keys

The report now observes structural TypeScript types, validation acceptance/refusal and decoded value structure, and explicitly excludes diagnostic metadata and nominal brands (`report:19–22`). Under that boundary:

| Keys | Pinned consumers and consequence |
| --- | --- |
| `identifier` | Documented as a tooling/reference identifier and diagnostic expected label (`Schema.ts:17091–17105`); used to select reference names in `internal/schema/toRepresentation.ts:115–118`, and diagnostic labels in `internal/schema/annotations.ts:57–60`. Erasure loses naming/reference presentation, outside the new observation; no validation or decoded-value effect found for the admitted direct structural schemas. |
| `title`, `description`, `documentation` | Declared as annotation metadata (`Schema.ts:17008–17030`). Title/description project into JSON Schema documentation (`internal/schema/toJsonSchemaDocument.ts:25–37`). No acceptance, decoded-value or structural-type consumer of `documentation` was found in the narrowly inspected parser/AST/reconstruction route. |
| `examples`, `default` | Explicitly documentation fields (`Schema.ts:17039–17047`), projected into JSON Schema annotations (`toJsonSchemaDocument.ts:39–42`). **`default` metadata is not a runtime default:** constructor defaults are a separate transformation/link stored in `Context.constructorDefault` (`SchemaAST.ts:3634–3645`), while declaration constructor hooks use the different `~constructor` annotation and a function (`:4177–4180`). Both are outside this permitted bag/profile. |
| `message`, `expected` | Used to format failures (`Schema.ts:17016–17027`, `:17075–17086`; `SchemaIssue.ts:912–920`, `:1045–1052`, `:1098–1106`). They change diagnostic text, which the observation excludes; no acceptance or decoded-value effect found. |

The annotation methods retain the schema's rebuild/type interface (`Schema.ts:189–192`); their implementation rebuilds with annotation metadata (`internal/schema/schema.ts:54–58`). No allowed key is `brands`, `parseOptions`, a reviver hook, or a transformation hook. The previous semantic cases are therefore excluded by key, rather than merely declared harmless.

This conclusion is deliberately limited: losing identifiers, descriptions, default/example documentation or messages is still a real change for tools and diagnostics. The report no longer claims to preserve those observations. The key validator also does not validate metadata payload shapes; that does not create a demonstrated structural-validation gap, but it is not a general well-formed-annotations checker.

## All successful-emission positions are checked

`validateAnnotations` scans every bag entry and accepts only the eight exact keys (`probe:36–52`). A mixed bag is not accepted after encountering an allowed prefix; it continues through the remainder.

- Every accepted node arm checks its own annotations: primitives and numbers (`:135–196`), object keyword (`:200–203`), arrays/tuples (`:210–224`), objects (`:226–231`), and unions (`:232–237`).
- An accepted object property validates its separate key annotations (`:106`) and then consumes its child schema result (`:107`); that child's node annotations are therefore checked independently. The property loop processes the full list (`:95–118`).
- Each tuple element validates its own annotation bag (`:215`) and consumes its recursively generated type (`:216`). Array rest schemas are also consumed (`:213`).
- Admitted numeric filters validate annotations before recognizing the check (`:63–89`, specifically `:68`), and the number arm consumes every check result (`:165–166`).
- Accepted union members are all consumed (`:236`), so their nested annotation refusals propagate.
- Filter groups are always refused (`:240–241`); references have no annotation field and are refused (`:130–131`). Unsupported declaration/suspension/enum/template/symbol forms and nonempty index signatures do not produce successful output. They cannot bypass validation into the admitted profile merely because their rejected children are not all diagnosed.

The known `parseOptions` channel is refused at node, filter, property and element bags. Placing an object containing a property named `parseOptions` inside an allowed *documentation value* is not the same channel: the pinned runtime looks up the annotation bag's top-level `parseOptions` key (`SchemaParser.ts:1096–1102`, `:1163–1166`), not arbitrary nested metadata payloads.

## Readiness limitation

On this new policy alone, there is no reason to block the narrow readable-profile brief. Keep the observation exclusions and rc.112 pin explicit, and keep future metadata consumers or an Effect version change outside this static verdict. The coordinator's rerun owns the guard/axiom/runtime results; this review does not upgrade finite controls into a general compiler or host preservation theorem.
