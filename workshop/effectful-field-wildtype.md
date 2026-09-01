# Effectful-field forward fixture

## Decision

The first API should be higher-order combinators over existing carriers, not a
new optic hierarchy:

```text
pure focus      Effect4.Lens S A
field marker    AnnotationKey Json on PropertySignatureOf.annotations
service         ServiceKey
operations      OperationId
semantic proof  Program signature
generated flow  checked RawFlow
```

`getM`, `replaceM`, and `modifyM` are composition functions. The compiled Lean
probe in `workshop/EffectfulFieldWildtype.lean` shows that the pure case reduces
definitionally to `Lens.modify` and that duplicate annotation entries remain
observable. It does not propose a serializable `Program`: generation must use
the existing first-order operation identities and checked flow.

The marker belongs on `Schema.annotateKey`, because rc.112 lowers key-level
annotations into `PropertySignature.annotations`. A node-level `annotate`
marker would apply to every reuse of that field schema and is not a field
selection.

## Highest-value wild fixtures

Use this corpus first; it covers the shape without dragging in unrelated
Schema breadth.

| Fixture | Evidence | Why it earns a seat |
| --- | --- | --- |
| Annotated struct field | `/Users/pooks/Dev/foldlab/corpus/kitlangton_motel/src/domain.ts:19` | Real `Schema.annotateKey` on a property; proves field-local metadata is normal user code. |
| Service-dependent one-way field transform | `/Users/pooks/Dev/foldlab/corpus/tim-smart_lalph/repos/effect/packages/platform-browser/test/IndexedDbQueryBuilder.test.ts:58` | `VerifyId` requires `VerifyContext` only on encoding; proves read/write service rows must remain directional. |
| Typed transformation failure | `/Users/pooks/Dev/foldlab/corpus/anomalyco_opencode/packages/core/test/session-runner-tool-registry.test.ts:315` | A field encoder fails with `SchemaIssue.InvalidValue`; proves generated field effects need an error channel. |
| Generic annotation persistence | `/Users/pooks/Dev/lean4-effect4/harness/schema-annotations/effect-annotations.ts` | Existing rc.112 harness already proves JSON-valued custom annotations survive `toRepresentation` / `toJson`. |
| Pure optic baseline | `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/Optic.ts:139` | rc.112 `Lens` is pure. Effectful access should wrap it, not fork it. |

The exact rc.112 source confirms the boundary:

- `Schema.Codec<T,E,RD,RE>` keeps decoding and encoding services separate in
  `/Users/pooks/Dev/foldlab/.staging/e2/src-cache/Schema.ts:1019`.
- `decodeEffect` returns `Effect<T, SchemaError, DecodingServices>` at
  `/Users/pooks/Dev/foldlab/.staging/e2/src-cache/Schema.ts:1558`.
- `encodeEffect` returns `Effect<E, SchemaError, EncodingServices>` at
  `/Users/pooks/Dev/foldlab/.staging/e2/src-cache/Schema.ts:2019`.
- rc.112 deliberately restricts `Schema.Optic` to `never` services and warns
  that `Schema.toIso` can throw for service-dependent transformations at
  `/Users/pooks/Dev/foldlab/.staging/e2/src-cache/Schema.ts:1128` and `:16121`.
- persisted generic annotations keep only JSON values in
  `/Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts:919`.

## Representative annotation and expected generated TypeScript

The first positive fixture is one `User.email` property annotated with a JSON
payload like this:

```ts
interface FieldEffectAnnotation {
  readonly version: 1
  readonly service: "UserFieldPolicy"
  readonly read: "readEmail"
  readonly write: "writeEmail"
}

declare module "effect/Schema" {
  namespace Annotations {
    interface Annotations {
      readonly "effect4/field-effect"?: FieldEffectAnnotation | undefined
    }
  }
}

const User = Schema.Struct({
  id: Schema.String,
  email: Schema.String.pipe(Schema.annotateKey({
    "effect4/field-effect": {
      version: 1,
      service: "UserFieldPolicy",
      read: "readEmail",
      write: "writeEmail"
    }
  }))
})
type User = typeof User.Type
```

Expected generated API, with no generated `EffectfulField` carrier:

```ts
import { Context, Effect, Optic } from "effect"

type ReadEmailError = { readonly _tag: "ReadEmailError" }
type WriteEmailError = { readonly _tag: "WriteEmailError" }

class UserFieldPolicy extends Context.Service<UserFieldPolicy, {
  readonly readEmail: (source: User) => Effect.Effect<string, ReadEmailError>
  readonly writeEmail: (source: User, value: string) => Effect.Effect<void, WriteEmailError>
}>()("UserFieldPolicy") {}

const emailLens = Optic.id<User>().key("email")

export const email = {
  get: (source: User): Effect.Effect<string, ReadEmailError, UserFieldPolicy> =>
    Effect.gen(function*() {
      const service = yield* UserFieldPolicy
      return yield* service.readEmail(source)
    }),

  replace: (value: string, source: User): Effect.Effect<User, WriteEmailError, UserFieldPolicy> =>
    Effect.gen(function*() {
      const service = yield* UserFieldPolicy
      yield* service.writeEmail(source, value)
      return emailLens.replace(value, source)
    }),

  modify: (f: (value: string) => string, source: User):
    Effect.Effect<User, ReadEmailError | WriteEmailError, UserFieldPolicy> =>
      Effect.flatMap(email.get(source), (value) => email.replace(f(value), source))
}
```

Exact type assertions for the positive fixture:

```ts
type GetSuccess = Effect.Success<ReturnType<typeof email.get>>       // string
type GetError = Effect.Error<ReturnType<typeof email.get>>           // ReadEmailError
type GetServices = Effect.Services<ReturnType<typeof email.get>>     // UserFieldPolicy
type PutSuccess = Effect.Success<ReturnType<typeof email.replace>>   // User
type PutError = Effect.Error<ReturnType<typeof email.replace>>       // WriteEmailError
type PutServices = Effect.Services<ReturnType<typeof email.replace>> // UserFieldPolicy
type ModifyError = Effect.Error<ReturnType<typeof email.modify>>     // ReadEmailError | WriteEmailError
```

At rc.112 the extractor is named `Effect.Services`, not
`Effect.Requirements`. Generating the latter is a version error.

## Admission/refusal battery

Keep these cases separate from TypeScript diagnostics; malformed metadata is a
Lean generation refusal, not an Effect failure.

1. Accept exactly one JSON marker on one unique string property.
2. Refuse two raw entries named `effect4/field-effect`, even if both decode.
3. Refuse one valid plus one malformed same-name entry. Checking only
   `AnnotationKey.getAll` is insufficient because it omits malformed payloads;
   first require raw `Annotations.payloadsAt(...).length = 1`.
4. Refuse missing/unknown `version`, service identity, read operation, or write
   operation; refuse an operation not in the selected closed alphabet.
5. Refuse a node-level marker when a property-level marker is required.
6. Refuse duplicate generated field names and duplicate raw property keys.
7. Refuse non-string property keys in the first profile; numeric/global-symbol
   paths need their own target spelling before admission.
8. Accept read-only and write-only markers, but emit only the declared leg and
   its directional error/service type. Do not synthesize a missing operation.

## Direct TypeScript and effect-tsgo gate

Use exact installed bytes at
`/Users/pooks/Dev/foldlab/library/effects/node_modules`: Effect
`4.0.0-rc.112`, TypeScript `7.0.2`, and `@effect/tsgo` `0.38.0`.

Each generated fixture gets its own one-file project. Run the unpatched
TypeScript compiler first, then:

```sh
/Users/pooks/Dev/foldlab/library/effects/node_modules/.bin/effect-tsgo \
  diagnostics --project tsconfig.json --format json --strict --list-files
```

Require one checked file, `detectedEffect = supportedEffect = "v4"`, and exact
diagnostic-name sets:

| Fixture | Mutation | Expected name |
| --- | --- | --- |
| positive | use and export all three field effects | none |
| floating | call `email.replace(...)` and discard it | `floatingEffect` |
| missing-error | ascribe `Effect.Effect<User, never, UserFieldPolicy>` to `email.replace(...)` (suppress ordinary TS error as in the existing Foldlab probe) | `missingEffectError` |
| missing-context | ascribe `Effect.Effect<User, WriteEmailError>` to `email.replace(...)` (suppress ordinary TS error) | `missingEffectContext` |
| sync escape | call `Schema.encodeSync` for a service-dependent field inside `Effect.gen` | direct TypeScript rejection and, where emitted by 0.38.0, `schemaSyncInEffect`; do not make this version-sensitive diagnostic the only gate |

The reusable diagnostic runner and exact JSON decoder already exist at
`/Users/pooks/Dev/foldlab/.staging/effect-core-v1/workshop/tsgo/run-probes.ts`.
Extend its project table rather than inventing a second diagnostic parser.

