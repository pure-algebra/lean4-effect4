# effect-lift manifest v0

GENERATED — projection of `Cas.Lift.manifestV0` by `lake exe emitlift`; do not edit.

Language: `cas-libfree`

## Pins

| pin | value |
| --- | --- |
| `compilerLeg` | `typescript@5.9.2` |
| `oxcLeg` | `oxlint@1.80.0 + effect-oxlint@0.3.4 (mpsuesser/effect-oxlint @ d8c892f4)` |
| `effect` | `4.0.0-rc.112 (rule-authoring dependency; recognition is version-neutral by import resolution)` |

## The language, element by element

| element | spelling | meaning |
| --- | --- | --- |
| `program-frame` | `export const p = (store) => E.gen(function* () { … })` | A store program: an exported constant holding an Effect generator over its capabilities — in v0, exactly one, the store. Everything the program does is listed in its body, one step per line. |
| `store-binder` | `(store)` | The store capability, bound as the program's parameter. In v0 it is the only capability the grammar recognizes — a staging choice, not language law: the model composes effect signatures by sum, and multi-capability frames are the manifest's largest planned growth (the wild census's top refusal bucket). |
| `binding` | `const a = yield* store.put(node)` | One program step: perform a store operation and bind its answer to a name. Steps run top to bottom. |
| `put-op` | `store.put(node)` | Admit one node into the store. The answer is the node's content address; admitting the same node twice answers the same address. |
| `node-literal` | `{ kind, payload, refs }` | The node being admitted: what kind it is, its opaque payload bytes, and its references to nodes admitted earlier. |
| `kind-version` | `version: 0` | The kind's schema version — a canonical decimal natural that fits 32 bits. |
| `kind-tag` | `tag: 71` | The kind's wire tag — which sort of node this is — a canonical decimal natural that fits 32 bits. |
| `payload-hex` | `payload: hex("ff")` | The payload bytes, spelled in lowercase even-length hex. The program never interprets them. |
| `ref` | `{ id: a, expectedTag: 71 }` | A reference to an earlier answer by its bound name, carrying the kind tag the referenced node is expected to have. |
| `return-word` | `return [a, b]` | The program's result: exactly the bound answers, in order. This is the run's word — the observation every realization is judged by. |

## Rules

| rule | scope | enabled | meaning |
| --- | --- | --- | --- |
| `program-decl` | declaration | yes | Recognize a candidate store-program declaration (the program frame). |
| `const-yield-put` | statement | yes | Recognize one binding step: const answer = yield\* store.put(node). |
| `node-literal` | expression | yes | Recognize the closed node-literal shape of a put argument. |
| `answer-ref` | expression | yes | Resolve each ref name to the index of an earlier answer. |
| `return-word` | statement | yes | Recognize the final return as the dense, ordered answer array. |
| `hex-helper` | declaration | no | Pin the in-file hex helper (disabled in v0: lifts carry helperUnpinned instead). |
| `const-yield-load` | statement | no | Recognize a load binding (disabled: load is not yet documented). |
| `body-partition` | body | yes | Partition the generator body into binding steps and the final return. |

## Constants

- candidate depth max: 64
- nat bits: 32
- nat literal pattern: `^(0|[1-9][0-9]*)$`
- payload hex pattern: `^([0-9a-f]{2})*$`

## Refusal details (pinned)

| key | detail |
| --- | --- |
| `payloadNotHexCall` | `payload is not hex("…")` |
| `payloadNotStringLiteral` | `payload argument is not a plain string literal` |
| `payloadHexDomain` | `payload hex is not lowercase even-length` |
| `optionalChain` | `optional chain in the spine` |
| `natNotLiteral` | `{role} is not a numeric literal` |
| `natNotCanonical` | `{role} is not canonical decimal` |
| `natOutOfRange` | `{role} does not fit {bits} bits` |

## Unreachable in v0

| code | revival |
| --- | --- |
| `E-REF-FORWARD` | a two-pass binder walk (v0 resolves refs against earlier binders only) |
| `E-IMPORT-OPAQUE` | import-form rules (v0 admits every effect-module binding form alike) |
| `E-HELPER-UNPINNED` | Rule 7 landing (hex pinning is disabled; the Lift carries a boolean instead) |
