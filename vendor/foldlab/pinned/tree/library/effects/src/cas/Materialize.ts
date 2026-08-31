/**
 * The materializer door — the generative direction of a described
 * schema.
 *
 * MATERIALIZE is the estate's word for exactly this: a canonical code,
 * held in the store as content, compiled to its fully typed runtime
 * carrier. Denotation flows to code and never the reverse (the
 * direction law: HOOVER ingests, EXECUTE mints, MATERIALIZE generates).
 * A materialization has two registers, and this module is both of them:
 *
 * - the VALIDATOR register — a live decision about a candidate value,
 *   thin over `Schema.decodeUnknownEffect` and adding nothing Effect
 *   already says;
 * - the SOURCE register — rendered TypeScript, printed by Effect's own
 *   `SchemaRepresentation.toCodeDocument`, stamped with the content
 *   address of the schema node it was materialized from so parity
 *   between the served text and the stored term is a digest check
 *   (R7, the served-equals-derived wall).
 *
 * **Both registers start from a REVIVED schema, by construction.** The
 * only way to get a `Materialized` is `fromStore` or `fromPayload`, and
 * both revive through `CanonicalSchema.fromRepresentation` before they
 * hand anything back. This is not a preference: `toCode` lives in a
 * FUNCTION-valued annotation and does not survive `toJson`, so a
 * persisted document generates nothing at all — code generation runs on
 * the live schema revival produces, and on nothing else. The
 * SchemaMaterialization suite pins that fact directly.
 *
 * Nothing here maintains a second registry, a second decoder, or a
 * second address: the revision switch is `CanonicalSchema.fromEnvelope`,
 * the reviver set is `CanonicalSchema.Revivers`, and the address is
 * either the store's own verified id or the digest of the very bytes
 * that were materialized.
 *
 * **This door refuses exactly what Lean's `Cas.Schema.ingest` refuses.**
 * `CanonicalSchema.fromEnvelope` runs the admitted-subset gate before
 * anything is revived, so a node the Lean door turns away never becomes
 * a live validator here (the JIT-substrate survey's B8,
 * SCHEMA-MATERIALIZATION.md ruling-queue item 19). Both entry points run
 * the gate AND revival inside their own failure channel: a refusal is a
 * `ProjectionCodecFailure` carrying a named `CanonicalSchema.Refusal`,
 * never a defect. `library/cas/conformance/schema-verdicts.json` and
 * `test/SchemaVerdicts.test.ts` are what hold the two doors to it.
 */
import { Effect, Schema, SchemaRepresentation, type SchemaAST } from "effect"
import { CasNodeInput, type ContentId } from "./Node.ts"
import {
  AddressScheme,
  CasLoader,
  CasSchemeVersion,
  encodeCasNode,
} from "./Store.ts"
import {
  canonicalJson,
  decodedVersionedEnvelope,
  ProjectionCodecFailure,
  type ProjectionError,
} from "./Value.ts"
import * as CanonicalSchema from "./CanonicalSchema.ts"

/** One materialized canonical schema: the live carrier revived out of
 * stored content, and the content address of the node it came from.
 *
 * The address is never supplied by a caller. It is the store's own
 * verified id (`fromStore`) or the digest of the payload bytes that
 * were materialized (`fromPayload`), which is what makes the source
 * register's stamp evidence rather than decoration. */
export interface Materialized {
  readonly address: ContentId
  readonly schema: Schema.Top
}

/** One binding of a materialized module: a materialization plus the
 * name it is exported under. */
export interface Binding extends Materialized {
  readonly name: string
}

/** One representation as canonical JSON text — what two table entries
 * are compared BY. Equality of live representations is object identity,
 * which is the wrong question: two bindings can independently lower the
 * same shape. */
const codeJson = (
  representation: SchemaRepresentation.Representation,
): string =>
  canonicalJson(
    SchemaRepresentation.toJson({ representation, references: {} }),
  )

/** Every table name a representation mentions. `stopAtSuspend` is what
 * tells the two questions apart, and both are asked below:
 *
 * - FALSE — reachability. Which entries does this one depend on at all,
 *   which is what decides whether it lies on a cycle.
 * - TRUE — EAGER reachability. Which entries does its generated code
 *   read at module-evaluation time, which is what decides declaration
 *   order. Everything under a `Suspend` is read later, or never.
 *
 * The same two walks `CanonicalSchema` runs over stored spellings
 * (`allRefs` and `bareRefs`), here over a live lowering's JSON. */
const referenceNames = (
  representation: SchemaRepresentation.Representation,
  stopAtSuspend = false,
): ReadonlyArray<string> => {
  const out: Array<string> = []
  const walk = (value: unknown): void => {
    if (Array.isArray(value)) {
      for (const item of value) walk(item)
      return
    }
    if (typeof value !== "object" || value === null) return
    const node = value as Record<string, unknown>
    if (stopAtSuspend && node["_tag"] === "Suspend") return
    if (node["_tag"] === "Reference") {
      if (typeof node["$ref"] === "string") out.push(node["$ref"])
      return
    }
    for (const child of Object.values(node)) walk(child)
  }
  walk(SchemaRepresentation.toJson({ representation, references: {} }))
  return out
}

/** The table entries that lie on a cycle — read off the table itself,
 * independently of Effect's own split, which is why it can be used to
 * cross-check that split rather than to restate it.
 *
 * A name is on a cycle exactly when it reaches itself. The table is
 * small and the walk is a fold over finite trees, so the direct
 * reachability closure is the honest implementation. */
const cyclicNames = (
  references: Readonly<Record<string, SchemaRepresentation.Representation>>,
): ReadonlySet<string> => {
  const edges = new Map<string, ReadonlyArray<string>>()
  for (const [name, code] of Object.entries(references)) {
    edges.set(
      name,
      referenceNames(code).filter((one) => Object.hasOwn(references, one)),
    )
  }
  const cyclic = new Set<string>()
  for (const start of edges.keys()) {
    const seen = new Set<string>()
    const stack = [...edges.get(start)!]
    while (stack.length > 0) {
      const here = stack.pop()!
      if (here === start) {
        cyclic.add(start)
        break
      }
      if (seen.has(here)) continue
      seen.add(here)
      stack.push(...(edges.get(here) ?? []))
    }
  }
  return cyclic
}

/** Excess properties are a decode failure by default here, matching the
 * rest of the CAS plane: canonical content has exactly the fields its
 * code declares. A caller who wants Effect's laxer reading passes its
 * own options through. */
const strictOptions = {
  onExcessProperty: "error",
} satisfies SchemaAST.ParseOptions

/** Materialize the schema node at an address, through the store's read
 * seam. The loader re-verifies the resident bytes against the address,
 * so the id it was asked for IS the materialization's stamp. */
export const fromStore = (
  address: ContentId,
): Effect.Effect<Materialized, ProjectionError, CasLoader> =>
  CanonicalSchema.get(address).pipe(
    // ASSEMBLY, between the read and the revival: a reference whose name
    // is a content address is a typed EDGE into the store, and revival
    // cannot follow it — Effect resolves a `$ref` against the table it
    // was handed and nothing else. So the table is closed first, out of
    // store words, and a target of another kind is `WrongKindReference`
    // rather than a dangling name nobody mentions again. A document with
    // no address-named reference assembles to itself.
    Effect.flatMap(CanonicalSchema.assemble),
    Effect.flatMap((document) =>
      // Revival runs INSIDE the failure channel: a reviver that throws is
      // a refusal of these bytes, not a defect of the program that asked
      // for them (the survey's B8 — an unadmitted id used to explode).
      Effect.try({
        try: (): Materialized => ({
          address,
          schema: CanonicalSchema.fromRepresentation(document),
        }),
        catch: (issue) =>
          new ProjectionCodecFailure({
            direction: "decode",
            id: address,
            issue: String(issue),
          }),
      })
    ),
  )

/** Materialize one schema node's payload bytes, held in hand rather
 * than fetched. The address is DERIVED: the bytes are re-verified as
 * canonical, wrapped in the schema node envelope they belong to, and
 * digested under the ambient address scheme. A caller cannot stamp a
 * materialization with an address its bytes do not hash to.
 *
 * Deliberately does NOT assemble: this door has bytes and no store, and
 * an address-named reference is a question only a store can answer.
 * Adding a `CasLoader` here would make every payload-in-hand caller
 * carry one to materialize a schema that names nothing. A document whose
 * references are unresolved revives with them unresolved, which is what
 * Effect's own reviver does with a dangling `$ref` too. */
export const fromPayload = (
  payload: Uint8Array,
): Effect.Effect<Materialized, ProjectionError, AddressScheme> =>
  Effect.gen(function* () {
    // The one gate that has to see the BYTES: a references table naming
    // one entry twice is two different documents once a parser has been
    // at it, so it is refused by name before anything parses (PDD-3
    // break-pass finding F1). Everything after this point takes a value
    // that has already been read.
    yield* Effect.try({
      try: () => CanonicalSchema.admitPayloadSpelling(payload),
      catch: (issue) =>
        new ProjectionCodecFailure({
          direction: "decode",
          issue: String(issue),
        }),
    })
    const envelope = yield* decodedVersionedEnvelope(payload)
    // The gate AND revival, both inside the failure channel: the door
    // refuses by name (`CanonicalSchema.SchemaRefusal`) and never lets a
    // throw escape as a defect.
    const schema = yield* Effect.try({
      try: () =>
        CanonicalSchema.fromRepresentation(
          CanonicalSchema.fromEnvelope(envelope),
        ),
      catch: (issue) =>
        new ProjectionCodecFailure({
          direction: "decode",
          issue: String(issue),
        }),
    })
    const node = CasNodeInput.make({
      kind: { tag: CanonicalSchema.KindTag, version: CasSchemeVersion },
      payload,
      refs: [],
    })
    const address = yield* AddressScheme.use((scheme) =>
      scheme.digest(encodeCasNode(node))
    )
    return { address, schema }
  })

/** The VALIDATOR register: the decision a materialized schema makes
 * about one candidate value.
 *
 * Deliberately the thinnest possible surface — Effect's own decoder,
 * defaulted to the strict reading and otherwise untouched. There is no
 * estate-shaped result type, no re-spelled issue, and no second failure
 * taxonomy: `SchemaError` already says what went wrong, and wrapping it
 * would only lose Effect's own reporting. */
export const validator = (
  materialized: Materialized,
  options?: SchemaAST.ParseOptions,
): (input: unknown) => Effect.Effect<unknown, Schema.SchemaError> =>
  Schema.decodeUnknownEffect(
    materialized.schema as Schema.Codec<unknown, unknown>,
    options ?? strictOptions,
  )

/** The SOURCE register: rendered TypeScript for a set of
 * materializations, stamped with the addresses they were materialized
 * from.
 *
 * Pure and total in its inputs — the addresses already ride the
 * materializations, so the header cannot claim an address that was not
 * the one materialized. Generation itself is Effect's
 * `toCodeDocument`, run on the LIVE representation of each revived
 * schema; the estate adds only the module frame and the stamp.
 *
 * **The MultiDocument assembly step** (PDD-13 slice 4). A recursive
 * schema allocates a references table, so a table is no longer a reason
 * to refuse: the bindings' tables are UNIONED into one MultiDocument and
 * the whole set is generated together, which is also what lets several
 * bindings share one named definition instead of each inlining a copy.
 * A name bound twice must be bound to the same code — two bindings can
 * each allocate `Objects_` for a different shape, and keeping one
 * silently is a wrong answer with no error.
 *
 * Fail-closed on everything the admitted subset does not yet reach: a
 * name that is not a TypeScript identifier, a duplicate name, a table
 * name bound to two codes, a reference naming no table entry (the door
 * ADMITS a dangling name — `CanonicalSchema.assemble` is what closes an
 * address-named one, and nothing closes a plain one), a table entry
 * whose declaration order cannot be made sound, and a generated artifact
 * that is not an import (unique symbols are not an admitted
 * representation node yet). */
export const source = (bindings: ReadonlyArray<Binding>): string => {
  const seen = new Set<string>()
  for (const binding of bindings) {
    if (!/^[A-Za-z_$][A-Za-z0-9_$]*$/u.test(binding.name)) {
      throw new TypeError(
        `materialized binding name ${canonicalJson(binding.name)} is not a TypeScript identifier`,
      )
    }
    if (seen.has(binding.name)) {
      throw new TypeError(
        `materialized binding name ${canonicalJson(binding.name)} is declared twice`,
      )
    }
    seen.add(binding.name)
  }

  // The live lowering: not JSON-round-tripped, so the `toCode`
  // annotations generation needs are still attached.
  const documents = bindings.map((binding) =>
    SchemaRepresentation.toRepresentation(binding.schema.ast)
  )

  // THE ASSEMBLY: one table over every binding.
  const references: Record<string, SchemaRepresentation.Representation> = {}
  for (const [index, document] of documents.entries()) {
    for (const [name, code] of Object.entries(document.references)) {
      const seated = references[name]
      if (seated !== undefined && codeJson(seated) !== codeJson(code)) {
        throw new TypeError(
          `materializing ${bindings[index]!.name} binds the reference name ${
            canonicalJson(name)
          } to a second code`,
        )
      }
      references[name] = code
    }
  }

  const representations = documents.map((document) => document.representation)
  // Effect's generator THROWS on a `$ref` with no entry, and the estate's
  // door admits one (a dangling name lies on no cycle, so guardedness
  // has nothing to say about it). Name it here rather than let an
  // anonymous throw out of the generator stand for it.
  for (const [name, code] of Object.entries(references)) {
    for (const named of referenceNames(code)) {
      if (!Object.hasOwn(references, named)) {
        throw new TypeError(
          `materializing the reference table entry ${canonicalJson(name)} needs ${
            canonicalJson(named)
          }, which no entry answers`,
        )
      }
    }
  }
  for (const [index, representation] of representations.entries()) {
    for (const named of referenceNames(representation)) {
      if (!Object.hasOwn(references, named)) {
        throw new TypeError(
          `materializing ${bindings[index]!.name} needs the reference ${
            canonicalJson(named)
          }, which no table entry answers`,
        )
      }
    }
  }

  const generated = representations.length === 0
    ? {
      artifacts: [],
      codes: [],
      references: { nonRecursives: [], recursives: {} },
    }
    : SchemaRepresentation.toCodeDocument({
      references,
      representations: representations as [
        SchemaRepresentation.Representation,
        ...Array<SchemaRepresentation.Representation>,
      ],
    })

  const imports = [`import { Schema } from "effect"`]
  const auxiliaries: Array<string> = []
  const auxiliarySeen = new Set<string>()
  for (const artifact of generated.artifacts) {
    if (artifact._tag === "Import") {
      if (!imports.includes(artifact.importDeclaration)) {
        imports.push(artifact.importDeclaration)
      }
      continue
    }
    if (artifact._tag === "Enum") {
      // An enum member table, emitted once above the bindings that name
      // it. Effect prints a TypeScript `enum` declaration; this package
      // is `erasableSyntaxOnly`, so the table is respelled as the object
      // literal that builds the identical `SchemaAST.Enum` — the same
      // move the hand mirrors make.
      if (!auxiliarySeen.has(artifact.identifier)) {
        auxiliarySeen.add(artifact.identifier)
        const open = artifact.code.runtime.indexOf("{")
        const close = artifact.code.runtime.lastIndexOf("}")
        if (open < 0 || close <= open) {
          throw new TypeError(
            `materialized Enum artifact ${artifact.identifier} has no member table to respell`,
          )
        }
        const members = artifact.code.runtime
          .slice(open + 1, close)
          .replaceAll(" = ", ": ")
        auxiliaries.push(
          [
            `const ${artifact.identifier} = {${members}} as const`,
            `type ${artifact.identifier} = (typeof ${artifact.identifier})[keyof typeof ${artifact.identifier}]`,
          ].join("\n"),
        )
      }
      continue
    }
    throw new TypeError(
      `materialized source needs a ${artifact._tag} artifact, which the admitted subset does not carry`,
    )
  }

  // The table, declared above the bindings that name it. `const`
  // bindings are hoisted into a temporal dead zone, so DECLARATION ORDER
  // IS SEMANTICS: an entry read at module-evaluation time before its own
  // declaration throws, and the module that emitted it is a module that
  // does not load.
  //
  // Effect's generator hands back two groups, and the order rests on
  // what each guarantees. `recursives` are the entries that lie on a
  // cycle, and every reference BETWEEN them is printed through
  // `Schema.suspend`, so no order among them can be wrong — they go
  // first. `nonRecursives` is topologically sorted among itself, so each
  // is declared after every plain entry it names; a plain entry naming a
  // recursive one is then already answered, because the recursives are
  // above.
  //
  // The one edge that order cannot serve is the other way round: a
  // RECURSIVE entry reading a PLAIN one eagerly. Effect's sort skips that
  // edge (it sorts only among the plain entries), so the estate refuses
  // by name rather than guessing. Nothing in the admitted subset reaches
  // it today: it takes a shared NAMED definition beside a recursive one,
  // and a name puts an `annotations` bag on the table entry, which
  // SM-21 still blocks. OWED when it does: a topological sort over the
  // EAGER edges, which is well founded — an eager cycle would be a
  // reference cycle with no `Suspend` on it, and that is exactly what
  // the door refuses `unguardedCycle`.
  const cyclic = cyclicNames(references)
  const recursiveNames = new Set(Object.keys(generated.references.recursives))
  // The two readings of "which entries lie on a cycle" — the estate's own
  // walk and Effect's — must agree in size, or the order above is
  // reasoning about a split it does not actually have.
  if (cyclic.size !== recursiveNames.size) {
    throw new TypeError(
      `materialized reference table: the estate reads ${cyclic.size} recursive entries and Effect's generator reads ${recursiveNames.size}`,
    )
  }
  for (const name of cyclic) {
    for (const named of referenceNames(references[name]!, true)) {
      if (Object.hasOwn(references, named) && !cyclic.has(named)) {
        throw new TypeError(
          `materialized reference ${canonicalJson(name)} reads the plain entry ${
            canonicalJson(named)
          } eagerly, which this emitter cannot order`,
        )
      }
    }
  }

  const tableDeclarations: Array<string> = []
  const declare = (name: string, code: SchemaRepresentation.Code): void => {
    if (seen.has(name)) {
      throw new TypeError(
        `materialized reference name ${canonicalJson(name)} collides with a binding of the same name`,
      )
    }
    tableDeclarations.push(
      [
        `const ${name} = ${code.runtime}`,
        ``,
        `type ${name} = ${code.Type}`,
      ].join("\n"),
    )
  }
  for (const [name, code] of Object.entries(generated.references.recursives)) {
    declare(name, code)
  }
  for (const entry of generated.references.nonRecursives) {
    declare(entry.$ref, entry.code)
  }

  const stamps = bindings.map((binding) =>
    ` *   - ${binding.name} — ${binding.address}`
  )
  const header = [
    `/**`,
    ` * GENERATED — do not edit. Materialized from canonical schema nodes`,
    ` * by \`Cas.Materialize.source\`: every binding below is what Effect's`,
    ` * own \`SchemaRepresentation.toCodeDocument\` prints for the schema`,
    ` * revived out of the addressed node. The addresses are the stamp`,
    ` * that makes this file a projection of store content and parity a`,
    ` * digest check (R7, the served-equals-derived wall) — regenerate,`,
    ` * never edit.`,
    ` *`,
    ` * Materialized from schema nodes (kind tag 0x${
      CanonicalSchema.KindTag.toString(16)
    }):`,
    ...stamps,
    ` */`,
  ]

  const declarations = bindings.map((binding, index) => {
    const code = generated.codes[index]!
    return [
      `export const ${binding.name} = ${code.runtime}`,
      ``,
      `export type ${binding.name} = ${code.Type}`,
    ].join("\n")
  })

  // Enum tables first (a table entry may name one), then the reference
  // table, then the exported bindings that name it.
  const body = [...auxiliaries, ...tableDeclarations, ...declarations]
    .join("\n\n")

  return `${[...header, ...imports, ``, body].join("\n")}\n`
}

