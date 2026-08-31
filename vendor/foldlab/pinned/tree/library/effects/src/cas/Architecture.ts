/**
 * The architecture, as a value — the library described in itself.
 *
 * The description is no longer written here. `Cas.foldlabCas`
 * (`library/cas/Cas/Architecture.lean`) is its one home, and
 * `lake exe emitarchitecture` prints it into
 * `generated/architecture.ts`; this module is the Effect-native
 * lifting of those rows — a Schema (the codec of the description), a
 * value (this library), a service (the description as a dependency),
 * and a layer (providing it).
 *
 * What that replaced: two hand-maintained spellings of the same
 * fifty-seven strings, held together by one shared pin over a
 * projection that deliberately drops the prose. The pin could see the
 * capability matrix and nothing else, so the two sides could disagree
 * about what a law MEANS — or about the order a backend's capabilities
 * are written in, which is exactly what they had come to disagree
 * about — with every gate in the estate green.
 *
 * The matrix is still derived here and still compared against the
 * pinned string, because that comparison is what says the two
 * DERIVATIONS agree: the model renders it through `Cas.Json`, this
 * side through `canonicalJson`, and the literal they meet at is now
 * emitted rather than retyped.
 */
import { Context, Layer, Schema } from "effect"
import { architecture, capabilityMatrixPin as emittedPin } from "./generated/architecture.ts"

/** One capability of the byte plane — the unit the seams split by. */
export const Capability = Schema.Literals(["read", "roots", "write"])
export type Capability = typeof Capability.Type

/** One carrier of the data vocabulary, with its model and runtime
 * homes. */
export const ArchType = Schema.Struct({
  form: Schema.String,
  lean: Schema.String,
  name: Schema.String,
  ts: Schema.String,
})
export type ArchType = typeof ArchType.Type

/** One law above the seams: what it means and which capabilities it
 * needs — nothing else about storage. */
export const ArchLaw = Schema.Struct({
  means: Schema.String,
  name: Schema.String,
  needs: Schema.Array(Capability),
  plane: Schema.Literals(["cas", "server"]),
})
export type ArchLaw = typeof ArchLaw.Type

/** One backend below the seams: which capabilities it provides. */
export const ArchBackend = Schema.Struct({
  means: Schema.String,
  name: Schema.String,
  provides: Schema.Array(Capability),
})
export type ArchBackend = typeof ArchBackend.Type

/** The library's shape: data vocabulary, seams, laws, backends. */
export const Description = Schema.Struct({
  backends: Schema.Array(ArchBackend),
  laws: Schema.Array(ArchLaw),
  seams: Schema.Array(Capability),
  types: Schema.Array(ArchType),
})
export type Description = typeof Description.Type

/** The value: `@foldlab/cas` — the emitted rows, lifted through the
 * description's own Schema. */
export const value: Description = Description.make(architecture)

/** The seam capabilities mapped to the service keys that realize them
 * — asserted against the real tags by the architecture suite.
 *
 * Hand-written, and not a candidate for emission: a service key is a
 * TypeScript fact. The model quantifies over the seams; it does not
 * know what `Context.Service` tags this runtime mints for them, and a
 * generated table of keys nothing on the Lean side can check would be
 * provenance without authority. */
export const seamKeys = {
  read: "foldlab/cas/ByteReader",
  roots: "foldlab/cas/RootStore",
  write: "foldlab/cas/ByteWriter",
} satisfies Record<Capability, string>

/** The digest every law recomputes, as its own dependency: not a seam
 * (it stores nothing) and not a law (it decides nothing) — the scheme
 * the composition chooses, which is why the model quantifies over it.
 * A service key, so it stays hand-written beside `seamKeys`. */
export const addressSchemeKey = "foldlab/cas/AddressScheme"

/** The description as a dependency: ask the context what the library
 * is. */
export class Service extends Context.Service<Service, Description>()(
  "foldlab/cas/Architecture",
) {}

/** Provide the description. */
export const layer: Layer.Layer<Service> = Layer.succeed(Service, value)

const sorted = (items: ReadonlyArray<string>): ReadonlyArray<string> =>
  items.toSorted()

/** The shape of the shared projection, named so the derivation keeps
 * its type evidence. */
export interface CapabilityMatrix {
  readonly backends: Record<string, ReadonlyArray<string>>
  readonly laws: Record<string, ReadonlyArray<string>>
  readonly seams: ReadonlyArray<string>
  readonly types: ReadonlyArray<string>
}

/** The load-bearing shared projection — one canonical-JSON object both
 * descriptions derive and pin. Sorting is the whole reason the pin
 * survived the two sides writing their capability lists in different
 * orders; it is kept because the projection is about MEMBERSHIP, and
 * the description's own row order is prose. */
export const capabilityMatrix = (description: Description): CapabilityMatrix => ({
  backends: Object.fromEntries(description.backends.map((backend) =>
    [backend.name, sorted(backend.provides)])),
  laws: Object.fromEntries(description.laws.map((law) =>
    [law.name, sorted(law.needs)])),
  seams: sorted(description.seams),
  types: sorted(description.types.map((carrier) => carrier.name)),
})

/** The pinned canonical rendering, emitted from the model's
 * `Cas.capabilityMatrixPin`. Changing the shape now means changing it
 * in ONE home and regenerating — which is what the byte gate is for. */
export const capabilityMatrixPin: string = emittedPin
