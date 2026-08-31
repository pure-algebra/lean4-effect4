/**
 * Per-kind semantics — the Ty-indexed algebra from CasGrammar.lean.
 *
 * `render` is pure and SHALLOW by type (a function of the node alone) — the
 * Lean spec makes context reproducibility the signature, not a theorem.
 * Depth arrives only through affordances. `Registry` is a total record over
 * `KindName`: a kind without semantics is a compile error (the Lean
 * `Registry := Ty → KindSem` totality check, in TypeScript).
 *
 * Affordance law (Lean `affords_sound`, proved there as `refAffords_sound`):
 * every affordance targets an existing reference — navigation never mints
 * reachability. `refAffordances` keeps it true by construction.
 */
import type { Cas } from "../../src/index.ts"
import { textOf, type KindName } from "./kinds.ts"

export interface Affordance {
  readonly name: string
  readonly target: Cas.ContentId
}

export interface KindSemantics {
  readonly render: (node: Cas.NodeInput) => string
  readonly affordances: (node: Cas.NodeInput) => ReadonlyArray<Affordance>
}

export type Registry = Readonly<Record<KindName, KindSemantics>>

/** Targets drawn from the node's own refs — `affords_sound` by construction. */
const refAffordances = (node: Cas.NodeInput): ReadonlyArray<Affordance> =>
  node.refs.map((ref, index) => ({ name: `ref:${index}[tag=${ref.expectedTag}]`, target: ref.id }))

const none = (): ReadonlyArray<Affordance> => []

const short = (id: string): string => id.slice(0, 8)

/** Folder payload: newline-joined names, positionally aligned with refs.
 * (Sketch framing; the package version is a Schema-encoded canonical value.) */
const folderNames = (node: Cas.NodeInput): ReadonlyArray<string> =>
  textOf(node.payload).split("\n").filter((name) => name.length > 0)

export const registry: Registry = {
  value: {
    render: (n) => textOf(n.payload),
    affordances: none,
  },
  chunk: {
    render: (n) => `<chunk ${n.payload.length}B>`,
    affordances: none,
  },
  tree: {
    render: (n) => `<tree: ${n.refs.length} children>`,
    affordances: refAffordances,
  },
  manifest: {
    render: (n) => `<blob header ${n.payload.length}B>`,
    affordances: refAffordances,
  },
  file: {
    render: (n) => `<file ${textOf(n.payload)}>`,
    affordances: refAffordances,
  },
  entry: {
    render: (n) => `<entry note=${textOf(n.payload)}>`,
    affordances: refAffordances,
  },
  context: {
    render: (n) => `<context: ${n.refs.length} items>`,
    affordances: refAffordances,
  },
  folder: {
    // A git tree "acts like a file structure": render the LISTING, expose
    // expansion as affordances — the agent explores lazily, never inlines.
    render: (n) =>
      folderNames(n)
        .map((name, i) => `${name} -> ${short(n.refs[i]?.id ?? "?")}`)
        .join("\n"),
    affordances: (n) =>
      folderNames(n).map((name, i) => ({
        name: `expand:${name}`,
        target: (n.refs[i]?.id ?? n.refs[0]?.id) as Cas.ContentId,
      })),
  },
}
