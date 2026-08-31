/**
 * GENERATED — do not edit. THE KIND-TAG REGISTRY, as data: every wire
 * tag `Cas.Grammar.manifestV0` gives a row, emitted from
 * `library/cas/Cas/Grammar/Manifest.lean` by `lake exe emitgrammar`;
 * regeneration is byte-identity-gated (`--check`, wired into
 * `check:cas`). `REGISTRY.md` is the same table's human rendering and
 * `manifest.json` its machine one.
 *
 * `src/internal/kindTags.ts` is the door's projection of this file.
 * `Cas.value` refuses every tag listed here, which is what stops a
 * caller-defined projection from aliasing a kind plane the library
 * already reads. A RESERVED row is a code point the registry holds
 * outside `Ty`; none is today (14 and 15 were ratified as the `step`
 * and `cont` sorts on 2026-08-29). Reserved or ratified, a row is
 * refused identically, because a tag with a second public
 * interpretation is the same hole either way — so this door's
 * membership did not move when those two rows did.
 *
 * emitted — schemaVersion 1, emitter `emitgrammar`,
 * module `library/cas/tools/EmitGrammar.lean`, toolchain Lean 4.33.1.
 */

/** One registry row's tag surface: the sort's registry name, its
 * wire kind tag, and whether the row is RESERVED — a code point the
 * registry holds outside `Ty` — rather than a ratified sort. No row
 * is reserved today; both kinds are refused identically at the door,
 * so the flag is a fact about the registry, never a door policy. */
export interface KindTagRow {
  readonly name: string
  readonly tag: number
  readonly reserved: boolean
}

/** Every registry row, in registry order — the table
 * `REGISTRY.md` renders for humans, as data. */
export const KindTagRows: ReadonlyArray<KindTagRow> = [
  {
    name: "value",
    tag: 1,
    reserved: false,
  },
  {
    name: "chunk",
    tag: 8,
    reserved: false,
  },
  {
    name: "tree",
    tag: 9,
    reserved: false,
  },
  {
    name: "manifest",
    tag: 10,
    reserved: false,
  },
  {
    name: "file",
    tag: 11,
    reserved: false,
  },
  {
    name: "entry",
    tag: 12,
    reserved: false,
  },
  {
    name: "context",
    tag: 13,
    reserved: false,
  },
  {
    name: "step",
    tag: 14,
    reserved: false,
  },
  {
    name: "cont",
    tag: 15,
    reserved: false,
  },
  {
    name: "annotation",
    tag: 65,
    reserved: false,
  },
  {
    name: "git",
    tag: 71,
    reserved: false,
  },
  {
    name: "agent",
    tag: 73,
    reserved: false,
  },
  {
    name: "query",
    tag: 81,
    reserved: false,
  },
  {
    name: "result",
    tag: 82,
    reserved: false,
  },
  {
    name: "schema",
    tag: 83,
    reserved: false,
  },
]

/** The registry's wire tags by sort name: how a consumer names
 * one row without repeating its number. */
export const KindTagsByName = {
  value: 1,
  chunk: 8,
  tree: 9,
  manifest: 10,
  file: 11,
  entry: 12,
  context: 13,
  step: 14,
  cont: 15,
  annotation: 65,
  git: 71,
  agent: 73,
  query: 81,
  result: 82,
  schema: 83,
}

/** THE door's refusal set: every tag the registry gives a row,
 * in registry order. `Cas.value` refuses each of these, so a
 * caller-defined projection can never give a registry row a second
 * public interpretation. */
export const GrammarKindTags: ReadonlyArray<number> = [1, 8, 9, 10, 11, 12, 13, 14, 15, 65, 71, 73, 81, 82, 83]
