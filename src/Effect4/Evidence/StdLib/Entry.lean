import Effect4.Store.Genesis
import Effect4.Store.PinDerived

/-!
# StdLib.Entry

Owner: the carriers the pinned standard library's census is made of — a pinned file, one
export, and the name space a census is read through — as store content.

A `Source` is a file of the pinned install with the SHA-256 the census instrument
(`scripts/generate-stdlib-census.ps1`) read off it; the digest is a `Digest`, not a hex string,
because hex left the carriers with the facts note's Q4 and `Digest.hex` is the one printer. An
`Entry` is one `export` declaration of such a file: its module, its exported name, the kind the
instrument recognised, the line, and `source : Ref Source` — a typed pointer at the file's node,
which admission resolves at kind `source` before the entry is admitted (Q4). So an entry can no
longer name a file the store does not hold.

Neither carrier writes a `Canonical` instance: both are generated into
`src/Effect4/Evidence/StdLib/Derived.lean` with the kinds `source` and `export`
(`Store/Kind.lean:25-28`), and the spec each node carries is the address of its shape's
document, derived and never a field (Q3). The documents under their old names (`entryDoc`,
`sourceDoc`, `treeDoc`) and the shape's printer (`Entry.json`, `Source.json`) are therefore
below the generated module, in `StdLib/Links.lean`; JSON is the spec language and the printer,
never identity (Q1).

The name space a census is read through is the store's own `Tree` (`src/Effect4/Store/Node.lean`),
the payload of a node at kind `tree`: name → reference pairs, the one way a name reaches content
now that the trie and its paths are retired (Q3, "names leave the store"). Its instance is
generated beside `Pin`'s; the total combinators the census folds with (`putOr`, `putRootOr`) are
the store's too (`src/Effect4/Store/Store.lean`).
-/

set_option autoImplicit false

namespace Effect4.StdLib

open Effect4.Store

/-! ## The carriers -/

/-- The declaration kinds the census recognises. -/
inductive ExportKind where
  /-- `export const`. -/
  | const
  /-- `export function`. -/
  | function
  /-- `export class`, `export abstract class`. -/
  | class_
  /-- `export interface`. -/
  | interface
  /-- `export type`. -/
  | type
  /-- `export namespace`, `export declare namespace`. -/
  | namespace_
deriving DecidableEq, Repr, Inhabited

/-- The TypeScript spelling, which is the census TSV's column. It is not what the shape renders:
the generated document and printer read the *constructor* names off the inductive, so `class_`
and `namespace_` cross the app face and this table stays the instrument's. -/
def ExportKind.spelling : ExportKind → String
  | .const => "const"
  | .function => "function"
  | .class_ => "class"
  | .interface => "interface"
  | .type => "type"
  | .namespace_ => "namespace"

/-- The alphabet, in declaration order: the cases of the generated sum, which Q5 renders as an
`anyOf` of string literals because every case is nullary. -/
def ExportKind.all : List ExportKind :=
  [.const, .function, .class_, .interface, .type, .namespace_]

/-- One file of the pinned install: the module it serves, its path inside the package, and the
SHA-256 the instrument read. The digest is foreign — it names bytes outside the store and is
checked by recomputation, never resolved (Q4) — so it is a `Digest` and not a `Ref`. -/
structure Source where
  /-- The module the file serves, `Effect` for `src/Effect.ts`. -/
  module : String
  /-- The path inside the package. -/
  file : String
  /-- The SHA-256 of the file's bytes. -/
  sha256 : Digest
deriving DecidableEq, Repr

/-- One export of a pinned module, with a typed pointer at the file it was read from. -/
structure Entry where
  /-- The module the export belongs to. -/
  module : String
  /-- The exported name. -/
  name : String
  /-- The declaration kind. -/
  kind : ExportKind
  /-- The line the declaration starts on. -/
  line : Nat
  /-- The file's node; admission resolves it at kind `source`. -/
  source : Ref Source
deriving DecidableEq, Repr

/-! ## Names

A census path is `[module, name]` and the tree binds it under `module/name`. `pathName` is the
one joiner: the store keeps no paths, so the spelling has to be a function both the namer and
the reader call. -/

/-- A path joined with slashes: the name a tree binds it under. -/
def pathName : List String → String
  | [] => ""
  | [segment] => segment
  | segment :: rest => segment ++ "/" ++ pathName rest

/-- Where an entry is bound in the census tree. -/
def Entry.pathName (entry : Entry) : String := StdLib.pathName [entry.module, entry.name]

#guard pathName ["Effect", "gen"] = "Effect/gen"
#guard pathName [] = ""
#guard pathName ["Effect"] = "Effect"
#guard Entry.pathName ⟨"Ref", "get", .const, 1, ⟨zeroDigest⟩⟩ = "Ref/get"

/-! ## Hexadecimal in a generated file

The census instrument writes each file's digest as sixty-four hexadecimal characters, so the
generated module needs a `String → Digest` that elaborates without a proof term per row.
`digestOfHex` is that total helper; it is total by falling back on the zero digest, and the
fallback is kept from ever firing by the generated `#guard` over `rawSources`, which refuses
the whole module if any literal is not thirty-two bytes of hexadecimal. The alternative the
landing offered — `Digest.ofHex? "…"` with a `by decide` beside every row — was refused
because it puts twenty-one kernel evaluations of the hex reader into a data module for no
stronger a statement than the guard's. -/

/-- A digest from a census literal, either case; the zero digest when the literal is not
thirty-two bytes of hexadecimal. Generated modules guard their literals, so the fallback is
unreachable there. -/
def digestOfHex (hex : String) : Digest := (Digest.ofHex? hex).getD zeroDigest

#guard digestOfHex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" = sha256 []
#guard digestOfHex "not-hex" = zeroDigest

/-! ## Receipts -/

#print axioms ExportKind.spelling
#print axioms ExportKind.all
#print axioms pathName
#print axioms Entry.pathName
#print axioms digestOfHex
#print axioms Effect4.Store.putOr
#print axioms Effect4.Store.putRootOr

end Effect4.StdLib
