/-!
# Store.Kind

Owner: the kind table of the store, the byte that files a node under its kind.

The table is `docs/research/2026-09-04-cas-trait-plan.md` §3: fifteen kinds, bytes 1–15 in the
order listed there, seven of them (`type`, `entry`, `query`, `result`, `chunk`, `manifest`,
`fiber`) reserved with no Lean consumer in this landing. Bytes are identity (the second byte of
every node, `nodeBytes = 0 :: kind.byte :: spec ++ payload` per the facts note's Q3), so the
table is fixed now, appended later, never renumbered. The kind byte is not injective on types:
several carriers file as `annotation`, and their `Ref`s stay different Lean types.

`byte` is the table; `ofByte?` and `ofName?` are lookups in the census `all`, so the round
trips are one `decide` each and the two injectivity theorems are corollaries, the way
`RepresentationTag.tagName_injective` is proved (`src/Effect4/Schema/Representation.lean:200`).
`export` is a Lean keyword, so the constructor is spelled `«export»`; its name is `"export"`.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- The kind of a node, in the plan's byte order. -/
inductive Kind where
  /-- A pinned source file (today's `FilePin`), a pinned span, an implementation. -/
  | source
  /-- One export of the pinned standard library (`Entry`). -/
  | «export»
  /-- Reserved for the extractor lane. -/
  | type
  /-- A schema `Document`: every spec; the meta-schema is the zero-spec genesis. -/
  | schema
  /-- An `Eff` program. -/
  | program
  /-- A trait, a receipt, a claim, a piece of evidence, a target, a characterization. -/
  | annotation
  /-- Reserved for the journal. -/
  | entry
  /-- Reserved. -/
  | query
  /-- Reserved. -/
  | result
  /-- Reserved for the blob kinds. -/
  | chunk
  /-- A name space: name → reference pairs. -/
  | tree
  /-- Reserved for the blob kinds. -/
  | manifest
  /-- The Char room's `Manifest`. -/
  | component
  /-- A vector set, a vector, a fact. -/
  | vector
  /-- Reserved. -/
  | fiber
deriving DecidableEq, Repr, Inhabited

namespace Kind

/-- The kind byte of the table. -/
def byte : Kind → UInt8
  | .source => 1
  | .«export» => 2
  | .type => 3
  | .schema => 4
  | .program => 5
  | .annotation => 6
  | .entry => 7
  | .query => 8
  | .result => 9
  | .chunk => 10
  | .tree => 11
  | .manifest => 12
  | .component => 13
  | .vector => 14
  | .fiber => 15

/-- The kind's spelling, the one the spec annotations and the printer use. -/
def name : Kind → String
  | .source => "source"
  | .«export» => "export"
  | .type => "type"
  | .schema => "schema"
  | .program => "program"
  | .annotation => "annotation"
  | .entry => "entry"
  | .query => "query"
  | .result => "result"
  | .chunk => "chunk"
  | .tree => "tree"
  | .manifest => "manifest"
  | .component => "component"
  | .vector => "vector"
  | .fiber => "fiber"

/-- The census, in byte order. -/
def all : List Kind :=
  [.source, .«export», .type, .schema, .program, .annotation, .entry, .query, .result, .chunk,
   .tree, .manifest, .component, .vector, .fiber]

/-- The kind filed under a byte, if any. -/
def ofByte? (b : UInt8) : Option Kind := all.find? fun k => decide (k.byte = b)

/-- The kind with a spelling, if any. -/
def ofName? (s : String) : Option Kind := all.find? fun k => decide (k.name = s)

theorem all_length : all.length = 15 := by decide

theorem mem_all (k : Kind) : k ∈ all := by cases k <;> decide

theorem ofByte?_byte (k : Kind) : ofByte? k.byte = some k := by
  cases k <;> decide

theorem byte_ofByte? {b : UInt8} {k : Kind} (h : ofByte? b = some k) : k.byte = b := by
  have h' : all.find? (fun k => decide (k.byte = b)) = some k := h
  have h2 := List.find?_some h'
  exact of_decide_eq_true h2

theorem byte_injective {a b : Kind} (h : a.byte = b.byte) : a = b := by
  have ha := ofByte?_byte a
  rw [h, ofByte?_byte b] at ha
  exact (Option.some.inj ha).symm

theorem ofName?_name (k : Kind) : ofName? k.name = some k := by
  cases k <;> decide

theorem name_ofName? {s : String} {k : Kind} (h : ofName? s = some k) : k.name = s := by
  have h' : all.find? (fun k => decide (k.name = s)) = some k := h
  have h2 := List.find?_some h'
  exact of_decide_eq_true h2

theorem name_injective {a b : Kind} (h : a.name = b.name) : a = b := by
  have ha := ofName?_name a
  rw [h, ofName?_name b] at ha
  exact (Option.some.inj ha).symm

/-- Every kind byte is in `1..15`; `0` is the version byte and never a kind. -/
theorem byte_pos (k : Kind) : 0 < k.byte.toNat := by cases k <;> decide

theorem byte_le (k : Kind) : k.byte.toNat ≤ 15 := by cases k <;> decide

end Kind

/-! ## The table, guarded -/

#guard Kind.byte .source = 1
#guard Kind.byte .«export» = 2
#guard Kind.byte .schema = 4
#guard Kind.byte .program = 5
#guard Kind.byte .annotation = 6
#guard Kind.byte .tree = 11
#guard Kind.byte .component = 13
#guard Kind.byte .vector = 14
#guard Kind.byte .fiber = 15
#guard Kind.ofByte? 0 = none
#guard Kind.ofByte? 16 = none
#guard Kind.ofByte? 2 = some .«export»
#guard Kind.ofName? "export" = some .«export»
#guard Kind.ofName? "Export" = none

/-! ## Receipts -/

#print axioms Kind.byte
#print axioms Kind.name
#print axioms Kind.ofByte?
#print axioms Kind.ofName?
#print axioms Kind.all_length
#print axioms Kind.mem_all
#print axioms Kind.ofByte?_byte
#print axioms Kind.byte_ofByte?
#print axioms Kind.byte_injective
#print axioms Kind.ofName?_name
#print axioms Kind.name_ofName?
#print axioms Kind.name_injective
#print axioms Kind.byte_pos
#print axioms Kind.byte_le

end Effect4.Store
