module

public import Effect4.Store.Domain.Document

/-!
# Store.Action

Owner: the stored records of host actions: an action's identity (`ActionId`), a query
(`Query κ`, kind `query`) and the result envelope (`Answered κ`, kind `result`), with the one
reader that node admission applies to every result node (`Node.resultQuery?`).

A result is the answer of a host action: a gate or an outside oracle (seams plan §4.5, §9 D1). No
checker result is stored. An action whose output varies puts a run identity in its query's input,
and a new action version names a new query.

- `Query κ` follows `Annotation τ` (`src/Effect4/Store/Domain/Traits.lean`): the input field takes
  the input carrier's own shape and table, so a query's specification names its input's shape.
- `Answered κ` holds its output as the raw value tree, embedded as is (`Shape.value`). Its
  references stay edges of the result node, which admission resolves. The generated `Canonical Val`
  instance would hide them: it frames a reference as data.
- `κ` is a phantom in `Answered κ`: the query is a reference at kind `query`, so every result
  shares one envelope grammar and one specification, `specOf (Answered Unit)`.

`Node.resultQuery?` reads that common envelope at node version 0, envelope version 0 and the
common specification, and answers the designated query: the envelope's query field, never a
reference inside the output. `Node.resultQuery?_eq_some_iff` states the reading exactly. The
store refuses a result node that does not read (`Admission.badEnvelope`), and a second distinct
result for one query (`Admission.poisoned`, `src/Effect4/Store/Domain/Store.lean`).

Placement: `exact-codecs`, stored carriers, R13. The readers are exact embeddings
(`guarded`). They establish payload identity under the declared carrier. They establish no result
truth, host determinism, progress or hash injectivity.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

/-! ## The action's identity -/

/-- A host action: its name, its version and the engine that runs it. -/
structure ActionId where
  name : String
  version : Nat
  engine : Digest
deriving DecidableEq, Repr

namespace ActionId

/-- A struct of the name, the version and the engine digest. -/
def shapeDoc : ShapeDoc :=
  ⟨.struct "ActionId" [("name", .string), ("version", .nat), ("engine", .digest)], []⟩

/-- Constructor `0` with the three fields in declaration order. -/
def write (a : ActionId) : Val := .ctor 0 [.str a.name, .nat a.version, .bytes a.engine.bytes]

/-- The structural reader; `guarded` makes it exact. -/
def raw : Val → Option ActionId
  | .ctor 0 [.str name, .nat version, .bytes engine] =>
    (Digest.ofBytes? engine).map fun digest => ⟨name, version, digest⟩
  | _ => none

theorem raw_write (a : ActionId) : raw (write a) = some a := by
  simp only [write, raw, Digest.ofBytes?_bytes, Option.map_some]

theorem fits_write (a : ActionId) : shapeDoc.accepts (write a) = true := by
  simp only [shapeDoc, write, ShapeDoc.accepts, acceptsIn, candidates, List.any_cons,
    List.any_nil, Bool.or_false, acceptsAt, acceptsFields, a.engine.length_eq,
    decide_true, Bool.true_and]

instance instCanonical : Canonical ActionId where
  shape := shapeDoc
  toVal := write
  ofVal := guarded write raw
  ofVal_toVal a := guarded_toVal write raw a (raw_write a)
  ofVal_exact := guarded_exact
  fits := fits_write

end ActionId

/-! ## The query -/

/-- One question to a host action: the action and its input. -/
structure Query (κ : Type) where
  action : ActionId
  input : κ
deriving Repr

namespace Query

variable {κ : Type} [Canonical κ]

/-- A struct of the action and the input, over the input carrier's table. -/
def shapeDoc (κ : Type) [Canonical κ] : ShapeDoc :=
  ⟨.struct "Query" [("action", ActionId.shapeDoc.root), ("input", (shape κ).root)], (shape κ).defs⟩

/-- Constructor `0` with the two fields in declaration order. -/
def write (q : Query κ) : Val := .ctor 0 [toVal q.action, toVal q.input]

/-- The structural reader: each field through its own exact reader. -/
def raw : Val → Option (Query κ)
  | .ctor 0 [action, input] =>
    match ofVal action, ofVal input with
    | some a, some i => some ⟨a, i⟩
    | _, _ => none
  | _ => none

theorem raw_write (q : Query κ) : raw (write q) = some q := by
  simp only [write, raw, ofVal_toVal]

theorem fits_write (q : Query κ) : (shapeDoc κ).accepts (write q) = true := by
  apply accepts_struct
  refine acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_nil _))
  · exact acceptsIn_mono_of_subset (d1 := []) (fun _ member => (List.not_mem_nil member).elim) _ _
      (ActionId.fits_write q.action)
  · exact Canonical.fits q.input

instance instCanonical : Canonical (Query κ) where
  shape := shapeDoc κ
  toVal := write
  ofVal := guarded write raw
  ofVal_toVal q := guarded_toVal write raw q (raw_write q)
  ofVal_exact := guarded_exact
  fits := fits_write

/-- Queries file at kind `query`. -/
instance instContent : Content (Query κ) := ⟨.query⟩

end Query

/-! ## The result envelope -/

/-- A host action's answer to one query: the envelope's version, the query, and the output as the
raw value tree. -/
structure Answered (κ : Type) where
  version : Nat
  query : Ref (Query κ)
  output : Val
deriving Repr

namespace Answered

variable {κ : Type}

/-- A struct of the version, the query reference and the raw output. -/
def shapeDoc : ShapeDoc :=
  ⟨.struct "Answered" [("version", .nat), ("query", .ref .query), ("output", .value)], []⟩

/-- Constructor `0`; the output is embedded as is, so its references stay edges. -/
def write (a : Answered κ) : Val :=
  .ctor 0 [.nat a.version, .ref Kind.query.byte a.query.digest.bytes, a.output]

/-- The structural reader; `guarded` makes it exact. -/
def raw : Val → Option (Answered κ)
  | .ctor 0 [.nat version, .ref kind bytes, output] =>
    if kind = Kind.query.byte then
      (Digest.ofBytes? bytes).map fun digest => ⟨version, ⟨digest⟩, output⟩
    else none
  | _ => none

theorem raw_write (a : Answered κ) : raw (write a) = some a := by
  change (Digest.ofBytes? a.query.digest.bytes).map
    (fun digest => (⟨a.version, ⟨digest⟩, a.output⟩ : Answered κ)) = some a
  rw [Digest.ofBytes?_bytes]
  rfl

theorem fits_write (a : Answered κ) : shapeDoc.accepts (write a) = true := by
  simp only [shapeDoc, write, ShapeDoc.accepts, acceptsIn, candidates, List.any_cons,
    List.any_nil, Bool.or_false, acceptsAt, acceptsFields, a.query.digest.length_eq,
    decide_true, Bool.true_and]

instance instCanonical : Canonical (Answered κ) where
  shape := shapeDoc
  toVal := write
  ofVal := guarded write raw
  ofVal_toVal a := guarded_toVal write raw a (raw_write a)
  ofVal_exact := guarded_exact
  fits := fits_write

/-- Results file at kind `result`. -/
instance instContent : Content (Answered κ) := ⟨.result⟩

/-- Every result node carries the common specification, whatever its input carrier. -/
theorem specFor_eq (a : Answered κ) : specFor a = specOf (Answered Unit) := by
  unfold specFor
  rw [if_neg (fun h => nomatch h.1)]
  rfl

end Answered

/-! ## The designated query -/

/-- The designated query of a result node: its envelope read at node version 0, envelope version
0 and the common specification. Every other node answers `none`. The node check applies it to
every result node (`Store.checkResult`). -/
def Node.resultQuery? (node : Node) : Option Digest :=
  if node.kind = .result ∧ node.version = 0 ∧ node.spec = specOf (Answered Unit) then
    match ofVal (α := Answered Unit) node.payload with
    | some envelope => if envelope.version = 0 then some envelope.query.digest else none
    | none => none
  else none

/-- **The envelope reads exactly** (`cas-result-envelope`). A node answers a designated query
exactly when it is the node of a version-0 envelope of that query. Helper of
`cas-result-once`: admission consumes it to name a result's query. -/
theorem Node.resultQuery?_eq_some_iff {node : Node} {query : Digest} :
    node.resultQuery? = some query ↔
      ∃ output, node = nodeOf (⟨0, ⟨query⟩, output⟩ : Answered Unit) := by
  constructor
  · intro h
    unfold Node.resultQuery? at h
    split at h
    · next header =>
      obtain ⟨kind, version, spec⟩ := header
      cases read : ofVal (α := Answered Unit) node.payload with
      | none =>
        rw [read] at h
        exact nomatch h
      | some envelope =>
        rw [read] at h
        change (if envelope.version = 0 then some envelope.query.digest else none) = some query at h
        split at h
        · next zero =>
          injection h with same
          have payload : node.payload = Answered.write envelope := ofVal_exact read
          refine ⟨envelope.output, ?_⟩
          obtain ⟨v, k, s, p⟩ := node
          simp only at kind version spec payload
          subst kind version spec payload same
          obtain ⟨n, ⟨d⟩, out⟩ := envelope
          simp only at zero
          subst zero
          simp only [nodeOf, Answered.specFor_eq]
          rfl
        · exact nomatch h
    · exact nomatch h
  · rintro ⟨output, rfl⟩
    unfold Node.resultQuery?
    rw [if_pos ⟨rfl, rfl, Answered.specFor_eq (⟨0, ⟨query⟩, output⟩ : Answered Unit)⟩]
    simp only [nodeOf_payload, ofVal_toVal]
    rfl

/-- Only a result node answers a designated query. -/
theorem Node.resultQuery?_kind {node : Node} {query : Digest} (h : node.resultQuery? = some query) :
    node.kind = .result := by
  obtain ⟨output, rfl⟩ := Node.resultQuery?_eq_some_iff.mp h
  rfl

/-- Helper of `cas-result-once`: the designated query is a checked edge at kind `query`, so edge
admission resolves it before the envelope check. -/
theorem Node.resultQuery?_mem_checkedEdges {node : Node} {query : Digest}
    (h : node.resultQuery? = some query) : (⟨.query, query⟩ : AnyRef) ∈ node.checkedEdges := by
  obtain ⟨output, rfl⟩ := Node.resultQuery?_eq_some_iff.mp h
  apply Node.mem_checkedEdges_of_mem_refsOf
  simp only [Node.refsOf, nodeOf_payload]
  change (⟨.query, query⟩ : AnyRef) ∈ Val.refs (.ctor 0 [.nat 0, .ref Kind.query.byte query.bytes, output])
  simp only [Val.refs, Val.refsList, Kind.ofByte?_byte, Digest.ofBytes?_bytes,
    List.nil_append, List.cons_append, List.mem_cons, true_or]

end Effect4.Store
