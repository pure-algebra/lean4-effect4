import Effect4
import Tools.GeneratedStamp
import Test.Codegen.SchemaGenerationCoverage

/-!
# Seat S, question 5: row 8's dedupe at the emitter (option (C)), measured on a copy

Research probe, outside every root; nothing imports it. Row 8's option (C) (seat G's receipt,
recommended, the coordinator agreeing): keep `ShapeDoc.document`'s version-0 bytes (the store's
addresses are a frozen contract) and deduplicate the references table where it is written as a
JSON object, the emitter (`Codegen/Schema.lean:310-322`), with a located refusal for a repeated
key whose bodies differ.

* `dedupeRefs` keeps the first entry of each key, drops a later entry with an equal body, and
  refuses a later entry with a different body at `["references", key]`.
* Laws (proved): on a table whose keys are distinct it is the identity, so (C) changes no byte of
  any document without repeats; its output's keys are distinct.
* The checked emitter `documentExprChecked`/`multiDocumentExprChecked`/`moduleSyntaxChecked`
  wraps the production `Codegen.Schema` functions unchanged.
* Measurement: the three `harness/schema-generation/` fixtures, re-emitted through the checked
  emitter with their stamps (printed between markers, compared with `cmp` by the host script);
  the 19 shape documents with repeated keys (seat G's census), emitted with and without (C).
-/

set_option autoImplicit false

namespace SeatS.RefDedupe

open Effect4 Effect4.Store TypeScript

structure RefRefusal where
  path : List String
  reason : String
deriving DecidableEq

/-- Keep the first entry of each key; drop a later entry with an equal body; refuse a later entry
whose body differs, located at the repeated key. -/
def dedupeFrom (acc : List ReferenceEntry) : List ReferenceEntry → Except RefRefusal (List ReferenceEntry)
  | [] => .ok acc
  | e :: es =>
    match acc.find? (fun f => f.key == e.key) with
    | none => dedupeFrom (acc ++ [e]) es
    | some f =>
      if f.representation = e.representation then dedupeFrom acc es
      else .error ⟨["references", e.key], "a repeated reference key with a different body"⟩

def dedupeRefs (es : List ReferenceEntry) : Except RefRefusal (List ReferenceEntry) := dedupeFrom [] es

/-- The keys of a table are distinct. -/
def keysDistinct (es : List ReferenceEntry) : Prop := (es.map (·.key)).Nodup

theorem find?_none_of_not_mem {acc : List ReferenceEntry} {k : String}
    (h : k ∉ acc.map (·.key)) : acc.find? (fun f => f.key == k) = none := by
  rw [List.find?_eq_none]
  intro f hf hk
  apply h
  rw [List.mem_map]
  exact ⟨f, hf, (beq_iff_eq.mp hk)⟩

/-- **The identity on a table without repeats** (proved): (C) moves no byte of such a document. -/
theorem dedupeFrom_distinct (acc es : List ReferenceEntry)
    (h : ((acc ++ es).map (·.key)).Nodup) : dedupeFrom acc es = .ok (acc ++ es) := by
  induction es generalizing acc with
  | nil => simp only [dedupeFrom, List.append_nil]
  | cons e es ih =>
    have hnot : e.key ∉ acc.map (·.key) := by
      intro hm
      rw [List.map_append, List.map_cons] at h
      exact (List.nodup_append.mp h).2.2 e.key hm e.key List.mem_cons_self rfl
    simp only [dedupeFrom, find?_none_of_not_mem hnot]
    have h' : ((acc ++ [e]) ++ es).map (·.key) = (acc ++ e :: es).map (·.key) := by
      rw [List.append_assoc, List.singleton_append]
    rw [ih (acc ++ [e]) (h' ▸ h), List.append_assoc, List.singleton_append]

theorem dedupeRefs_distinct (es : List ReferenceEntry) (h : keysDistinct es) :
    dedupeRefs es = .ok es := by
  unfold dedupeRefs
  unfold keysDistinct at h
  rw [dedupeFrom_distinct [] es (by simpa only [List.nil_append] using h), List.nil_append]

/-- **Distinct keys out** (proved): whatever `dedupeRefs` answers has no repeated key. -/
theorem dedupeFrom_nodup (acc es : List ReferenceEntry) (hacc : keysDistinct acc)
    (out : List ReferenceEntry) (h : dedupeFrom acc es = .ok out) : keysDistinct out := by
  induction es generalizing acc with
  | nil =>
    simp only [dedupeFrom, Except.ok.injEq] at h
    exact h ▸ hacc
  | cons e es ih =>
    simp only [dedupeFrom] at h
    split at h
    · rename_i hnone
      apply ih (acc ++ [e]) _ h
      unfold keysDistinct
      rw [List.map_append, List.map_singleton]
      refine List.nodup_append.mpr ⟨hacc, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      rw [List.find?_eq_none] at hnone
      rw [List.mem_map] at ha
      obtain ⟨f, hf, hk⟩ := ha
      exact hnone f hf (beq_iff_eq.mpr (hk.trans hab))
    · split at h
      · exact ih acc hacc h
      · exact nomatch h

theorem dedupeRefs_nodup (es out : List ReferenceEntry) (h : dedupeRefs es = .ok out) :
    keysDistinct out :=
  dedupeFrom_nodup [] es List.nodup_nil out h

/-! ## The checked emitter: the production functions, the table deduplicated first -/

def documentExprChecked (d : Document) : Except RefRefusal Expr := do
  let refs ← dedupeRefs d.references
  .ok (Effect4.Codegen.Schema.documentExpr { d with references := refs })

def multiDocumentExprChecked (d : MultiDocument) : Except RefRefusal Expr := do
  let refs ← dedupeRefs d.references
  .ok (Effect4.Codegen.Schema.multiDocumentExpr { d with references := refs })

def moduleSyntaxChecked (name : String) (d : Document) (data : List (String × Json) := []) :
    Except RefRefusal Module := do
  let refs ← dedupeRefs d.references
  .ok (Effect4.Codegen.Schema.moduleSyntax name { d with references := refs } data)

theorem moduleSyntaxChecked_distinct (name : String) (d : Document) (data : List (String × Json))
    (h : keysDistinct d.references) :
    moduleSyntaxChecked name d data = .ok (Effect4.Codegen.Schema.moduleSyntax name d data) := by
  unfold moduleSyntaxChecked
  rw [dedupeRefs_distinct d.references h]
  rfl

/-! ## The three harness fixtures (the same inputs as `harness/schema-generation/Emit*.lean`) -/

private def person : Representation :=
  Schema.struct
    [ Schema.property "name"
        ((Schema.withCheck Schema.string Schema.Check.trimmed).getD Schema.string)
    , Schema.property "active" Schema.boolean ]
private def personDocument : Document := Schema.document person
private def multi : MultiDocument :=
  { representations := [Schema.string, Schema.boolean]
    references := [{ key := "shared", representation := Schema.number }] }
def coverageDocument : Document := Test.Codegen.SchemaGenerationCoverage.document

-- the three tables have distinct keys, so (C) is the identity on them (proved above, tested here)
#guard ((personDocument.references.map (·.key)).eraseDups.length == personDocument.references.length)
#guard ((coverageDocument.references.map (·.key)).eraseDups.length == coverageDocument.references.length)
#guard ((multi.references.map (·.key)).eraseDups.length == multi.references.length)
#guard coverageDocument.references.length == 23

def personFixture : Except RefRefusal String := do
  let m ← moduleSyntaxChecked "PersonSchema" personDocument
    [ ("ada", .obj [("name", .str "Ada"), ("active", .bool true)])
    , ("prototypeData", .obj [("__proto__", .str "data")]) ]
  .ok ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitFixture.lean" ++ "\n" ++
    Render.module house0 m)

def coverageFixture : Except RefRefusal String := do
  let m ← moduleSyntaxChecked "AllRepresentationsSchema" coverageDocument
  .ok ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitCoverageFixture.lean" ++ "\n" ++
    Render.module house0 m)

def multiFixture : Except RefRefusal String := do
  let e ← multiDocumentExprChecked multi
  .ok ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitMultiFixture.lean" ++ "\n" ++
    String.intercalate "\n"
      [ "/**", " * Generated by Effect4 Schema.", " *", " * Do not edit.", " */"
      , "import * as Schema from \"effect/Schema\"", ""
      , "/** Raw Effect Schema multi-root document. */"
      , "export const TwoRootsSchemaJson: Schema.Json = " ++ Render.expr house0 0 e, "" ])

/-! ## The shape documents with repeated keys (seat G's census: 19 of 88), with and without (C) -/

def repeatsOf (d : Document) : Nat := d.references.length - (d.references.map (·.key)).eraseDups.length

def shapeDocs : List (String × Document) :=
  [ ("Document", (shape Document).document), ("MultiDocument", (shape MultiDocument).document),
    ("Representation", (shape Representation).document), ("Check", (shape Check).document),
    ("ReferenceEntry", (shape ReferenceEntry).document), ("ShapeDoc", (shape ShapeDoc).document) ]

-- every repeat in these tables has an equal body, so (C) refuses none of them and drops the repeats
#guard shapeDocs.all fun d => match dedupeRefs d.2.references with
  | .ok out => out.length + repeatsOf d.2 == d.2.references.length
  | .error _ => false
#guard repeatsOf (shape Document).document == 22
-- a repeated key with a different body: the located refusal
def conflicting : List ReferenceEntry :=
  [⟨"A", Schema.string⟩, ⟨"B", Schema.boolean⟩, ⟨"A", Schema.number⟩]
#guard match dedupeRefs conflicting with
  | .error e => e == ⟨["references", "A"], "a repeated reference key with a different body"⟩
  | .ok _ => false
#guard match dedupeRefs [⟨"A", Schema.string⟩, ⟨"A", Schema.string⟩] with
  | .ok out => out == [⟨"A", Schema.string⟩]
  | .error _ => false

/-! ## Red controls: each claim is false, and `#guard_msgs` asserts its `#guard` fails -/

/-- RED: a repeated key with a different body deduplicates silently (the first body kept). -/
def red_conflictAccepted : Bool := match dedupeRefs conflicting with
  | .ok _ => true
  | .error _ => false
/--
error: Expression
  red_conflictAccepted
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_conflictAccepted

/-- RED: the meta-schema's table has distinct keys, so (C) has nothing to do there. -/
def red_metaDistinct : Bool := repeatsOf (shape Document).document == 0
/--
error: Expression
  red_metaDistinct
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_metaDistinct

/-! ## Output for the host comparison (`S/host/q5-dedupe.sh`) -/

#eval do
  let fixtures : List (String × Except RefRefusal String) := [("Person.generated.ts", personFixture),
      ("AllRepresentations.generated.ts", coverageFixture), ("TwoRoots.generated.ts", multiFixture)]
  for (name, f) in fixtures do
    match f with
    | Except.ok text => IO.println ("=====BEGIN " ++ name) *> IO.print text *> IO.println "=====END"
    | Except.error e => IO.println ("=====REFUSED " ++ name ++ " " ++ toString e.path)
  -- the meta-schema as a TypeScript module, without and with (C)
  let metaDoc := (shape Document).document
  IO.println ("=====BEGIN meta-raw.ts")
  IO.print (Render.module house0 (Effect4.Codegen.Schema.moduleSyntax "MetaSchema" metaDoc))
  IO.println "=====END"
  match moduleSyntaxChecked "MetaSchema" metaDoc with
  | Except.ok m => IO.println "=====BEGIN meta-deduped.ts" *> IO.print (Render.module house0 m) *> IO.println "=====END"
  | Except.error e => IO.println ("=====REFUSED meta-deduped.ts " ++ toString e.path)
  for (name, d) in shapeDocs do
    IO.println ("REPEATS " ++ name ++ " " ++ toString d.references.length ++ " entries, " ++
      toString (repeatsOf d) ++ " repeats")

end SeatS.RefDedupe

#print axioms SeatS.RefDedupe.find?_none_of_not_mem
#print axioms SeatS.RefDedupe.dedupeFrom_distinct
#print axioms SeatS.RefDedupe.dedupeRefs_distinct
#print axioms SeatS.RefDedupe.dedupeFrom_nodup
#print axioms SeatS.RefDedupe.dedupeRefs_nodup
#print axioms SeatS.RefDedupe.moduleSyntaxChecked_distinct
#print axioms SeatS.RefDedupe.dedupeRefs
#print axioms SeatS.RefDedupe.moduleSyntaxChecked
