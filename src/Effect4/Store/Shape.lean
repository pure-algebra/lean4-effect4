import Effect4.Schema.Authoring
import Effect4.Arch.JsonNumber
import Effect4.Store.Kind
import Effect4.Store.Digest

/-!
# Store.Shape

Owner: the shape language a canonical carrier describes itself in, the checker that says a
value tree fits a shape, and the two derivations the shape drives: the spec `Document` and the
JSON printer.

The alphabet is the facts note's Q5: `unit | bool | nat | string | bytes | digest | list |
option | pair | struct name fields | sum name cases | ref kind | anyRef | named n`, and a
`ShapeDoc {root, defs}` maps onto `Document {representation, references}`. One description,
several derivations: `ShapeDoc.accepts` is the `fits` checker of the class, `ShapeDoc.document`
the spec (the Q5 rendering table, fixed under version byte 0), `ShapeDoc.print` the printer
(the same table read the other way; hex lowercase, one printer).

`accepts` is structural on the value (`acceptsAt : Val → Shape → Bool`), so the fuel is the
value's own size. A `named n` shape is resolved through `defs`: `candidates` lists every
binding of `n`, and a value fits `named n` when it fits one of them. For a document with unique
names — every document the generator writes — that is the one binding; the reason the checker
is stated over all of them is `acceptsIn_mono`: acceptance survives appending definitions on
either side, which is what lets `Canonical (α × β)` prove `fits` with the two components'
tables appended, without a uniqueness side condition the class has no place for. A definition
whose body is itself `named` is one step away and accepts nothing.

The rendering table, `render`: `unit ↦ null`; `bool`, `string` as is; `nat ↦ number ∘
Check.int`; `bytes`, `digest ↦ string` with the hex pattern check; `list ↦ array`; `option s ↦
anyOf [s, null]`; `pair ↦ tuple`; `struct ↦ struct` in declaration order, never sorted,
annotated `identifier`; an all-nullary `sum ↦ anyOf` of string literals; any other `sum ↦
variant` (`_tag`); `ref kind ↦ string` with the hex check and the typed `ref = kind`
annotation; `anyRef ↦ struct [kind, address]`; `named ↦ reference`. A definition entry whose
shape is not already a named struct or sum is annotated with its key as `identifier`, so a
fixed-width scalar (`{root := named "UInt64", defs := [("UInt64", nat)]}`) renders as a
`number` with an identifier, as Q5 asks. The two annotation keys are restated here with the
shape of `src/Effect4/Surface/Annotate.lean:73-91` (`identifierKey`) and `:345-351`
(`markKey`), because that module sits above the store. The printer's number rule,
`Json.ofNat` over `binary64OfNat`, is `Effect4.Arch.JsonNumber`'s (`src/Effect4/Arch/JsonNumber.lean`,
namespace `Effect4.Arch`), the one JSON-number rule every printer of the tree reads.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64 Representation Document AnnotationKey Annotations ReferenceEntry
  PropertySignature)
open Effect4.Arch (Json.ofNat)

/-! ## The alphabet -/

/-- The shape of a canonical carrier: the Q5 alphabet. -/
inductive Shape where
  | unit
  | bool
  | nat
  | string
  | bytes
  /-- Thirty-two bytes. -/
  | digest
  | list (item : Shape)
  | option (item : Shape)
  | pair (fst snd : Shape)
  /-- A structure: constructor 0 with its fields in declaration order. -/
  | struct (name : String) (fields : List (String × Shape))
  /-- A sum: one case per constructor in declaration order, each with its fields. -/
  | sum (name : String) (cases : List (String × List (String × Shape)))
  /-- A reference that must resolve at one kind. -/
  | ref (kind : Kind)
  /-- A reference at any registered kind, carried with its kind byte. -/
  | anyRef
  /-- A shape defined in the document's table. -/
  | named (name : String)
deriving Inhabited

namespace Shape

/-! A structural `Repr`, by hand, for the same reason `Val`'s is (`Store/Val.lean`): the
derived one on a nested inductive is a `partial` definition the trust gate refuses. -/

mutual
/-- The shape as the Lean syntax that builds it. -/
def render : Shape → String
  | .unit => "Shape.unit"
  | .bool => "Shape.bool"
  | .nat => "Shape.nat"
  | .string => "Shape.string"
  | .bytes => "Shape.bytes"
  | .digest => "Shape.digest"
  | .list item => s!"(Shape.list {render item})"
  | .option item => s!"(Shape.option {render item})"
  | .pair a b => s!"(Shape.pair {render a} {render b})"
  | .struct name fields => s!"(Shape.struct {name.quote} [{", ".intercalate (renderFields fields)}])"
  | .sum name cases => s!"(Shape.sum {name.quote} [{", ".intercalate (renderCases cases)}])"
  | .ref k => s!"(Shape.ref .{k.name})"
  | .anyRef => "Shape.anyRef"
  | .named name => s!"(Shape.named {name.quote})"
def renderFields : List (String × Shape) → List String
  | [] => []
  | (n, s) :: rest => s!"({n.quote}, {render s})" :: renderFields rest
def renderCases : List (String × List (String × Shape)) → List String
  | [] => []
  | (n, fields) :: rest =>
    s!"({n.quote}, [{", ".intercalate (renderFields fields)}])" :: renderCases rest
end

instance instRepr : Repr Shape := ⟨fun s _ => Std.Format.text (render s)⟩

end Shape

/-- A root shape and the table its `named` shapes resolve in. -/
structure ShapeDoc where
  root : Shape
  defs : List (String × Shape)
deriving Repr, Inhabited

/-- Every binding of a name in a table, in table order. -/
def lookupAll (name : String) : List (String × Shape) → List Shape
  | [] => []
  | (n, s) :: rest => if n = name then s :: lookupAll name rest else lookupAll name rest

/-- The shapes a shape stands for: itself, or a `named` shape's bindings. -/
def candidates (defs : List (String × Shape)) : Shape → List Shape
  | .named n => lookupAll n defs
  | s => [s]

/-- Whether every case of a sum carries no field: the rule that renders it as string literals. -/
def allNullary (cases : List (String × List (String × Shape))) : Bool :=
  cases.all fun c => c.2.isEmpty

/-! ## The checker -/

mutual
/-- A value fits a resolved shape. Children are checked against the candidates of their own
shapes, so a `named` child resolves in the same table. -/
def acceptsAt (defs : List (String × Shape)) : Val → Shape → Bool
  | .unit, .unit => true
  | .bool _, .bool => true
  | .nat _, .nat => true
  | .str _, .string => true
  | .bytes _, .bytes => true
  | .bytes d, .digest => decide (d.length = 32)
  | .list xs, .list item => acceptsList defs item xs
  | .pair a b, .pair f g =>
    (candidates defs f).any (acceptsAt defs a) && (candidates defs g).any (acceptsAt defs b)
  | .none, .option _ => true
  | .some a, .option item => (candidates defs item).any (acceptsAt defs a)
  | .ctor i args, .struct _ fields => decide (i = 0) && acceptsFields defs fields args
  | .ctor i args, .sum _ cases =>
    match cases[i]? with
    | some (_, fields) => acceptsFields defs fields args
    | none => false
  | .ref b d, .ref k => decide (b = k.byte) && decide (d.length = 32)
  | .ref b d, .anyRef => (Kind.ofByte? b).isSome && decide (d.length = 32)
  | _, _ => false
/-- Every element fits the item shape. -/
def acceptsList (defs : List (String × Shape)) : Shape → List Val → Bool
  | _, [] => true
  | item, x :: xs => (candidates defs item).any (acceptsAt defs x) && acceptsList defs item xs
/-- Every argument fits its field's shape, and there are exactly as many. -/
def acceptsFields (defs : List (String × Shape)) : List (String × Shape) → List Val → Bool
  | [], [] => true
  | (_, s) :: fields, a :: args =>
    (candidates defs s).any (acceptsAt defs a) && acceptsFields defs fields args
  | _, _ => false
end

/-- A value fits a shape in a table: it fits one of the shape's candidates. -/
def acceptsIn (defs : List (String × Shape)) (s : Shape) (v : Val) : Bool :=
  (candidates defs s).any (acceptsAt defs v)

/-- The `fits` checker of the class: the value fits the root in the document's table. -/
def ShapeDoc.accepts (doc : ShapeDoc) (v : Val) : Bool := acceptsIn doc.defs doc.root v

/-! ## Monotonicity in the table -/

theorem lookupAll_append (name : String) (d1 d2 : List (String × Shape)) :
    lookupAll name (d1 ++ d2) = lookupAll name d1 ++ lookupAll name d2 := by
  induction d1 with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨n, s⟩ := p
    simp only [List.cons_append, lookupAll]
    split <;> simp [ih]

theorem mem_candidates_append_right {defs more : List (String × Shape)} {s s' : Shape}
    (h : s' ∈ candidates defs s) : s' ∈ candidates (defs ++ more) s := by
  cases s
  case named n =>
    simp only [candidates, lookupAll_append, List.mem_append]
    exact Or.inl h
  all_goals exact h

theorem mem_candidates_append_left {defs more : List (String × Shape)} {s s' : Shape}
    (h : s' ∈ candidates defs s) : s' ∈ candidates (more ++ defs) s := by
  cases s
  case named n =>
    simp only [candidates, lookupAll_append, List.mem_append]
    exact Or.inr h
  all_goals exact h

/-- Lifting one child's monotonicity through its candidates. -/
theorem any_mono {defs defs' : List (String × Shape)}
    (hsub : ∀ s s', s' ∈ candidates defs s → s' ∈ candidates defs' s) {a : Val}
    (ih : ∀ s', acceptsAt defs a s' = true → acceptsAt defs' a s' = true) {f : Shape}
    (h : (candidates defs f).any (acceptsAt defs a) = true) :
    (candidates defs' f).any (acceptsAt defs' a) = true := by
  rw [List.any_eq_true] at h ⊢
  obtain ⟨s', hs', hp⟩ := h
  exact ⟨s', hsub f s' hs', ih s' hp⟩

mutual
theorem acceptsAt_mono {defs defs' : List (String × Shape)}
    (hsub : ∀ s s', s' ∈ candidates defs s → s' ∈ candidates defs' s) :
    ∀ (v : Val) (s' : Shape), acceptsAt defs v s' = true → acceptsAt defs' v s' = true
  | .unit, s', h => by
    cases s'
    case unit => rfl
    all_goals simp [acceptsAt] at h
  | .bool b, s', h => by
    cases s'
    case bool => rfl
    all_goals simp [acceptsAt] at h
  | .nat n, s', h => by
    cases s'
    case nat => rfl
    all_goals simp [acceptsAt] at h
  | .str s, s', h => by
    cases s'
    case string => rfl
    all_goals simp [acceptsAt] at h
  | .bytes d, s', h => by
    cases s'
    case bytes => rfl
    case digest => exact h
    all_goals simp [acceptsAt] at h
  | .list xs, s', h => by
    cases s'
    case list item =>
      simp only [acceptsAt] at h ⊢
      exact acceptsList_mono hsub item xs h
    all_goals simp [acceptsAt] at h
  | .pair a b, s', h => by
    cases s'
    case pair f g =>
      simp only [acceptsAt, Bool.and_eq_true] at h ⊢
      exact ⟨any_mono hsub (acceptsAt_mono hsub a) h.1, any_mono hsub (acceptsAt_mono hsub b) h.2⟩
    all_goals simp [acceptsAt] at h
  | .none, s', h => by
    cases s'
    case option item => rfl
    all_goals simp [acceptsAt] at h
  | .some a, s', h => by
    cases s'
    case option item =>
      simp only [acceptsAt] at h ⊢
      exact any_mono hsub (acceptsAt_mono hsub a) h
    all_goals simp [acceptsAt] at h
  | .ctor i args, s', h => by
    cases s'
    case struct name fields =>
      simp only [acceptsAt, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, acceptsFields_mono hsub fields args h.2⟩
    case sum name cases =>
      simp only [acceptsAt] at h ⊢
      split at h
      · next _ fields hf =>
        try rw [hf]
        exact acceptsFields_mono hsub fields args h
      · exact nomatch h
    all_goals simp [acceptsAt] at h
  | .ref b d, s', h => by
    cases s'
    case ref k => exact h
    case anyRef => exact h
    all_goals simp [acceptsAt] at h
theorem acceptsList_mono {defs defs' : List (String × Shape)}
    (hsub : ∀ s s', s' ∈ candidates defs s → s' ∈ candidates defs' s) :
    ∀ (item : Shape) (xs : List Val), acceptsList defs item xs = true → acceptsList defs' item xs = true
  | _, [], _ => rfl
  | item, x :: xs, h => by
    simp only [acceptsList, Bool.and_eq_true] at h ⊢
    exact ⟨any_mono hsub (acceptsAt_mono hsub x) h.1, acceptsList_mono hsub item xs h.2⟩
theorem acceptsFields_mono {defs defs' : List (String × Shape)}
    (hsub : ∀ s s', s' ∈ candidates defs s → s' ∈ candidates defs' s) :
    ∀ (fields : List (String × Shape)) (args : List Val),
      acceptsFields defs fields args = true → acceptsFields defs' fields args = true
  | [], [], _ => rfl
  | (_, s) :: fields, a :: args, h => by
    simp only [acceptsFields, Bool.and_eq_true] at h ⊢
    exact ⟨any_mono hsub (acceptsAt_mono hsub a) h.1, acceptsFields_mono hsub fields args h.2⟩
  | [], _ :: _, h => by simp [acceptsFields] at h
  | _ :: _, [], h => by simp [acceptsFields] at h
end

theorem acceptsIn_mono {defs defs' : List (String × Shape)}
    (hsub : ∀ s s', s' ∈ candidates defs s → s' ∈ candidates defs' s) (s : Shape) (v : Val)
    (h : acceptsIn defs s v = true) : acceptsIn defs' s v = true :=
  any_mono hsub (acceptsAt_mono hsub v) h

/-- Acceptance survives definitions appended after the table. -/
theorem acceptsIn_append_right (defs more : List (String × Shape)) (s : Shape) (v : Val)
    (h : acceptsIn defs s v = true) : acceptsIn (defs ++ more) s v = true :=
  acceptsIn_mono (fun _ _ hm => mem_candidates_append_right hm) s v h

/-- Acceptance survives definitions prepended before the table. -/
theorem acceptsIn_append_left (defs more : List (String × Shape)) (s : Shape) (v : Val)
    (h : acceptsIn defs s v = true) : acceptsIn (more ++ defs) s v = true :=
  acceptsIn_mono (fun _ _ hm => mem_candidates_append_left hm) s v h

/-- A shape that is not `named` is its own one candidate. -/
theorem candidates_of_not_named (defs : List (String × Shape)) (s : Shape)
    (h : ∀ n, s ≠ .named n) : candidates defs s = [s] := by
  cases s
  case named n => exact absurd rfl (h n)
  all_goals rfl

/-- Fitting a shape that is not `named` is fitting it directly. -/
theorem acceptsIn_of_not_named (defs : List (String × Shape)) (s : Shape) (v : Val)
    (h : ∀ n, s ≠ .named n) : acceptsIn defs s v = acceptsAt defs v s := by
  unfold acceptsIn
  rw [candidates_of_not_named defs s h]
  simp

/-! ## The annotation keys -/

/-- rc.112's `identifier`: the shape of `Surface/Annotate.lean:73-91`, restated. -/
def identifierKey : AnnotationKey String where
  name := "identifier"
  encode := Json.str
  decode := fun raw => match raw with
    | .str value => some value
    | _ => none

theorem identifierKey_lawful : identifierKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw <;> simp [identifierKey] at decoded ⊢
    exact decoded.symm

/-- The `ref = kind` key: which kind a reference must resolve at, as the kind's name. -/
def refKey : AnnotationKey Kind where
  name := "effect4/ref"
  encode := fun k => Json.str k.name
  decode := fun raw => match raw with
    | .str value => Kind.ofName? value
    | _ => none

theorem refKey_lawful : refKey.Lawful := by
  constructor
  · intro k
    exact Kind.ofName?_name k
  · intro raw k decoded
    cases raw <;> simp [refKey] at decoded ⊢
    exact Kind.name_ofName? decoded

/-! ## The spec: `ShapeDoc.document` -/

/-- The pattern of a byte string in lowercase hex. -/
def hexPattern : String := "^([0-9a-f]{2})*$"

/-- The pattern of a thirty-two-byte digest in lowercase hex. -/
def digestPattern : String := "^[0-9a-f]{64}$"

mutual
/-- The Q5 rendering table. -/
def render : Shape → Representation
  | .unit => Schema.null
  | .bool => Schema.boolean
  | .nat => .number none [Schema.Check.int]
  | .string => Schema.string
  | .bytes => .string none [Schema.Check.pattern hexPattern]
  | .digest => .string none [Schema.Check.pattern digestPattern]
  | .list item => Schema.array (render item)
  | .option item => Schema.anyOf (render item) [Schema.null]
  | .pair f s => Schema.tuple [Schema.element (render f), Schema.element (render s)]
  | .struct name fields => .objects (identifierKey.singleton name) [] (renderFields fields) []
  | .sum name cases =>
    if allNullary cases then
      .union (identifierKey.singleton name) [] (cases.map fun c => Schema.literalString c.1) .anyOf
    else .union (identifierKey.singleton name) [] (renderCases cases) .anyOf
  | .ref k => .string (refKey.singleton k) [Schema.Check.pattern digestPattern]
  | .anyRef =>
    Schema.struct
      [ Schema.property "kind" Schema.string
      , Schema.property "address" (.string none [Schema.Check.pattern digestPattern]) ]
  | .named n => Schema.reference n
/-- The properties of a struct, in declaration order. -/
def renderFields : List (String × Shape) → List PropertySignature
  | [] => []
  | (n, s) :: fields => Schema.property n (render s) :: renderFields fields
/-- The tagged structs of a sum with arguments, in declaration order. -/
def renderCases : List (String × List (String × Shape)) → List Representation
  | [] => []
  | (n, fields) :: cases => Schema.tagged n (renderFields fields) :: renderCases cases
end

/-- Give a rendered definition its key as `identifier`, unless it carries one already (a named
struct or sum does). -/
def renderDef (name : String) (s : Shape) : Representation :=
  match s with
  | .struct _ _ => render s
  | .sum _ _ => render s
  | _ =>
    match Representation.nodeAnnotations.preview (render s) with
    | some bag => Representation.nodeAnnotations.replace (identifierKey.append name bag) (render s)
    | none => render s

/-- The spec of a shape document: the root rendered, the table as the references. -/
def ShapeDoc.document (doc : ShapeDoc) : Document :=
  { representation := render doc.root
    references := doc.defs.map fun d => ⟨d.1, renderDef d.1 d.2⟩ }

/-! ## The printer: `ShapeDoc.print` -/

/-- The lowercase hex string of a byte string. -/
def hexString (bs : Bytes) : String := String.ofList (hexOfBytes bs)

/-- The first candidate of a shape, or the shape itself when it has none. -/
def headShape (defs : List (String × Shape)) (s : Shape) : Shape :=
  match candidates defs s with
  | s' :: _ => s'
  | [] => s

/-- A kind byte's name for the printer; an unregistered byte prints as `null`. -/
def kindJson (b : UInt8) : Json :=
  match Kind.ofByte? b with
  | some k => .str k.name
  | none => .null

mutual
/-- The printer: the Q5 table read from the value's side. The shape supplies the names (fields,
cases, kinds) and the value supplies the structure, so a value that does not fit still prints,
by structure, under `_ctor`/`args`. -/
def printIn (defs : List (String × Shape)) : Shape → Val → Json
  | _, .unit => .null
  | _, .bool b => .bool b
  | _, .nat n => Json.ofNat n
  | _, .str s => .str s
  | _, .bytes d => .str (hexString d)
  | _, .none => .null
  | s, .some a =>
    match headShape defs s with
    | .option item => printIn defs item a
    | _ => printIn defs .unit a
  | s, .list xs =>
    match headShape defs s with
    | .list item => .arr (printList defs item xs)
    | _ => .arr (printList defs .unit xs)
  | s, .pair a b =>
    match headShape defs s with
    | .pair f g => .arr [printIn defs f a, printIn defs g b]
    | _ => .arr [printIn defs .unit a, printIn defs .unit b]
  | s, .ctor i args =>
    match headShape defs s with
    | .struct _ fields => .obj (printFields defs fields args)
    | .sum _ cases =>
      match cases[i]? with
      | some (name, fields) =>
        if allNullary cases then .str name
        else .obj (("_tag", .str name) :: printFields defs fields args)
      | none => .obj [("_ctor", Json.ofNat i), ("args", .arr (printList defs .unit args))]
    | _ => .obj [("_ctor", Json.ofNat i), ("args", .arr (printList defs .unit args))]
  | s, .ref k d =>
    match headShape defs s with
    | .anyRef => .obj [("kind", kindJson k), ("address", .str (hexString d))]
    | _ => .str (hexString d)
/-- The elements of a list, each under the item shape. -/
def printList (defs : List (String × Shape)) : Shape → List Val → List Json
  | _, [] => []
  | item, x :: xs => printIn defs item x :: printList defs item xs
/-- The fields of a struct or case, named in declaration order. -/
def printFields (defs : List (String × Shape)) : List (String × Shape) → List Val → List (String × Json)
  | (n, s) :: fields, a :: args => (n, printIn defs s a) :: printFields defs fields args
  | _, _ => []
end

/-- The printer of a shape document: the value under the root, names from the table. -/
def ShapeDoc.print (doc : ShapeDoc) (v : Val) : Json := printIn doc.defs doc.root v

/-! ## The census entry, guarded: the shape of `StdLib/Entry.lean:23-49` -/

/-- The document of the census entry, as the generator would write it. -/
def entryDoc : ShapeDoc :=
  { root := .struct "Entry"
      [("module", .string), ("name", .string), ("kind", .named "ExportKind"), ("line", .nat)]
    defs := [("ExportKind", .sum "ExportKind"
      [("const", []), ("function", []), ("class_", []), ("interface", []), ("type", []),
       ("namespace_", [])])] }

#guard entryDoc.accepts sampleEntry = true
#guard entryDoc.accepts (.ctor 0 [.str "Effect", .str "gen", .ctor 6 [], .nat 1947]) = false
#guard entryDoc.accepts (.ctor 0 [.str "Effect", .str "gen", .ctor 0 []]) = false
#guard entryDoc.accepts (.ctor 1 [.str "Effect", .str "gen", .ctor 0 [], .nat 1947]) = false
#guard entryDoc.accepts (.ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .str "1947"]) = false
#guard entryDoc.print sampleEntry =
  .obj [("module", .str "Effect"), ("name", .str "gen"), ("kind", .str "const"),
    ("line", Json.ofNat 1947)]
#guard (ShapeDoc.mk (.ref .«export») []).accepts (.ref 2 (List.replicate 32 0)) = true
#guard (ShapeDoc.mk (.ref .«export») []).accepts (.ref 1 (List.replicate 32 0)) = false
#guard (ShapeDoc.mk (.ref .«export») []).accepts (.ref 2 (List.replicate 31 0)) = false
#guard (ShapeDoc.mk .anyRef []).accepts (.ref 15 (List.replicate 32 0)) = true
#guard (ShapeDoc.mk .anyRef []).accepts (.ref 16 (List.replicate 32 0)) = false
#guard (ShapeDoc.mk .anyRef []).print (.ref 2 (List.replicate 32 0)) =
  .obj [("kind", .str "export"), ("address", .str (String.ofList (List.replicate 64 '0')))]
#guard (ShapeDoc.mk .digest []).accepts (.bytes (List.replicate 32 0)) = true
#guard (ShapeDoc.mk .digest []).accepts (.bytes (List.replicate 33 0)) = false
#guard (ShapeDoc.mk (.option .nat) []).accepts .none = true
#guard (ShapeDoc.mk (.option .nat) []).accepts (.some (.nat 3)) = true
#guard (ShapeDoc.mk (.option .nat) []).accepts (.some (.bool true)) = false
#guard (ShapeDoc.mk (.named "X") [("X", .named "Y"), ("Y", .nat)]).accepts (.nat 1) = false
#guard entryDoc.document.references.length = 1
#guard (entryDoc.document.representation).tag = .objects
#guard (render (.sum "ExportKind" [("const", []), ("function", [])])).tag = .union
#guard (render .nat).tag = .number

/-! ## Receipts -/

#print axioms lookupAll
#print axioms candidates
#print axioms acceptsAt
#print axioms acceptsIn
#print axioms ShapeDoc.accepts
#print axioms lookupAll_append
#print axioms mem_candidates_append_right
#print axioms mem_candidates_append_left
#print axioms any_mono
#print axioms acceptsAt_mono
#print axioms acceptsIn_mono
#print axioms acceptsIn_append_right
#print axioms acceptsIn_append_left
#print axioms acceptsIn_of_not_named
#print axioms identifierKey
#print axioms identifierKey_lawful
#print axioms refKey
#print axioms refKey_lawful
#print axioms render
#print axioms renderDef
#print axioms ShapeDoc.document
#print axioms hexString
#print axioms printIn
#print axioms ShapeDoc.print

end Effect4.Store
