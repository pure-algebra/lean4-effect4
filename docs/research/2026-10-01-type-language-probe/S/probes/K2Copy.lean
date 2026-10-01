import Effect4.Laws.Schema.Codec
import Effect4.Schema.Bridge
import Effect4.Schema.Fold
import Effect4.Schema.OfShape

/-!
# Seat S, type-language probe (2026-10-01), question 1: the K2 arms per form, on a copy

Research probe, outside every root; nothing imports it. A copy of `Ty` with the forms the data
wave adds (`PTy`), and copies of `Schema/Bridge.lean`'s `schema`/`ofSchema` and
`Schema/Codec.lean`'s arms with their laws (`Laws/Schema/Codec.lean`), each new or changed line
under a `-- [arm:<form>]` or `-- [change:<what>]` marker so `S/probes/count-arms.py` measures the
lines a landing would touch.

The copy's shape (coordinated with seat P's brief, not with its files): the twenty production
constructors in their order, then `record (fields : List (String × PTy))` (row 119's constructor
text), then `optKey (inner : PTy)` (stage 4's field modifier, legal only as a record field's
type: the record constructor's text stays row 119's), then `map (key value : PTy)` (row 125).
Tagged unions are unions of records (stage 2: no constructor). `int` is inhabited by `Int`'s
generated image (`Store/Domain/Canonical.lean:359-368`; stage 5 with row 121). Seat T's census
(merged at main `8036f0b4`, its §2.1) adds, with its constructor texts: `tuple (items : List PTy)`
(normalized to `prod` at arity 2), `app (name : String) (args : List PTy)` (a nominal reference:
a declaration with type parameters), and the leaves `null`, `undefined`, `number` (binary64, if
row 121 rules it) and `bytes`.

Value encoding assumed here (seat P owns it): a record is `ctor 0 [list names, list slots]`, both
in the canonical order by name (probe R's row 165, recommended over row 119's positional
`ctor 0 slots`, which this file keeps only as a red control); an optional field's slot is `none`
(absent) or `some v`;
a map is a list of `[key, value]` pairs ascending by key, keys distinct; an `int` is `ctor 0 [nat n]`
(`Int.ofNat n`) or `ctor 1 [nat n]` (`Int.negSucc n`).
-/

set_option autoImplicit false

namespace SeatS.K2

open Effect4 Effect4.Program Effect4.Machine

/-! ## §1 The copy of the type language -/

inductive PTy where
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : PTy)
  | list (inner : PTy)
  | prod (left right : PTy)
  | except (error value : PTy)
  | exitOf (value error : PTy)
  | causeOf (error : PTy)
  | fiberOf (value error : PTy)
  | union (left right : PTy)
  | lit (value : String)
  | refOf (value : PTy)
  | deferredOf (value error : PTy)
  | var (index : Nat)
  | unknown
  -- [arm:record]
  | record (fields : List (String × PTy))
  -- [arm:optKey]
  | optKey (inner : PTy)
  -- [arm:map]
  | map (key value : PTy)
  -- [arm:tuple]
  | tuple (items : List PTy)
  -- [arm:app]
  | app (name : String) (args : List PTy)
  -- [arm:null]
  | null
  -- [arm:undefined]
  | undefined
  -- [arm:number]
  | number
  -- [arm:bytes]
  | bytes

instance : Inhabited PTy := ⟨.never⟩

/-- The single-motive eliminator (the `Store.Val.ind`/`Json.ind` idiom; seat Q generates it). -/
theorem PTy.ind' {motive : PTy → Prop}
    (never : motive .never) (unit : motive .unit) (nat : motive .nat) (int : motive .int)
    (string : motive .string) (bool : motive .bool) (handle : ∀ s, motive (.handle s))
    (option : ∀ t, motive t → motive (.option t)) (list : ∀ t, motive t → motive (.list t))
    (prod : ∀ a b, motive a → motive b → motive (.prod a b))
    (except : ∀ a b, motive a → motive b → motive (.except a b))
    (exitOf : ∀ a b, motive a → motive b → motive (.exitOf a b))
    (causeOf : ∀ t, motive t → motive (.causeOf t))
    (fiberOf : ∀ a b, motive a → motive b → motive (.fiberOf a b))
    (union : ∀ a b, motive a → motive b → motive (.union a b))
    (lit : ∀ s, motive (.lit s)) (refOf : ∀ t, motive t → motive (.refOf t))
    (deferredOf : ∀ a b, motive a → motive b → motive (.deferredOf a b))
    (var : ∀ i, motive (.var i)) (unknown : motive .unknown)
    (record : ∀ fs, (∀ p ∈ fs, motive p.2) → motive (.record fs))
    (optKey : ∀ t, motive t → motive (.optKey t))
    (map : ∀ k v, motive k → motive v → motive (.map k v))
    (tuple : ∀ ts, (∀ t ∈ ts, motive t) → motive (.tuple ts))
    (app : ∀ n ts, (∀ t ∈ ts, motive t) → motive (.app n ts))
    (null : motive .null) (undefined : motive .undefined) (number : motive .number)
    (bytes : motive .bytes) : ∀ t, motive t :=
  fun t =>
    PTy.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2)
      (motive_3 := fun ts => ∀ t ∈ ts, motive t) (motive_4 := fun p => motive p.2)
      never unit nat int string bool handle option list prod except exitOf causeOf fiberOf
      union lit refOf deferredOf var unknown record optKey map tuple app null undefined
      number bytes
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (fun _ _ ih => ih)
      t

mutual
/-- A computational equality for the guards (seat Q generates the real one with its iff). -/
def PTy.beq : PTy → PTy → Bool
  | .never, .never | .unit, .unit | .nat, .nat | .int, .int | .string, .string
  | .bool, .bool | .unknown, .unknown | .null, .null | .undefined, .undefined
  | .number, .number | .bytes, .bytes => true
  | .handle a, .handle b | .lit a, .lit b => a == b
  | .var i, .var j => i == j
  | .option a, .option b | .list a, .list b | .causeOf a, .causeOf b
  | .refOf a, .refOf b | .optKey a, .optKey b => PTy.beq a b
  | .prod a b, .prod c d | .except a b, .except c d | .exitOf a b, .exitOf c d
  | .fiberOf a b, .fiberOf c d | .union a b, .union c d | .deferredOf a b, .deferredOf c d
  | .map a b, .map c d => PTy.beq a c && PTy.beq b d
  | .record fs, .record gs => PTy.beqFields fs gs
  | .tuple xs, .tuple ys => PTy.beqList xs ys
  | .app n xs, .app m ys => n == m && PTy.beqList xs ys
  | _, _ => false
def PTy.beqList : List PTy → List PTy → Bool
  | [], [] => true
  | t :: ts, u :: us => PTy.beq t u && PTy.beqList ts us
  | _, _ => false
def PTy.beqFields : List (String × PTy) → List (String × PTy) → Bool
  | [], [] => true
  | (n, t) :: fs, (m, u) :: gs => n == m && PTy.beq t u && PTy.beqFields fs gs
  | _, _ => false
end

instance : BEq PTy := ⟨PTy.beq⟩

/-! ## §2 The field order: UTF-8 bytes through `Ty.ltKey` (Codex's `byteBefore`) -/

/-- Field names compare by their UTF-8 bytes, the order `Ty.key` already uses for literals. -/
def nameLt (a b : String) : Bool := Ty.ltKey (Ty.key (.lit a)) (Ty.key (.lit b))

theorem nameLt_irrefl (a : String) : nameLt a a = false := by
  cases h : nameLt a a with
  | false => rfl
  | true => exact absurd h (Ty.lt_irrefl (.lit a))

theorem nameLt_trans {a b c : String} (hab : nameLt a b = true) (hbc : nameLt b c = true) :
    nameLt a c = true :=
  Ty.lt_trans (a := .lit a) (b := .lit b) (c := .lit c) hab hbc

theorem nameLt_total (a b : String) : nameLt a b = true ∨ a = b ∨ nameLt b a = true := by
  rcases Ty.lt_trichotomy (.lit a) (.lit b) with h | h | h
  · exact Or.inl h
  · injection h with h
    exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Insert by name; an equal name already present wins (a left fold keeps the first). -/
def insF {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs =>
    if nameLt p.1 q.1 = true then p :: q :: qs
    else if p.1 = q.1 then q :: qs
    else q :: insF p qs

/-- The canonical field order (row 119): ascending by name bytes, the first of a repeat kept. -/
def canonF {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc p => insF p acc) []

/-- Strictly ascending by name. -/
def SortedF {α : Type} (l : List (String × α)) : Prop :=
  l.Pairwise (fun a b => nameLt a.1 b.1 = true)

theorem insF_last {α : Type} (p : String × α) (l : List (String × α))
    (h : ∀ q ∈ l, nameLt q.1 p.1 = true) : insF p l = l ++ [p] := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    have hq : nameLt q.1 p.1 = true := h q List.mem_cons_self
    have h1 : ¬ nameLt p.1 q.1 = true := by
      intro hpq
      have := nameLt_trans hpq hq
      rw [nameLt_irrefl] at this
      exact Bool.false_ne_true this
    have h2 : ¬ p.1 = q.1 := by
      intro he
      rw [he, nameLt_irrefl] at hq
      exact Bool.false_ne_true hq
    simp only [insF, if_neg h1, if_neg h2, List.cons_append]
    rw [ih (fun r hr => h r (List.mem_cons_of_mem q hr))]

theorem foldl_insF_of_sorted {α : Type} (xs acc : List (String × α))
    (h : SortedF (acc ++ xs)) : xs.foldl (fun a p => insF p a) acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    have hx : ∀ q ∈ acc, nameLt q.1 x.1 = true := fun q hq =>
      (List.pairwise_append.mp h).2.2 q hq x List.mem_cons_self
    simp only [List.foldl_cons]
    rw [insF_last x acc hx]
    have h' : SortedF ((acc ++ [x]) ++ xs) := by
      rw [List.append_assoc, List.singleton_append]
      exact h
    rw [ih (acc ++ [x]) h', List.append_assoc, List.singleton_append]

/-- **Static layout preparation, the Schema side** (the review's bound): on a field list already
in canonical order the sort is the identity, so an arm that sorts and an arm prepared once agree. -/
theorem canonF_of_sorted {α : Type} (l : List (String × α)) (h : SortedF l) : canonF l = l :=
  foldl_insF_of_sorted l [] (by simpa only [List.nil_append] using h)

theorem insF_map {α β : Type} (f : α → β) (p : String × α) (l : List (String × α)) :
    insF (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) =
      (insF p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [List.map_cons, insF, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp only [List.map_cons, insF, if_neg h1, if_pos h2]
      · simp only [List.map_cons, insF, if_neg h1, if_neg h2, ih]

/-- Sorting is by name only: it commutes with a map of the payloads (revision 5's
`sortFields_mapPayload`, here for the deduplicating sort). -/
theorem canonF_map {α β : Type} (f : α → β) (xs : List (String × α)) :
    canonF (xs.map (fun q => (q.1, f q.2))) = (canonF xs).map (fun q => (q.1, f q.2)) := by
  unfold canonF
  suffices ∀ acc : List (String × α),
      (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => insF p a)
          (acc.map (fun q => (q.1, f q.2))) =
        (xs.foldl (fun a p => insF p a) acc).map (fun q => (q.1, f q.2)) from this []
  induction xs with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [insF_map f x acc]
    exact ih (insF x acc)

/-! ## §3 Formation: closed, and the Schema side's well-formedness -/

mutual
def PTy.closed : PTy → Bool
  | .var _ => false
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _
  | .null | .undefined | .number | .bytes => true
  | .option t | .list t | .causeOf t | .refOf t | .optKey t => PTy.closed t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b
  | .map a b => PTy.closed a && PTy.closed b
  | .record fs => PTy.closedFields fs
  | .tuple ts | .app _ ts => PTy.closedList ts
def PTy.closedFields : List (String × PTy) → Bool
  | [] => true
  | (_, t) :: fs => PTy.closed t && PTy.closedFields fs
def PTy.closedList : List PTy → Bool
  | [] => true
  | t :: ts => PTy.closed t && PTy.closedList ts
end

/-- Distinct field names, by the first repeat (`repeatedField at`). -/
def firstRepeat {α : Type} : List (String × α) → List String → Option String
  | [], _ => none
  | (n, _) :: fs, seen => if seen.contains n then some n else firstRepeat fs (n :: seen)

/-- The declaration ids the reader maps to other constructors: an `app` may not take one, and
`bytes` takes `Uint8Array` from `handle` as the `var` repair takes `TypeParameter`. -/
-- [arm:app]
def reservedId (id : String) : Bool :=
  ["effect/schema/Option", "effect/schema/Ref", "effect/schema/Result", "effect/schema/Fiber",
   "effect/schema/Deferred", "effect/schema/Cause", "effect/schema/Exit",
   "effect/schema/TypeParameter", "effect/schema/Uint8Array"].contains id

mutual
/-- The formation rules the Schema arms rely on: a record's names are distinct; an optional key
is a record field's type and nothing else; a map is keyed by `string` (an index signature over
`Schema.String`; a literal-keyed `Record` is a record, question 2 E6). -/
def PTy.wf : PTy → Bool
  | .optKey _ => false
  -- the `var` repair (row 128) costs one handle name: `TypeParameter` is the template's image
  | .handle s => !(s = "effect/schema/TypeParameter") && !(s = "effect/schema/Uint8Array")
  -- [arm:tuple] arity two is `prod` (seat T's normal form)
  | .tuple ts => !(ts.length = 2) && PTy.wfList ts
  -- [arm:app] `app t []` is `handle t` (seat T's normal form)
  | .app n ts => !ts.isEmpty && !reservedId n && PTy.wfList ts
  | .record fs => (firstRepeat fs []).isNone && PTy.wfFields fs
  | .map .string v => PTy.wf v
  | .map _ _ => false
  | .option t | .list t | .causeOf t | .refOf t => PTy.wf t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b =>
    PTy.wf a && PTy.wf b
  | _ => true
def PTy.wfFields : List (String × PTy) → Bool
  | [] => true
  | (_, t) :: fs => (match t with | .optKey u => PTy.wf u | t' => PTy.wf t') && PTy.wfFields fs
def PTy.wfList : List PTy → Bool
  | [] => true
  | t :: ts => PTy.wf t && PTy.wfList ts
end

/-! ## §4 `Schema/Bridge.lean`, copied: `schema` and the located `ofSchema` -/

mutual
/-- The writer. Production text except the three new arms; a record's fields are written in the
type's own order (callers pass `normalize`d types, whose fields are canonical). -/
def schema : PTy → Representation
  | .never => Schema.never
  | .unknown => .unknown none []
  | .unit => Schema.void
  | .nat => .number none [Effect4.Schema.Bridge.isIntCheck, Effect4.Schema.Bridge.nonNegativeCheck]
  | .int => .number none [Effect4.Schema.Bridge.isIntCheck]
  | .string => Schema.string
  | .bool => Schema.boolean
  | .lit s => Schema.literalString s
  | .handle target => .declaration ⟨target, .null⟩ none [] []
  | .option inner => .declaration ⟨"effect/schema/Option", .null⟩ none [schema inner] []
  | .list inner => Schema.array (schema inner)
  | .prod left right => Schema.tuple [Schema.element (schema left), Schema.element (schema right)]
  | .except error value =>
    .declaration ⟨"effect/schema/Result", .null⟩ none [schema value, schema error] []
  | .exitOf value error =>
    .declaration ⟨"effect/schema/Exit", .null⟩ none [schema value, schema error, Effect4.Schema.Bridge.defectRep] []
  | .causeOf error =>
    .declaration ⟨"effect/schema/Cause", .null⟩ none [schema error, Effect4.Schema.Bridge.defectRep] []
  | .fiberOf value error =>
    .declaration ⟨"effect/schema/Fiber", .null⟩ none [schema value, schema error] []
  | .refOf value => .declaration ⟨"effect/schema/Ref", .null⟩ none [schema value] []
  | .deferredOf value error =>
    .declaration ⟨"effect/schema/Deferred", .null⟩ none [schema value, schema error] []
  | .var _ => .declaration ⟨"effect/schema/TypeParameter", .null⟩ none [] []
  | .union left right => .union none [] [schema left, schema right] .anyOf
  -- [arm:record] an rc.112 struct: named properties, no index signature
  | .record fs => .objects none [] (schemaProps fs) []
  -- [arm:optKey] outside a record field (refused at formation): the inner schema
  | .optKey inner => schema inner
  -- [arm:map] `Schema.Record(K, V)`: no property, one index signature
  | .map key value => .objects none [] [] [{ parameter := schema key, type := schema value }]
  -- [arm:tuple] `Schema.Tuple([…])`: plain elements, no rest
  | .tuple items => .arrays none [] (schemaElems items) []
  -- [arm:app] a declaration with type parameters (`Schema/Representation.lean:704`)
  | .app name args => .declaration ⟨name, .null⟩ none (schemaList args) []
  -- [arm:null]
  | .null => .null none []
  -- [arm:undefined]
  | .undefined => .undefined none []
  -- [arm:number] plain `Schema.Number`
  | .number => .number none []
  -- [arm:bytes] rc.112 `Schema.Uint8Array` (`Schema.ts:13605-13621`)
  | .bytes => .declaration ⟨"effect/schema/Uint8Array", .null⟩ none [] []
-- [arm:tuple]
def schemaElems : List PTy → List Element
  | [] => []
  | t :: ts => { isOptional := false, type := schema t, annotations := none } :: schemaElems ts
-- [arm:app]
def schemaList : List PTy → List Representation
  | [] => []
  | t :: ts => schema t :: schemaList ts
-- [arm:record]
def schemaProps : List (String × PTy) → List PropertySignature
  -- [arm:record]
  | [] => []
  -- [arm:record]
  | (n, t) :: fs =>
    (match t with
     -- [arm:optKey] `Schema.optionalKey`: the flag over the inner schema
     | .optKey u =>
       { name := .string n, type := schema u, isOptional := true, isMutable := false,
         annotations := none }
     -- [arm:record]
     | t' =>
       { name := .string n, type := schema t', isOptional := false, isMutable := false,
         annotations := none }) :: schemaProps fs
end

/-- A located refusal: the path from the root, then the reason (the vocabulary's shape). -/
structure Refusal where
  path : List String
  reason : String
deriving DecidableEq

-- [change:located]
abbrev Read (α : Type) := Except Refusal α

-- [change:located]
def refuse {α : Type} (path : List String) (reason : String) : Read α := .error ⟨path, reason⟩

-- [change:located]
/-- Prefix a child's refusal with the child's position. -/
def under {α : Type} (segment : String) : Read α → Read α
  | .ok a => .ok a
  | .error e => .error { e with path := segment :: e.path }

/-- The annotation allowlist: revision 5's eight documentation keys (`annotation-review.md`)
and, proposed here, `arbitrary` (rc.112 writes it on its own `isInt` filter: question 2 E9d; a
fast-check generation hint, read by no parser). Every other key refuses by name. -/
-- [change:annotations]
def docKeys : List String :=
  ["identifier", "title", "description", "documentation", "examples", "default", "message",
   "expected", "arbitrary"]

-- [change:annotations]
def annOk : Annotations → Bool
  | none => true
  | some entries => entries.all fun e => docKeys.contains e.key

-- [change:annotations]
def checkAnn (path : List String) : Annotations → Read Unit
  | none => .ok ()
  | some entries =>
    match entries.find? (fun e => !docKeys.contains e.key) with
    | some e => refuse (path ++ ["annotations"])
        ("annotation '" ++ e.key ++ "' is not documentation: it changes decoding or is unknown")
    | none => .ok ()

/-- The whole-check comparison (row 128): the `isInt` filter exactly, its payload `null`, no
referenced schemas, not aborted, documentation annotations only. -/
-- [change:whole-check]
def isIntC : Check → Bool
  | .filter ⟨"effect/schema/isInt", .null, none⟩ a false => annOk a
  | _ => false

-- [change:whole-check]
def nonNegC : Check → Bool
  | .filter ⟨"effect/schema/isGreaterThanOrEqualTo", .obj [("minimum", .number z)], none⟩ a false =>
    z.bits == 0 && annOk a
  | _ => false

/-- A union as the last member of a union: the right spine of a nested union. -/
def isAnyOfUnion : Representation → Bool
  | .union _ [] _ .anyOf => true
  | _ => false

mutual
/-- The reader with located refusals. Production arms with `Option` replaced by `Read`; the new
arms read records, optional keys, maps and n-ary unions; the whole-check comparison and the
`TypeParameter` refusal are row 128's repairs. -/
def ofSchemaL : Representation → Read PTy
  | .never a [] => do checkAnn [] a; .ok .never
  | .unknown a [] => do checkAnn [] a; .ok .unknown
  | .void a [] => do checkAnn [] a; .ok .unit
  -- [change:whole-check]
  | .number a [c] => do
    checkAnn [] a
    if isIntC c then .ok .int else refuse ["checks[0]"] "a check Ty cannot represent"
  -- [change:whole-check]
  | .number a [c, d] => do
    checkAnn [] a
    if isIntC c then
      if nonNegC d then .ok .nat else refuse ["checks[1]"] "a check Ty cannot represent"
    else refuse ["checks[0]"] "a check Ty cannot represent"
  -- [arm:number] plain `Schema.Number` (binary64, if row 121 rules it; refused by name until then)
  | .number a [] => do checkAnn [] a; .ok .number
  | .string a [] => do checkAnn [] a; .ok .string
  | .boolean a [] => do checkAnn [] a; .ok .bool
  | .literal a [] (.string s) => do checkAnn [] a; .ok (.lit s)
  -- [change:declarations] a reserved id reads as its constructor; any other id is a nominal reference
  | .declaration ⟨id, .null⟩ a params [] => do
    checkAnn [] a
    if reservedId id then readReserved id params
    else
      match params with
      | [] => .ok (.handle id)
      -- [arm:app]
      | _ => (readArgs 0 params).map (.app id)
  | .arrays a [] [] [item] => do
    checkAnn [] a
    (under "rest[0]" (ofSchemaL item)).map .list
  | .arrays a [] [⟨false, x, ax⟩, ⟨false, y, ay⟩] [] => do
    checkAnn [] a
    checkAnn ["elements[0]"] ax
    checkAnn ["elements[1]"] ay
    let tx ← under "elements[0]" (ofSchemaL x)
    let ty ← under "elements[1]" (ofSchemaL y)
    .ok (.prod tx ty)
  -- [arm:tuple] any other arity, plain elements, no rest
  | .arrays a [] els [] => do
    checkAnn [] a
    (readElems 0 els).map .tuple
  -- [arm:null]
  | .null a [] => do checkAnn [] a; .ok .null
  -- [change:n-ary-union] an rc.112 union of two or more members, right-nested
  | .union a [] (m :: m' :: ms) .anyOf => do
    checkAnn [] a
    readMembers 0 (m :: m' :: ms)
  -- [arm:record] named properties, no index signature; a repeated name refuses where it repeats
  | .objects a [] ps [] => do
    checkAnn [] a
    let fs ← readProps ps
    match firstRepeat fs [] with
    | some n => refuse [n] "repeatedField: a record names each field once"
    | none => .ok (.record fs)
  -- [arm:map] exactly one index signature over `Schema.String`, no property
  | .objects a [] [] [⟨.string pa [], v⟩] => do
    checkAnn [] a
    checkAnn ["indexSignatures[0]", "parameter"] pa
    (under "indexSignatures[0]" (ofSchemaL v)).map (.map .string)
  -- [arm:map]
  | .objects _ [] [] [_] => refuse ["indexSignatures[0]", "parameter"]
      "a map is keyed by Schema.String only (row 125)"
  -- [arm:record]
  | .objects _ [] _ _ => refuse ["indexSignatures"] "index signatures beside properties (StructWithRest) have no Ty"
  -- [arm:undefined] (with it, rc.112's `Schema.optional(A)`, `Union[A, Undefined]`, reads)
  | .undefined a [] => do checkAnn [] a; .ok .undefined
  | _ => refuse [] "a node Ty cannot represent"
-- [change:declarations] the production declaration arms, by arity, for the reserved ids
def readReserved (id : String) : List Representation → Read PTy
  | [] =>
    -- [change:var] row 128's `var` repair: the template parameter is not a program type
    if id = "effect/schema/TypeParameter" then
      refuse [] "a row template's parameter is not a program type (row 128)"
    -- [arm:bytes]
    else if id = "effect/schema/Uint8Array" then .ok .bytes
    else .ok (.handle id)
  | [val] =>
    if id = "effect/schema/Option" then
      (under "typeParameters[0]" (ofSchemaL val)).map .option
    else if id = "effect/schema/Ref" then
      (under "typeParameters[0]" (ofSchemaL val)).map .refOf
    else refuse [] ("declaration '" ++ id ++ "' with one parameter has no Ty")
  | [x, y] =>
    if id = "effect/schema/Result" then do
      let tv ← under "typeParameters[0]" (ofSchemaL x)
      let te ← under "typeParameters[1]" (ofSchemaL y)
      .ok (.except te tv)
    else if id = "effect/schema/Fiber" then do
      let tv ← under "typeParameters[0]" (ofSchemaL x)
      let te ← under "typeParameters[1]" (ofSchemaL y)
      .ok (.fiberOf tv te)
    else if id = "effect/schema/Deferred" then do
      let tv ← under "typeParameters[0]" (ofSchemaL x)
      let te ← under "typeParameters[1]" (ofSchemaL y)
      .ok (.deferredOf tv te)
    else if id = "effect/schema/Cause" && Effect4.Schema.Bridge.isDefect y then
      (under "typeParameters[0]" (ofSchemaL x)).map .causeOf
    else refuse [] ("declaration '" ++ id ++ "' with two parameters has no Ty")
  | [v, e, d] =>
    if id = "effect/schema/Exit" && Effect4.Schema.Bridge.isDefect d then do
      let tv ← under "typeParameters[0]" (ofSchemaL v)
      let te ← under "typeParameters[1]" (ofSchemaL e)
      .ok (.exitOf tv te)
    else refuse [] ("declaration '" ++ id ++ "' with three parameters has no Ty")
  | _ => refuse [] ("the reserved declaration '" ++ id ++ "' at this arity has no Ty")
-- [arm:tuple]
def readElems (i : Nat) : List Element → Read (List PTy)
  | [] => .ok []
  | ⟨false, t, a⟩ :: es => do
    checkAnn ["elements[" ++ toString i ++ "]"] a
    let tt ← under ("elements[" ++ toString i ++ "]") (ofSchemaL t)
    let rest ← readElems (i + 1) es
    .ok (tt :: rest)
  | ⟨true, _, _⟩ :: _ =>
    refuse ["elements[" ++ toString i ++ "]"] "an optional tuple element has no Ty"
-- [arm:app]
def readArgs (i : Nat) : List Representation → Read (List PTy)
  | [] => .ok []
  | r :: rs => do
    let t ← under ("typeParameters[" ++ toString i ++ "]") (ofSchemaL r)
    let rest ← readArgs (i + 1) rs
    .ok (t :: rest)
-- [change:n-ary-union]
def readMembers (i : Nat) : List Representation → Read PTy
  | [] => refuse [] "an empty union"
  | [m] => under ("types[" ++ toString i ++ "]") (ofSchemaL m)
  | m :: ms => do
    let a ← under ("types[" ++ toString i ++ "]") (ofSchemaL m)
    let b ← readMembers (i + 1) ms
    .ok (.union a b)
-- [arm:record]
def readProps : List PropertySignature → Read (List (String × PTy))
  | [] => .ok []
  | ⟨.string n, t, opt, isMut, a⟩ :: ps => do
    if isMut then refuse [n] "mutableKey: Ty records are readonly"
    else do
      checkAnn [n] a
      let tt ← under n (ofSchemaL t)
      let rest ← readProps ps
      -- [arm:optKey] `isOptional` reads as the optional-key modifier
      .ok ((n, if opt then .optKey tt else tt) :: rest)
  | ⟨.number _, _, _, _, _⟩ :: _ => refuse [] "a numeric property key has no Ty field name"
  | ⟨.globalSymbol k, _, _, _, _⟩ :: _ => refuse [k.key] "a symbol property key has no Ty field name"
end

/-! ## §5 The retraction, on the copy (proved) -/

/-- The motive: the retraction at `t`, and, at an optional key, at the type it modifies. -/
def RetractMotive (t : PTy) : Prop :=
  t.closed = true →
    (t.wf = true → ofSchemaL (schema t) = .ok t) ∧
    (∀ u, t = .optKey u → u.wf = true → ofSchemaL (schema u) = .ok u)

theorem readProps_cons_plain (n : String) (t : PTy) (fs gs : List (String × PTy))
    (ht : ofSchemaL (schema t) = .ok t) (hs : readProps (schemaProps fs) = .ok gs) :
    readProps (⟨.string n, schema t, false, false, none⟩ :: schemaProps fs) =
      .ok ((n, t) :: gs) := by
  simp only [readProps, Bool.false_eq_true, ↓reduceIte, checkAnn, ht, under, hs]
  rfl

theorem readProps_cons_opt (n : String) (u : PTy) (fs gs : List (String × PTy))
    (hu : ofSchemaL (schema u) = .ok u) (hs : readProps (schemaProps fs) = .ok gs) :
    readProps (⟨.string n, schema u, true, false, none⟩ :: schemaProps fs) =
      .ok ((n, .optKey u) :: gs) := by
  simp only [readProps, Bool.false_eq_true, ↓reduceIte, checkAnn, hu, under, hs]
  rfl

theorem readProps_schemaProps (fs : List (String × PTy))
    (ih : ∀ p ∈ fs, RetractMotive p.2) (hc : PTy.closedFields fs = true)
    (hw : PTy.wfFields fs = true) : readProps (schemaProps fs) = .ok fs := by
  induction fs with
  | nil => rfl
  | cons p fs ihl =>
    obtain ⟨n, t⟩ := p
    simp only [PTy.closedFields, Bool.and_eq_true] at hc
    have ihp := ih (n, t) List.mem_cons_self hc.1
    have ihs : PTy.wfFields fs = true → readProps (schemaProps fs) = .ok fs :=
      fun hw' => ihl (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hc.2 hw'
    cases t
    case optKey u =>
      simp only [PTy.wfFields, Bool.and_eq_true] at hw
      simp only [schemaProps]
      exact readProps_cons_opt n u fs fs (ihp.2 u rfl hw.1) (ihs hw.2)
    all_goals
      simp only [PTy.wfFields, Bool.and_eq_true] at hw
      simp only [schemaProps]
      exact readProps_cons_plain n _ fs fs (ihp.1 hw.1) (ihs hw.2)

theorem rOption : reservedId "effect/schema/Option" = true := rfl
theorem rRef : reservedId "effect/schema/Ref" = true := rfl
theorem rResult : reservedId "effect/schema/Result" = true := rfl
theorem rFiber : reservedId "effect/schema/Fiber" = true := rfl
theorem rDeferred : reservedId "effect/schema/Deferred" = true := rfl
theorem rCause : reservedId "effect/schema/Cause" = true := rfl
theorem rExit : reservedId "effect/schema/Exit" = true := rfl
theorem rUint8 : reservedId "effect/schema/Uint8Array" = true := rfl

theorem readElems_schemaElems (ts : List PTy) (ih : ∀ t ∈ ts, RetractMotive t)
    (hc : PTy.closedList ts = true) (hw : PTy.wfList ts = true) (i : Nat) :
    readElems i (schemaElems ts) = .ok ts := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ihl =>
    simp only [PTy.closedList, Bool.and_eq_true] at hc
    simp only [PTy.wfList, Bool.and_eq_true] at hw
    have h1 := (ih t List.mem_cons_self hc.1).1 hw.1
    have h2 := ihl (fun u hu => ih u (List.mem_cons_of_mem _ hu)) hc.2 hw.2 (i + 1)
    simp only [schemaElems, readElems, checkAnn, under, h1, h2]
    rfl

theorem readArgs_schemaList (ts : List PTy) (ih : ∀ t ∈ ts, RetractMotive t)
    (hc : PTy.closedList ts = true) (hw : PTy.wfList ts = true) (i : Nat) :
    readArgs i (schemaList ts) = .ok ts := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ihl =>
    simp only [PTy.closedList, Bool.and_eq_true] at hc
    simp only [PTy.wfList, Bool.and_eq_true] at hw
    have h1 := (ih t List.mem_cons_self hc.1).1 hw.1
    have h2 := ihl (fun u hu => ih u (List.mem_cons_of_mem _ hu)) hc.2 hw.2 (i + 1)
    simp only [schemaList, readArgs, under, h1, h2]
    rfl

/-- **The retraction at every form** (K2's second law, the copy's `ofSchema_schema`): on a closed,
well-formed type the located reader answers the type the writer wrote. -/
theorem retract (t : PTy) : RetractMotive t := by
  induction t using PTy.ind' with
  | never => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | unit => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | nat => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | int => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | string => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | bool => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | lit s => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | unknown => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | null => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | undefined => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | number => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | bytes => exact fun _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | var i => exact fun hc => absurd hc Bool.false_ne_true
  | handle s =>
    refine fun _ => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hw
    cases hr : reservedId s with
    | true => simp only [schema, ofSchemaL, checkAnn, hr, ↓reduceIte, readReserved, hw.1, hw.2]; rfl
    | false => simp only [schema, ofSchemaL, checkAnn, hr, Bool.false_eq_true, ↓reduceIte]; rfl
  | option t ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [schema, ofSchemaL, checkAnn, rOption, ↓reduceIte, readReserved, (ih hc).1 hw]
    rfl
  | list t ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [schema, Schema.array, ofSchemaL, checkAnn, under, (ih hc).1 hw]
    rfl
  | refOf t ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [schema, ofSchemaL, checkAnn, rRef, ↓reduceIte, readReserved, (ih hc).1 hw]
    rfl
  | causeOf t ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [schema, ofSchemaL, checkAnn, rCause, ↓reduceIte, readReserved, (ih hc).1 hw]
    rfl
  | prod a b iha ihb =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    simp only [PTy.wf, Bool.and_eq_true] at hw
    simp only [schema, Schema.tuple, Schema.element, ofSchemaL, checkAnn, under,
      (iha hc.1).1 hw.1, (ihb hc.2).1 hw.2]
    rfl
  | except e a ihe iha =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    simp only [PTy.wf, Bool.and_eq_true] at hw
    simp only [schema, ofSchemaL, checkAnn, rResult, ↓reduceIte, readReserved,
      (ihe hc.1).1 hw.1, (iha hc.2).1 hw.2]
    rfl
  | exitOf a e iha ihe =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    simp only [PTy.wf, Bool.and_eq_true] at hw
    simp only [schema, ofSchemaL, checkAnn, rExit, ↓reduceIte, readReserved,
      (iha hc.1).1 hw.1, (ihe hc.2).1 hw.2]
    rfl
  | fiberOf a e iha ihe =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    simp only [PTy.wf, Bool.and_eq_true] at hw
    simp only [schema, ofSchemaL, checkAnn, rFiber, ↓reduceIte, readReserved,
      (iha hc.1).1 hw.1, (ihe hc.2).1 hw.2]
    rfl
  | deferredOf a e iha ihe =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    simp only [PTy.wf, Bool.and_eq_true] at hw
    simp only [schema, ofSchemaL, checkAnn, rDeferred, ↓reduceIte, readReserved,
      (iha hc.1).1 hw.1, (ihe hc.2).1 hw.2]
    rfl
  | union a b iha ihb =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    simp only [PTy.wf, Bool.and_eq_true] at hw
    simp only [schema, ofSchemaL, checkAnn, readMembers, under,
      (iha hc.1).1 hw.1, (ihb hc.2).1 hw.2]
    rfl
  | record fs ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed] at hc
    simp only [PTy.wf, Bool.and_eq_true, Option.isNone_iff_eq_none] at hw
    simp only [schema, ofSchemaL, checkAnn, readProps_schemaProps fs ih hc hw.2, bind,
      Except.bind, hw.1]
  | optKey u ih =>
    refine fun hc => ⟨fun hw => absurd hw Bool.false_ne_true, fun u' h hw => ?_⟩
    cases h
    exact (ih hc).1 hw
  | map k v ihk ihv =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed, Bool.and_eq_true] at hc
    cases k with
    | string =>
      simp only [PTy.wf] at hw
      simp only [schema, Schema.string, ofSchemaL, checkAnn, under, (ihv hc.2).1 hw]
      rfl
    | _ => simp only [PTy.wf, Bool.false_eq_true] at hw
  | tuple ts ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed] at hc
    simp only [PTy.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hw
    have hr := readElems_schemaElems ts ih hc hw.2 0
    rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · rfl
    · simp only [schemaElems] at hr
      simp only [schema, schemaElems, ofSchemaL, checkAnn, hr]
      rfl
    · exact absurd rfl hw.1
    · simp only [schemaElems] at hr
      simp only [schema, schemaElems, ofSchemaL, checkAnn, hr]
      rfl
  | app n ts ih =>
    refine fun hc => ⟨fun hw => ?_, fun _ h => nomatch h⟩
    simp only [PTy.closed] at hc
    simp only [PTy.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
    have hr := readArgs_schemaList ts ih hc hw.2 0
    rcases ts with _ | ⟨a, rest⟩
    · simp only [List.isEmpty_nil] at hw
      exact absurd hw.1.1 (by decide)
    · simp only [schemaList] at hr
      simp only [schema, schemaList, ofSchemaL, checkAnn, hw.1.2, Bool.false_eq_true, ↓reduceIte,
        hr]
      rfl

theorem ofSchemaL_schema (t : PTy) (hc : t.closed = true) (hw : t.wf = true) :
    ofSchemaL (schema t) = .ok t :=
  ((retract t) hc).1 hw

/-! ## §6 `N_S` as a fold, and the exact embedding (proved) -/

/-- `N_S`'s union step: an `anyOf` union whose last member is itself an unchecked `anyOf` union
(after erasure) splices that member's list (the right spine; rc.112 decodes the nested and the
flat union alike, question 2 E10f). Children arrive normalised, so one splice suffices. -/
-- [change:N_S]
def spliceLast (checks : List Check) (mode : UnionMode) (ts : List Representation) :
    List Representation :=
  match mode, checks, ts.getLast? with
  | .anyOf, [], some (.union none [] ms .anyOf) => ts.dropLast ++ ms
  | _, _, _ => ts

/-- The named normaliser `N_S`, an algebra of the generated fold (`Schema/Fold.lean`): erase
every annotation bag (node, property, element, check), and flatten an `anyOf` union's right
spine. Property order is kept: the reader reads it as written. -/
-- [change:N_S]
def nsAlg : RepresentationAlgebra RepresentationSelfCarrier where
  representation_declaration rep _ tps cs := .declaration rep none tps cs
  representation_reference k := .reference k
  representation_suspend _ cs th := .suspend none cs th
  representation_null _ cs := .null none cs
  representation_undefined _ cs := .undefined none cs
  representation_void _ cs := .void none cs
  representation_never _ cs := .never none cs
  representation_unknown _ cs := .unknown none cs
  representation_any _ cs := .any none cs
  representation_string _ cs := .string none cs
  representation_number _ cs := .number none cs
  representation_boolean _ cs := .boolean none cs
  representation_bigint _ cs := .bigint none cs
  representation_symbol _ cs := .symbol none cs
  representation_literal _ cs v := .literal none cs v
  representation_uniqueSymbol _ cs k := .uniqueSymbol none cs k
  representation_objectKeyword _ cs := .objectKeyword none cs
  representation_enum _ cs es := .enum none cs es
  representation_templateLiteral _ cs ps := .templateLiteral none cs ps
  representation_arrays _ cs els rest :=
    .arrays none cs (els.map fun e => { e with annotations := none }) rest
  representation_objects _ cs ps is :=
    .objects none cs (ps.map fun p => { p with annotations := none }) is
  representation_union _ cs ts mode := .union none cs (spliceLast cs mode ts) mode
  check_filter rep _ ab := .filter rep none ab
  check_filterGroup rep _ cs := .filterGroup rep none cs

-- [change:N_S]
def N_S (r : Representation) : Representation := cata_representation nsAlg r

/-- The reader guarded by the writer's image modulo `N_S` (probe C's `readExact`, the formal
pass's TY-09 route 1): answer `t` only when `N_S (schema t) = N_S r`. -/
-- [change:exact]
def ofSchemaExact (r : Representation) : Read PTy :=
  match ofSchemaL r with
  | .ok t =>
    if N_S (schema t) = N_S r then .ok t
    else refuse [] "exactness: the reading's schema differs from the input modulo N_S"
  | .error e => .error e

/-- **Exactness modulo `N_S`** (K2's third law). -/
theorem ofSchemaExact_exact {r : Representation} {t : PTy} (h : ofSchemaExact r = .ok t) :
    N_S (schema t) = N_S r := by
  unfold ofSchemaExact at h
  split at h
  · rename_i t' _
    by_cases hN : N_S (schema t') = N_S r
    · rw [if_pos hN] at h
      cases h
      exact hN
    · rw [if_neg hN] at h
      exact nomatch h
  · exact nomatch h

/-- The guard only refuses. -/
theorem ofSchemaExact_le {r : Representation} {t : PTy} (h : ofSchemaExact r = .ok t) :
    ofSchemaL r = .ok t := by
  unfold ofSchemaExact at h
  split at h
  · rename_i t' ht'
    by_cases hN : N_S (schema t') = N_S r
    · rw [if_pos hN] at h
      cases h
      exact ht'
    · rw [if_neg hN] at h
      exact nomatch h
  · exact nomatch h

/-- **The retraction is kept** under the guard (K2's second law for the exact reader). -/
theorem ofSchemaExact_schema (t : PTy) (hc : t.closed = true) (hw : t.wf = true) :
    ofSchemaExact (schema t) = .ok t := by
  unfold ofSchemaExact
  rw [ofSchemaL_schema t hc hw]
  simp only [↓reduceIte]

/-! ## §7 The bridge per form: admitted shapes and located refusals (tested) -/

def readsAs (r : Representation) (t : PTy) : Bool :=
  match ofSchemaL r with
  | .ok t' => t' == t
  | .error _ => false

def refusedAt (r : Representation) (path : List String) : Bool :=
  match ofSchemaL r with
  | .error e => e.path == path
  | .ok _ => false

def exactAgrees (r : Representation) : Bool :=
  match ofSchemaL r, ofSchemaExact r with
  | .ok t, .ok t' => t == t'
  | .error _, .error _ => true
  | _, _ => false

def prop (n : String) (r : Representation) (opt : Bool := false) (isMut : Bool := false)
    (ann : Annotations := none) : PropertySignature :=
  { name := .string n, type := r, isOptional := opt, isMutable := isMut, annotations := ann }

/-- rc.112's own persisted `Schema.Int`/`Schema.Natural` checks, annotations included (question 2,
E9d, E9d2: `logs/q2-edges.log` `REPR int`, `REPR natural`). -/
def rcIsInt : Check :=
  .filter ⟨"effect/schema/isInt", .null, none⟩
    (some [⟨"expected", .str "an integer"⟩,
      ⟨"arbitrary", .obj [("constraint", .obj [("integer", .bool true)])]⟩]) false
def rcNonNeg : Check :=
  .filter ⟨"effect/schema/isGreaterThanOrEqualTo", .obj [("minimum", Arch.Json.ofNat 0)], none⟩
    (some [⟨"expected", .str "a value greater than or equal to 0"⟩]) false
def rcInt : Representation := .number none [rcIsInt]
def rcNat : Representation := .number none [rcIsInt, rcNonNeg]

def tagged (tag : String) (fields : List (String × PTy)) : PTy :=
  .record (("_tag", .lit tag) :: fields)

-- records: the writer and the reader, written order, located refusals
def rAB : PTy := .record [("a", .int), ("b", .string)]
#guard readsAs (schema rAB) rAB
#guard readsAs (.objects none [] [prop "b" Schema.string, prop "a" rcInt] [])
  (.record [("b", .string), ("a", .int)])
#guard refusedAt (.objects none [] [prop "a" Schema.string, prop "b" rcInt, prop "a" rcInt] []) ["a"]
#guard refusedAt (.objects none [] [prop "a" Schema.string (isMut := true)] []) ["a"]
#guard refusedAt (.objects (some [⟨"parseOptions", .obj [("onExcessProperty", .str "error")]⟩]) []
  [prop "a" Schema.string] []) ["annotations"]
#guard readsAs (.objects (some [⟨"identifier", .str "User"⟩]) []
  [prop "a" Schema.string (ann := some [⟨"title", .str "A"⟩])] []) (.record [("a", .string)])
#guard refusedAt (.objects none [] [prop "a" Schema.string (ann := some [⟨"parseOptions", .obj []⟩])] [])
  ["a", "annotations"]
#guard refusedAt (.objects none [] [prop "user" (.objects none [] [prop "age" Schema.bigint] [])] [])
  ["user", "age"]
#guard refusedAt (.objects none [] [prop "a" Schema.string] [{ parameter := Schema.string, type := rcInt }])
  ["indexSignatures"]
def numKeyProp : PropertySignature :=
  { name := .number Float64.zero, type := Schema.string, isOptional := false, isMutable := false,
    annotations := none }
#guard refusedAt (.objects none [] [numKeyProp] []) []
#guard readsAs (.objects none [] [] []) (.record [])
-- optional keys: `optionalKey` reads; `optional` (`Union[A, Undefined]`) reads once the `undefined`
-- leaf lands (seat T's N4), as the three-state slot `optKey (union A undefined)`
def rOpt : PTy := .record [("a", .optKey .int), ("b", .string)]
#guard readsAs (schema rOpt) rOpt
#guard readsAs (.objects none [] [prop "a" (.union none [] [rcInt, Schema.undefined] .anyOf) (opt := true)] [])
  (.record [("a", .optKey (.union .int .undefined))])
-- maps: one index signature over `Schema.String`
def rMap : PTy := .map .string .int
#guard readsAs (schema rMap) rMap
#guard refusedAt (.objects none [] [] [{ parameter := Schema.number, type := rcInt }])
  ["indexSignatures[0]", "parameter"]
#guard refusedAt (.objects none [] [] [{ parameter := .string none [Schema.Check.pattern "^a"], type := rcInt }])
  ["indexSignatures[0]", "parameter"]
#guard readsAs (.objects none [] [prop "a" rcInt, prop "b" rcInt] []) (.record [("a", .int), ("b", .int)])
-- tagged unions: unions of records; n-ary `anyOf` reads right-nested; `oneOf` refuses
def rTU : PTy := .union (tagged "A" [("x", .int)]) (tagged "B" [("y", .string)])
#guard readsAs (schema rTU) rTU
def flat3 : Representation := .union none []
  [Schema.literalString "a", Schema.literalString "b", Schema.literalString "c"] .anyOf
def lit3 : PTy := .union (.lit "a") (.union (.lit "b") (.lit "c"))
#guard readsAs flat3 lit3
#guard (Effect4.Schema.Bridge.ofSchema flat3).isNone   -- today: refused (effect Red7)
#guard refusedAt (.union none [] [Schema.string, rcInt] .oneOf) []
#guard N_S (schema lit3) = N_S flat3              -- the nested writer and the flat reader agree modulo N_S
#guard schema lit3 ≠ flat3                       -- and not without it
-- number and int: the whole-check comparison against rc.112's own documents
#guard readsAs rcInt .int
#guard readsAs rcNat .nat
#guard readsAs (schema .nat) .nat
#guard readsAs (.number none []) .number        -- binary64, if row 121 rules it (refused by name until then)
def ge5 : Representation := .number none [Effect4.Schema.Bridge.isIntCheck,
  .filter ⟨"effect/schema/isGreaterThanOrEqualTo", .obj [("minimum", Arch.Json.ofNat 5)], none⟩ none false]
#guard Effect4.Schema.Bridge.ofSchema ge5 = some .nat       -- RED CONTROL: today "≥ 5" reads as nat (PED-05)
#guard refusedAt ge5 ["checks[1]"]
def groupedInt : Representation := .number none [Schema.Check.group
  (Schema.Check.named "effect/schema/isGreaterThanOrEqualTo" (.obj [("minimum", Arch.Json.ofNat 5)])) []
  none (some ⟨"effect/schema/isInt", .null, none⟩)]
#guard Effect4.Schema.Bridge.ofSchema groupedInt = some .int  -- RED CONTROL: today a group reads as int (V1a)
#guard refusedAt groupedInt ["checks[0]"]
#guard refusedAt (.number none [.filter ⟨"effect/schema/isInt", .null, none⟩ none true]) ["checks[0]"]
#guard refusedAt (.number none [.filter ⟨"effect/schema/isInt", .null, none⟩
  (some [⟨"parseOptions", .obj [("disableChecks", .bool true)]⟩]) false]) ["checks[0]"]
-- the `var` repair: today the template parameter reads back as a handle (TREE-D12)
#guard Effect4.Schema.Bridge.ofSchema (Effect4.Schema.Bridge.schema (.var 0)) =
  some (.handle "effect/schema/TypeParameter")             -- RED CONTROL
#guard refusedAt (schema (.var 0)) []
-- seat T's forms: tuples (arity two is `prod`), nominal references, the leaves
def tup3 : PTy := .tuple [.int, .string, .bool]
#guard readsAs (schema tup3) tup3
#guard readsAs (schema (.tuple [])) (.tuple [])
#guard readsAs (schema (.tuple [.int])) (.tuple [.int])
#guard readsAs (schema (.tuple [.int, .string])) (.prod .int .string)     -- the normal form
#guard refusedAt (.arrays none [] [⟨true, Schema.string, none⟩] []) ["elements[0]"]
def stream : PTy := .app "Stream.Stream" [.int, .never, .never]
#guard readsAs (schema stream) stream
#guard readsAs (schema (.app "Duration.Duration" [])) (.handle "Duration.Duration")  -- the normal form
#guard readsAs (schema (.app "effect/schema/Option" [.int])) (.option .int)         -- a reserved id
#guard refusedAt (.declaration ⟨"Queue.Dequeue", .null⟩ none [Schema.bigint] []) ["typeParameters[0]"]
#guard readsAs (schema .null) .null && readsAs (schema .undefined) .undefined
#guard readsAs (schema .number) .number && readsAs (schema .bytes) .bytes
#guard readsAs (schema (.handle "effect/schema/Uint8Array")) .bytes                 -- `bytes` takes the name
-- the guard never fires on these inputs: the unguarded reader is exact on them (tested)
#guard [schema rAB, schema rOpt, schema rMap, schema rTU, flat3, rcInt, rcNat, ge5, groupedInt,
  schema tup3, schema stream, schema .bytes, schema (.tuple []),
  .objects none [] [prop "b" Schema.string, prop "a" rcInt] [],
  .objects (some [⟨"identifier", .str "User"⟩]) [] [prop "a" Schema.string] []].all exactAgrees

/-! ### The level of the exactness statement: `N_S` needs no property sort at the bridge (tested)

The copy's `schema` writes a record's fields in the type's own order and its reader keeps the
written order (the bridge level: `Bridge.schema`, `Bridge.ofSchema`, raw types), so `N_S` above
needs no property sort and a permuted struct reads and writes back permuted. The public writer
`Ty.schema` normalizes first (`Bridge.lean:243-244`) and writes the canonical order whatever the
document's, while rc.112 persists declaration order (question 2 E1–E2): an exactness statement
against the public writer would need `N_Sp` below (`nsAlg` with a stable, non-deduplicating sort in
the `objects` arm), and a union-member reordering as well, which rc.112's ordered `anyOf` can
observe (question 2 E7). So the statement belongs at the bridge level. -/

def propSortKey (p : PropertySignature) : String :=
  match p.name with
  | .string n => n
  | _ => ""

/-- Stable insertion by the field order; no dedupe (a normaliser never drops a property). -/
def insProp (p : PropertySignature) : List PropertySignature → List PropertySignature
  | [] => [p]
  | q :: qs => if nameLt (propSortKey p) (propSortKey q) then p :: q :: qs else q :: insProp p qs

def sortProps (ps : List PropertySignature) : List PropertySignature :=
  ps.foldl (fun acc p => insProp p acc) []

def nsSortedAlg : RepresentationAlgebra RepresentationSelfCarrier :=
  { nsAlg with
    representation_objects := fun _ cs ps is =>
      .objects none cs (sortProps (ps.map fun p => { p with annotations := none })) is }

def N_Sp (r : Representation) : Representation := cata_representation nsSortedAlg r

/-- rc.112's `Struct({ b, a })`, persisted in declaration order. -/
def permutedBA : Representation := .objects none [] [prop "b" Schema.string, prop "a" rcInt] []
#guard N_Sp (schema rAB) = N_Sp permutedBA
#guard sortProps [prop "b" Schema.string, prop "a" Schema.string, prop "a" Schema.boolean] =
  [prop "a" Schema.string, prop "a" Schema.boolean, prop "b" Schema.string]   -- stable, nothing dropped

/-- The store's shapes through the new reader: the `Test/Schema/DialectContract.lean` rows that
re-pin when records land (tested). A store struct carries `identifier` (allowlisted) and its
`nat` renders as `isInt` alone, so it reads as a record of `int`; a one-case sum is a
one-member union, refused; a nullary sum is a literal union. -/
def storeRead (sh : Effect4.Store.Shape) : Read PTy := ofSchemaL (Effect4.Store.render sh)
#guard readsAs (Effect4.Store.render (.struct "P" [("x", .nat)])) (.record [("x", .int)])
#guard (Effect4.Schema.Bridge.ofSchema (Effect4.Store.render (.struct "P" [("x", .nat)]))).isNone
#guard refusedAt (Effect4.Store.render (.sum "Tree" [("leaf", 0, [("value", .nat)])])) []
#guard readsAs (Effect4.Store.render (.sum "K" [("a", 0, []), ("b", 1, [])])) (.union (.lit "a") (.lit "b"))
#guard readsAs (Effect4.Store.render (.sum "Two" [("leaf", 0, [("value", .nat)]), ("node", 1, [])]))
  (.union (.record [("_tag", .lit "leaf"), ("value", .int)]) (.record [("_tag", .lit "node")]))
#guard refusedAt (Effect4.Store.render .anyRef) ["address"]
#guard readsAs (Effect4.Store.render (.pair .nat .string)) (.prod .int .string)

/-! ## §8 Membership on the copy (seat P owns it; the codec needs it) -/

def reasonAdmitsP (member : Val → PTy → Bool) (ty : PTy) :
    Reason Err Defect FiberId Ann → Bool
  | .fail e _ =>
    match valOfErr e with
    | some v => member v ty
    | none => false
  | .die _ _ | .interrupt _ _ => true

def causeAdmitsP (member : Val → PTy → Bool) (ty : PTy) (c : CauseV) : Bool :=
  c.reasons.all (reasonAdmitsP member ty)

/-- A tuple's items against their checkers, in order; lengths equal. -/
def fitList : List Val → List (Val → Bool) → Bool
  | [], [] => true
  | v :: vs, c :: cs => c v && fitList vs cs
  | _, _ => false

/-- Positional fit: each slot against its field's checker, in order; lengths equal. -/
def fitPos : List Val → List (String × (Val → Bool)) → Bool
  | [], [] => true
  | v :: vs, (_, c) :: cs => c v && fitPos vs cs
  | _, _ => false

def entryKey? : Val → Option String
  | .list [.str s, _] => some s
  | _ => none

def ascendingNames : List String → Bool
  | a :: b :: rest => nameLt a b && ascendingNames (b :: rest)
  | _ => true

/-- A map value's keys: strings, strictly ascending by bytes (so distinct). -/
def entriesAscending (es : List Val) : Bool :=
  match es.mapM entryKey? with
  | some ks => ascendingNames ks
  | none => false

mutual
/-- `Val.hasTy`, copied: production arms, then `int` (stage 5) and the three new forms. A
record reads its slots in canonical order: the algebra sorts the fields' checkers by name, so
the read stays a fold (the synthesis model's `hasTyAlg`). -/
def hasTyP (v : Val) (ty : PTy) (allocated : List String) : Bool :=
  match ty with
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => hasTyP x inner allocated
    | _ => false
  | .handle target =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => target == NativeOp.refTarget
      | some .promise => target == NativeOp.deferredTarget
      | some .scope => target == Ty.scopeTarget
      | some .external => externalHandleTarget target && allocated[index]? == some target
      | _ => false
    | _ => target == Ty.contextTarget && (Val.context? v).isSome
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  | .refOf _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .cell
    | _ => false
  | .deferredOf _ _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .promise
    | _ => false
  | .var _ => false
  | .exitOf a e =>
    match v with
    | Val.exitOk x => hasTyP x a allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmitsP (fun w _ => hasTyP w e allocated) e c
      | none => false
    | _ => false
  | .causeOf e =>
    match Val.cause? v with
    | some c => causeAdmitsP (fun w _ => hasTyP w e allocated) e c
    | none => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => hasTyP x ta allocated && hasTyP y tb allocated
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => hasTyP (Val.fiber id) ty allocated)
      | none => false
    | .list values => values.all fun x => hasTyP x ty allocated
    | _ => false
  | .union l r => hasTyP v l allocated || hasTyP v r allocated
  | .lit value => match v with | .str s => s == value | _ => false
  | .never => false
  | .unknown => true
  -- [arm:int] stage 5 (row 121): `Int`'s generated image (`IntCanonical.toVal`)
  | .int => match v with | .ctor 0 [.nat _] | .ctor 1 [.nat _] => true | _ => false
  | .except error value =>
    match v with
    | .ctor 0 [err] => hasTyP err error allocated
    | .ctor 1 [val] => hasTyP val value allocated
    | _ => false
  -- [arm:record] row 165: `ctor 0 [list names, list slots]` in canonical order; names first, exactly
  | .record fs =>
    match v with
    | .ctor 0 [.list ns, .list vs] =>
      ns == (canonF (fieldCheckers fs allocated)).map (fun p => .str p.1) &&
        fitPos vs (canonF (fieldCheckers fs allocated))
    | _ => false
  -- [arm:optKey] the slot of an optional field: absent or present
  | .optKey t =>
    match v with
    | .none => true
    | .some x => hasTyP x t allocated
    | _ => false
  -- [arm:tuple] `Val.list` of the items, exact arity, pointwise (as `prod` at arity two)
  | .tuple ts =>
    match v with
    | .list vs => fitList vs (itemCheckers ts allocated)
    | _ => false
  -- [arm:app] a nominal reference is opaque (like `handle`; its value judgment is seat P's)
  | .app _ _ => false
  -- [arm:null] the value images of `null`, `undefined` and binary64 `number` are owed (P, row 121)
  | .null | .undefined | .number => false
  -- [arm:bytes] the existing `Val.bytes` frame
  | .bytes => match v with | .bytes _ => true | _ => false
  -- [arm:map] `[key, value]` pairs, keys strings ascending
  | .map k w =>
    match v with
    | .list entries =>
      entriesAscending entries && entries.all (fun e =>
        match e with
        | .list [kv, vv] => hasTyP kv k allocated && hasTyP vv w allocated
        | _ => false)
    | _ => false
-- [arm:record]
def fieldCheckers : List (String × PTy) → List String → List (String × (Val → Bool))
  | [], _ => []
  | (n, t) :: fs, al => (n, fun w => hasTyP w t al) :: fieldCheckers fs al
-- [arm:tuple]
def itemCheckers : List PTy → List String → List (Val → Bool)
  | [], _ => []
  | t :: ts, al => (fun w => hasTyP w t al) :: itemCheckers ts al
end

/-- Row 119's positional membership as first written (`ctor 0` of the slots, no names), kept only
for the red control: row 165 replaces it. -/
def posRecordFits (v : Val) (fs : List (String × PTy)) : Bool :=
  match v with
  | .ctor 0 vs => fitPos vs (canonF (fs.map (fun p => (p.1, fun w => hasTyP w p.2 []))))
  | _ => false

/-! ## §9 `Schema/Codec.lean`, copied: layout, support, the wire arms -/

mutual
def layoutP : PTy → PTy
  | .lit _ => .string
  | .option t => .option (layoutP t)
  | .list t => .list (layoutP t)
  | .prod a b => .prod (layoutP a) (layoutP b)
  | .except e a => .except (layoutP e) (layoutP a)
  | .exitOf a e => .exitOf (layoutP a) (layoutP e)
  | .causeOf e => .causeOf (layoutP e)
  -- [arm:record]
  | .record fs => .record (layoutFields fs)
  -- [arm:optKey]
  | .optKey t => .optKey (layoutP t)
  -- [arm:map]
  | .map k v => .map (layoutP k) (layoutP v)
  -- [arm:tuple]
  | .tuple ts => .tuple (layoutList ts)
  | t => t
-- [arm:tuple]
def layoutList : List PTy → List PTy
  | [] => []
  | t :: ts => layoutP t :: layoutList ts
-- [arm:record]
def layoutFields : List (String × PTy) → List (String × PTy)
  | [] => []
  | (n, t) :: fs => (n, layoutP t) :: layoutFields fs
end

mutual
def isSupportedP : PTy → Bool
  | .never | .unit | .nat | .string | .bool | .lit _ => true
  -- [arm:int]
  | .int => true
  | .option t | .list t | .causeOf t => isSupportedP t
  | .prod a b | .except a b | .exitOf a b | .union a b => isSupportedP a && isSupportedP b
  -- [arm:record]
  | .record fs => supportedFields fs
  -- [arm:optKey]
  | .optKey t => isSupportedP t
  -- [arm:map]
  | .map .string v => isSupportedP v
  -- [arm:tuple]
  | .tuple ts => supportedList ts
  -- [arm:app] [arm:null] [arm:undefined] [arm:number] [arm:bytes] refused by name: each obstacle in the note
  | _ => false
-- [arm:tuple]
def supportedList : List PTy → Bool
  | [] => true
  | t :: ts => isSupportedP t && supportedList ts
-- [arm:record]
def supportedFields : List (String × PTy) → Bool
  | [] => true
  | (_, t) :: fs => isSupportedP t && supportedFields fs
end

-- [arm:int]
def signBit : UInt64 := 0x8000000000000000

/-- `Int`'s generated value image (`Store/Domain/Canonical.lean:361-363`). -/
-- [arm:int]
def intVal : Int → Val
  | .ofNat n => .ctor 0 [.nat n]
  | .negSucc n => .ctor 1 [.nat n]

/-- A signed integer's JSON number: `ofNat`'s binary64, the sign bit set for a negative. -/
-- [arm:int]
def intJson : Int → Json
  | .ofNat n => Arch.Json.ofNat n
  | .negSucc n => .number ⟨Arch.binary64OfNat (n + 1) ||| signBit⟩

/-- Exact signed integral binary64 data in `intJson`'s image; `-0` refuses (rc.112 accepts it:
question 2, E9g). -/
-- [arm:int]
def int? : Json → Option Int
  | .number f =>
    if f.bits &&& signBit = 0 then (Schema.Codec.nat? (.number f)).map Int.ofNat
    else
      match Schema.Codec.nat? (.number ⟨f.bits &&& ~~~signBit⟩) with
      | some (m + 1) => if intJson (.negSucc m) = .number f then some (.negSucc m) else none
      | _ => none
  | _ => none

/-- A record's entries read from the value: each name from the value's name list (checked against
the type's), each slot through its field's encoder; an absent optional key writes no entry. -/
-- [arm:record]
def encodeNamed : List Val → List Val → List (String × (Val → Option (Option Json))) →
    Option (List (String × Json))
  | [], [], [] => some []
  | .str n :: ns, v :: vs, (m, enc) :: es =>
    if n = m then do
      let o ← enc v
      let rest ← encodeNamed ns vs es
      match o with
      | some j => some ((n, j) :: rest)
      | none => some rest
    else none
  | _, _, _ => none

mutual
/-- The structural encoder: production arms, then `int`, records, optional keys and maps. -/
def encodeRawP : PTy → Val → Option Json
  | .unit, .unit => some .null
  | .bool, .bool b => some (.bool b)
  | .nat, .nat n => some (Arch.Json.ofNat n)
  | .string, .str s | .lit _, .str s => some (.str s)
  | .option _, .none => some (.obj [("_tag", .str "None")])
  | .option t, .some v => (encodeRawP t v).map (Schema.Codec.tagged "Some" "value")
  | .list t, .list vs => (vs.mapM (encodeRawP t)).map Json.arr
  | .prod a b, .list [x, y] => do
    let jx ← encodeRawP a x
    let jy ← encodeRawP b y
    return .arr [jx, jy]
  | .except e _, .ctor 0 [v] => (encodeRawP e v).map (Schema.Codec.tagged "Failure" "failure")
  | .except _ a, .ctor 1 [v] => (encodeRawP a v).map (Schema.Codec.tagged "Success" "success")
  | .exitOf a _, .ctor 0 [v] => (encodeRawP a v).map (Schema.Codec.tagged "Success" "value")
  | .exitOf _ e, .ctor 1 [written] => do
    let c ← causeImage.ofVal written
    (Schema.Codec.encodeCause (encodeRawP e) c).map (Schema.Codec.tagged "Failure" "cause")
  | .causeOf e, v => do
    let c ← Val.cause? v
    Schema.Codec.encodeCause (encodeRawP e) c
  | .union a b, v =>
    if hasTyP v a [] then encodeRawP a v
    else if hasTyP v b [] then encodeRawP b v else none
  -- [arm:int]
  | .int, .ctor 0 [.nat n] => some (intJson (.ofNat n))
  -- [arm:int]
  | .int, .ctor 1 [.nat n] => some (intJson (.negSucc n))
  -- [arm:record] an object keyed by the field names, canonical order; an absent optional key has no entry
  | .record fs, .ctor 0 [.list ns, .list vs] =>
    (encodeNamed ns vs (canonF (fieldEncoders fs))).map Json.obj
  -- [arm:tuple] an array of the items, exact arity
  | .tuple ts, .list vs => (encodeItems ts vs).map Json.arr
  -- [arm:map] an object keyed by the map's keys, in the value's (ascending) order
  | .map .string w, .list entries =>
    (entries.mapM (fun (e : Val) =>
      match e with
      | .list [.str k, x] => (encodeRawP w x).map (fun j => (k, j))
      | _ => none)).map Json.obj
  | _, _ => none
-- [arm:tuple]
def encodeItems : List PTy → List Val → Option (List Json)
  | [], [] => some []
  | t :: ts, v :: vs => do
    let j ← encodeRawP t v
    let rest ← encodeItems ts vs
    some (j :: rest)
  | _, _ => none
-- [arm:record]
def fieldEncoders : List (String × PTy) → List (String × (Val → Option (Option Json)))
  | [] => []
  | (n, t) :: fs =>
    (n, match t with
      -- [arm:optKey] `none` is an absent key; `some x` its value
      | .optKey u => fun v =>
        match v with
        | .none => some none
        | .some x => (encodeRawP u x).map some
        | _ => none
      -- [arm:record]
      | t' => fun v => (encodeRawP t' v).map some) :: fieldEncoders fs
end

/-- A field's entry: absent, once, or refused when repeated (the strict field set). -/
-- [arm:record]
def lookupOnce (n : String) (entries : List (String × Json)) : Option (Option Json) :=
  match entries.filter (fun e => e.1 == n) with
  | [] => some none
  | [(_, j)] => some (some j)
  | _ => none

-- [arm:record]
def decodeSlots (entries : List (String × Json)) :
    List (String × (Option Json → Option Val)) → Option (List Val)
  | [] => some []
  | (n, dec) :: ds => do
    let oj ← lookupOnce n entries
    let v ← dec oj
    let rest ← decodeSlots entries ds
    some (v :: rest)

mutual
/-- The structural reader at a type, one fold with one parameter (probe R's `conv strict`): `strict`
is the codec (S-3: extra, duplicate and missing keys refuse), `!strict` is route A's row adapter
(entries the type does not name are dropped; a duplicated or missing declared name refuses).
Production arms, the union arm with the canonical-branch check (row 128: a later branch answers
only when no earlier branch's membership holds of its value, the encoder's own selection rule),
then `int`, records, optional keys, tuples and maps. -/
def convP (strict : Bool) : PTy → Json → Option Val
  | .unit, .null => some .unit
  | .bool, .bool b => some (.bool b)
  | .nat, j => (Schema.Codec.nat? j).map Val.nat
  | .string, .str s | .lit _, .str s => some (.str s)
  | .option t, j =>
    if Schema.Codec.fields? j ["_tag"] = some [.str "None"] then some .none
    else do
      let payload ← Schema.Codec.payload? j "Some" "value"
      (convP strict t payload).map Store.Val.some
  | .list t, .arr js => (js.mapM (convP strict t)).map Val.list
  | .prod a b, .arr [jx, jy] => do
    let x ← convP strict a jx
    let y ← convP strict b jy
    return .list [x, y]
  | .except e a, j =>
    if let some p := Schema.Codec.payload? j "Failure" "failure" then
      (convP strict e p).map (fun v => .ctor 0 [v])
    else do
      let p ← Schema.Codec.payload? j "Success" "success"
      (convP strict a p).map (fun v => .ctor 1 [v])
  | .exitOf a e, j =>
    if let some p := Schema.Codec.payload? j "Success" "value" then
      (convP strict a p).map (fun v => .ctor 0 [v])
    else do
      let p ← Schema.Codec.payload? j "Failure" "cause"
      (Schema.Codec.decodeCause (convP strict e) p).map Val.exitErr
  | .causeOf e, j => (Schema.Codec.decodeCause (convP strict e) j).map Val.exitErr
  -- [change:canonical-branch]
  | .union a b, j =>
    match (convP strict a j).filter (fun v => hasTyP v a []) with
    | some v => some v
    | none => (convP strict b j).filter (fun v => hasTyP v b [] && !hasTyP v a [])
  -- [arm:int]
  | .int, j => (int? j).map intVal
  -- [arm:record] the exact field set in any order (`strict`: no unnamed key; both: no repeated
  -- declared key, every required key); the value carries the canonical names (row 165)
  | .record fs, .obj entries =>
    if !strict || entries.all (fun e => ((canonF (fieldDecoders strict fs)).map (·.1)).contains e.1) then
      (decodeSlots entries (canonF (fieldDecoders strict fs))).map (fun slots =>
        .ctor 0 [.list ((canonF (fieldDecoders strict fs)).map (fun d => .str d.1)), .list slots])
    else none
  -- [arm:tuple]
  | .tuple ts, .arr js => (decodeItems strict ts js).map Val.list
  -- [arm:map] distinct keys, the value's pairs sorted by key
  | .map .string w, .obj entries =>
    if (firstRepeat entries []).isSome then none
    else (entries.mapM (fun e => (convP strict w e.2).map (fun v => (e.1, v)))).map
      (fun kvs => .list ((canonF kvs).map (fun kv => .list [.str kv.1, kv.2])))
  | _, _ => none
-- [arm:tuple]
def decodeItems (strict : Bool) : List PTy → List Json → Option (List Val)
  | [], [] => some []
  | t :: ts, j :: js => do
    let v ← convP strict t j
    let rest ← decodeItems strict ts js
    some (v :: rest)
  | _, _ => none
-- [arm:record]
def fieldDecoders (strict : Bool) : List (String × PTy) → List (String × (Option Json → Option Val))
  | [] => []
  | (n, t) :: fs =>
    (n, match t with
      -- [arm:optKey] an absent key is `none`; a present one `some`
      | .optKey u => fun oj =>
        match oj with
        | none => some .none
        | some j => (convP strict u j).map Store.Val.some
      -- [arm:record]
      | t' => fun oj => oj.bind (convP strict t')) :: fieldDecoders strict fs
end

/-- The codec's structural reader. -/
def decodeRawP (t : PTy) (j : Json) : Option Val := convP true t j

/-- Route A's structural row adapter (row 122; probe R's `Boundary.adapt`). -/
def adaptRawP (t : PTy) (j : Json) : Option Val := convP false t j

/-- Membership, a JSON image, and exact recovery (production `encode`, without `normalize`:
the laws below hold at every type, so production's `CTy` statements follow). -/
def encodeP (t : PTy) (v : Val) : Option Json :=
  if hasTyP v t [] then
    match encodeRawP (layoutP t) v with
    | none => none
    | some j => if decodeRawP (layoutP t) j = some v then some j else none
  else none

def decodeP (t : PTy) (j : Json) : Option Val :=
  (decodeRawP (layoutP t) j).filter (fun v => hasTyP v t [])

/-- Route A's row adapter at a type (row 122; probe R's `Boundary.adapt`): the codec's fold with
undeclared entries dropped, then the same membership check. -/
def adaptP (t : PTy) (j : Json) : Option Val :=
  (adaptRawP (layoutP t) j).filter (fun v => hasTyP v t [])

/-! ## §10 `Laws/Schema/Codec.lean`, copied (proved) -/

theorem encodeP_eq_some {t : PTy} {v : Val} {j : Json} :
    encodeP t v = some j ↔
      hasTyP v t [] = true ∧ encodeRawP (layoutP t) v = some j ∧
        decodeRawP (layoutP t) j = some v := by
  unfold encodeP
  by_cases ht : hasTyP v t [] = true
  · rw [if_pos ht]
    cases he : encodeRawP (layoutP t) v with
    | none => simp only [reduceCtorEq, false_and, and_false]
    | some k =>
      dsimp only
      by_cases hd : decodeRawP (layoutP t) k = some v
      · rw [if_pos hd]
        constructor
        · intro h
          cases h
          exact ⟨ht, rfl, hd⟩
        · intro h
          obtain ⟨_, h1, _⟩ := h
          cases h1
          rfl
      · rw [if_neg hd]
        constructor
        · intro h
          exact nomatch h
        · intro h
          obtain ⟨_, h1, h2⟩ := h
          cases h1
          exact absurd h2 hd
  · rw [if_neg ht]
    constructor
    · intro h
      exact nomatch h
    · intro h
      exact absurd h.1 ht

/-- Every successful encoding recovers exactly (production `decode_of_encode`). -/
theorem decodeP_of_encodeP {t : PTy} {v : Val} {j : Json} (h : encodeP t v = some j) :
    decodeP t j = some v := by
  obtain ⟨ht, _, hd⟩ := encodeP_eq_some.mp h
  unfold decodeP
  rw [hd, Option.filter_eq_some_iff]
  exact ⟨rfl, ht⟩

/-- Decoding implies membership (production `hasTy_decode`). -/
theorem hasTy_decodeP {t : PTy} {j : Json} {v : Val} (h : decodeP t j = some v) :
    hasTyP v t [] = true := by
  unfold decodeP at h
  rw [Option.filter_eq_some_iff] at h
  exact h.2

/-- What the session's reply check needs (probe R's `adapt_member`): the adapter answers members. -/
theorem adapt_memberP {t : PTy} {j : Json} {v : Val} (h : adaptP t j = some v) :
    hasTyP v t [] = true := by
  unfold adaptP at h
  rw [Option.filter_eq_some_iff] at h
  exact h.2

/-- Admitted encodings cannot identify distinct values (production `encode_injective`). -/
theorem encodeP_injective {t : PTy} {v w : Val} {j : Json}
    (hv : encodeP t v = some j) (hw : encodeP t w = some j) : v = w :=
  Option.some.inj ((decodeP_of_encodeP hv).symm.trans (decodeP_of_encodeP hw))

/-- The codec's half of `encode_sub`: membership at both types and one layout give one encoding. -/
theorem encodeP_sub_of_member {s t : PTy} {v : Val} (hs : hasTyP v s [] = true)
    (ht : hasTyP v t [] = true) (hl : layoutP s = layoutP t) : encodeP t v = encodeP s v := by
  unfold encodeP
  rw [if_pos hs, if_pos ht, hl]

/-- **`encode_sub` on the copy**: the production statement, with membership's monotonicity
(`hasTy_sub`, seat P's law at the new forms) as its one hypothesis. -/
theorem encodeP_sub (sub : PTy → PTy → Bool)
    (hasTy_sub : ∀ a b w, sub a b = true → hasTyP w a [] = true → hasTyP w b [] = true)
    {s t : PTy} {v : Val} (hsub : sub s t = true) (hv : hasTyP v s [] = true)
    (hl : layoutP s = layoutP t) : encodeP t v = encodeP s v :=
  encodeP_sub_of_member hv (hasTy_sub s t v hsub hv) hl

/-! ## §11 `N_J` and the exact decoder (proved) -/

/-- Insert by key after every entry not greater (a stable sort: repeats keep their order). -/
def insJ (p : String × Json) : List (String × Json) → List (String × Json)
  | [] => [p]
  | q :: qs => if nameLt p.1 q.1 = true then p :: q :: qs else q :: insJ p qs

def sortJ (es : List (String × Json)) : List (String × Json) := es.foldl (fun acc p => insJ p acc) []

mutual
/-- The named key-order normaliser `N_J`: every object's entries sorted by key bytes, stably. -/
def NJ : Json → Json
  | .arr xs => .arr (NJList xs)
  | .obj es => .obj (sortJ (NJEntries es))
  | j => j
def NJList : List Json → List Json
  | [] => []
  | x :: xs => NJ x :: NJList xs
def NJEntries : List (String × Json) → List (String × Json)
  | [] => []
  | (k, x) :: es => (k, NJ x) :: NJEntries es
end

/-- The decoder guarded by the encoder's image modulo `N_J` (probe C's `decodeExact`). -/
def decodeExactP (t : PTy) (j : Json) : Option Val :=
  (decodeP t j).filter (fun v => decide ((encodeP t v).map NJ = some (NJ j)))

/-- **Exactness modulo `N_J`** (K2's third law). -/
theorem decodeExactP_exact {t : PTy} {j : Json} {v : Val} (h : decodeExactP t j = some v) :
    ∃ j', encodeP t v = some j' ∧ NJ j' = NJ j := by
  unfold decodeExactP at h
  rw [Option.filter_eq_some_iff] at h
  have hg := of_decide_eq_true h.2
  cases hw : encodeP t v with
  | none => rw [hw] at hg; exact nomatch hg
  | some j' =>
    rw [hw, Option.map_some, Option.some.injEq] at hg
    exact ⟨j', rfl, hg⟩

/-- **The retraction is kept** (K2's second law). -/
theorem decodeExactP_retract {t : PTy} {v : Val} {j : Json} (h : encodeP t v = some j) :
    decodeExactP t j = some v := by
  unfold decodeExactP
  rw [decodeP_of_encodeP h, Option.filter_eq_some_iff]
  refine ⟨rfl, decide_eq_true ?_⟩
  rw [h, Option.map_some]

/-- The guard only refuses. -/
theorem decodeExactP_le {t : PTy} {j : Json} {v : Val} (h : decodeExactP t j = some v) :
    decodeP t j = some v := by
  unfold decodeExactP at h
  rw [Option.filter_eq_some_iff] at h
  exact h.1

/-! ## §12 Static layout preparation, the Schema side (proved; the review's bound) -/

theorem sortedF_iff_names {α : Type} (l : List (String × α)) :
    SortedF l ↔ (l.map (·.1)).Pairwise (fun a b => nameLt a b = true) := by
  unfold SortedF
  rw [List.pairwise_map]

theorem sortedF_transfer {α β : Type} (xs : List (String × α)) (ys : List (String × β))
    (h : xs.map (·.1) = ys.map (·.1)) (hs : SortedF ys) : SortedF xs := by
  rw [sortedF_iff_names, h]
  exact (sortedF_iff_names ys).mp hs

theorem fieldEncoders_names (fs : List (String × PTy)) :
    (fieldEncoders fs).map (·.1) = fs.map (·.1) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [fieldEncoders, List.map_cons, ih]

theorem fieldDecoders_names (strict : Bool) (fs : List (String × PTy)) :
    (fieldDecoders strict fs).map (·.1) = fs.map (·.1) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [fieldDecoders, List.map_cons, ih]

theorem fieldCheckers_names (fs : List (String × PTy)) (al : List String) :
    (fieldCheckers fs al).map (·.1) = fs.map (·.1) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [fieldCheckers, List.map_cons, ih]

/-- **Prepared once, no sort per value**: on a record whose fields are already in canonical order
(what `normalize` hands the Schema arms), the codec's and membership's sorts are the identity,
so an evaluator prepared at the type agrees with the sorting arm on every value. An
evaluator-agreement fact for the Schema side only; the term-level layout is seat R's. -/
theorem prepared_agrees (fs : List (String × PTy)) (al : List String) (strict : Bool)
    (h : SortedF fs) :
    canonF (fieldEncoders fs) = fieldEncoders fs ∧
      canonF (fieldDecoders strict fs) = fieldDecoders strict fs ∧
      canonF (fieldCheckers fs al) = fieldCheckers fs al :=
  ⟨canonF_of_sorted _ (sortedF_transfer _ fs (fieldEncoders_names fs) h),
   canonF_of_sorted _ (sortedF_transfer _ fs (fieldDecoders_names strict fs) h),
   canonF_of_sorted _ (sortedF_transfer _ fs (fieldCheckers_names fs al) h)⟩

/-! ## §13 The codec per form, and row 128 at the new forms (tested; red controls on production) -/

def jobj (es : List (String × Json)) : Json := .obj es
def jn (n : Nat) : Json := Arch.Json.ofNat n
/-- A record value (row 165): its names and its slots, in canonical order. -/
def rv (fields : List (String × Val)) : Val :=
  .ctor 0 [.list (fields.map (fun f => .str f.1)), .list (fields.map (·.2))]

-- records: an object keyed by name, the exact field set in any order
def vAB : Val := rv [("a", intVal 1), ("b", .str "x")]
#guard encodeP rAB vAB = some (jobj [("a", jn 1), ("b", .str "x")])
#guard decodeP rAB (jobj [("b", .str "x"), ("a", jn 1)]) = some vAB
#guard decodeP rAB (jobj [("a", jn 1), ("b", .str "x"), ("c", .bool true)]) = none
#guard decodeP rAB (jobj [("a", jn 1)]) = none
#guard decodeP rAB (jobj [("a", jn 1), ("a", jn 1), ("b", .str "x")]) = none
-- the type's written order does not move the layout: the canonical read
#guard encodeP (.record [("b", .string), ("a", .int)]) vAB = some (jobj [("a", jn 1), ("b", .str "x")])
#guard NJ (jobj [("b", .str "x"), ("a", jn 1)]) = NJ (jobj [("a", jn 1), ("b", .str "x")])
#guard decodeExactP rAB (jobj [("b", .str "x"), ("a", jn 1)]) = some vAB
-- optional keys: absent is `none`; rc.112 `optional`'s `null` for an explicit undefined refuses
#guard encodeP rOpt (rv [("a", .none), ("b", .str "x")]) = some (jobj [("b", .str "x")])
#guard encodeP rOpt (rv [("a", .some (intVal 1)), ("b", .str "x")]) =
  some (jobj [("a", jn 1), ("b", .str "x")])
#guard decodeP rOpt (jobj [("b", .str "x")]) = some (rv [("a", .none), ("b", .str "x")])
#guard decodeP rOpt (jobj [("a", .null), ("b", .str "x")]) = none
-- maps: keys sorted in the value; a repeated key refuses (rc.112's text route keeps the last)
def vMap : Val := .list [.list [.str "a", intVal 1], .list [.str "b", intVal 2]]
#guard encodeP rMap vMap = some (jobj [("a", jn 1), ("b", jn 2)])
#guard decodeP rMap (jobj [("b", jn 2), ("a", jn 1)]) = some vMap
#guard decodeP rMap (jobj [("a", jn 1), ("a", jn 2)]) = none
#guard encodeP rMap (.list [.list [.str "b", intVal 2], .list [.str "a", intVal 1]]) = none
#guard encodeP rMap (.list []) = some (jobj [])
-- tagged unions: the branch by its `_tag` literal
def vA : Val := rv [("_tag", .str "A"), ("x", intVal 1)]
#guard encodeP rTU vA = some (jobj [("_tag", .str "A"), ("x", jn 1)])
#guard decodeP rTU (jobj [("x", jn 1), ("_tag", .str "A")]) = some vA
#guard decodeP rTU (jobj [("_tag", .str "B"), ("y", .str "s")]) = some (rv [("_tag", .str "B"), ("y", .str "s")])
#guard decodeP rTU (jobj [("_tag", .str "A"), ("y", .str "s")]) = none
-- int (stage 5): signed exact binary64; the domain differs from rc.112's `isInt` at both ends
#guard encodeP .int (intVal (-15)) = some (intJson (-15))
#guard decodeP .int (intJson (-15)) = some (intVal (-15))
#guard decodeP .int (.number Float64.negZero) = none
#guard decodeP .int (jn (2 ^ 53)) = some (intVal (2 ^ 53))
#guard Effect4.Schema.decode .nat (jn (2 ^ 53)) = some (.nat (2 ^ 53))
#guard Effect4.Schema.decode .nat (.number Float64.negZero) = none
-- (i) row 128's witness: RED CONTROL on the production decoder, then the copy
def overlapEE : PTy := .union (.except .nat .nat) (.exitOf .nat .nat)
def jFailure : Json := jobj [("_tag", .str "Failure"), ("failure", jn 1)]
def jSuccess : Json := jobj [("_tag", .str "Success"), ("value", jn 1)]
#guard Effect4.Schema.decode (.union (.except .nat .nat) (.exitOf .nat .nat)) jSuccess =
  some (.ctor 0 [.nat 1])
#guard decodeP overlapEE jSuccess = none
#guard decodeP overlapEE jFailure = some (.ctor 0 [.nat 1])
-- (ii) under row 119's positional clause a record and a tagged union share an image (one value,
-- two record types: the red control `red_sharedImage`); under row 165 the names tell them apart
def tagA : PTy := tagged "A" [("x", .nat)]
def recAB : PTy := .record [("a", .string), ("b", .nat)]
def vShared : Val := .ctor 0 [.str "A", .nat 1]
#guard posRecordFits vShared [("_tag", .lit "A"), ("x", .nat)] && posRecordFits vShared [("a", .string), ("b", .nat)]
def vNamedA : Val := rv [("_tag", .str "A"), ("x", .nat 1)]
def vNamedAB : Val := rv [("a", .str "A"), ("b", .nat 1)]
#guard hasTyP vNamedA tagA [] && !hasTyP vNamedA recAB [] && hasTyP vNamedAB recAB [] && !hasTyP vNamedAB tagA []
#guard decodeP (.union tagA recAB) (jobj [("a", .str "A"), ("b", jn 1)]) = some vNamedAB
#guard decodeP (.union tagA recAB) (jobj [("_tag", .str "A"), ("x", jn 1)]) = some vNamedA
#guard encodeP (.union tagA recAB) vNamedAB = some (jobj [("a", .str "A"), ("b", jn 1)])
-- (iii) a one-field record no longer shares `ctor 0 [v]` with Result's failure or Exit's success
def rx : PTy := .record [("x", .nat)]
#guard hasTyP (.ctor 0 [.nat 1]) (.except .nat .nat) [] && !hasTyP (.ctor 0 [.nat 1]) rx []
  && hasTyP (rv [("x", .nat 1)]) rx [] && !hasTyP (rv [("x", .nat 1)]) (.except .nat .nat) []
#guard decodeP (.union (.except .nat .nat) rx) (jobj [("x", jn 1)]) = some (rv [("x", .nat 1)])
#guard decodeP (.union rx (.except .nat .nat)) jFailure = some (.ctor 0 [.nat 1])
-- (iv) `Int`'s generated image overlaps Result's: a Result failure leaves the union's image
#guard decodeP (.union .int (.except .nat .nat)) jFailure = none
#guard encodeP (.union .int (.except .nat .nat)) (.ctor 0 [.nat 1]) = some (jn 1)
-- (v) one JSON image, two values: the encoder refuses the second (S-3's existing clause)
def recSuccess : PTy := .record [("_tag", .lit "Success"), ("value", .nat)]
#guard encodeP (.union (.exitOf .nat .nat) recSuccess) (rv [("_tag", .str "Success"), ("value", .nat 1)]) = none
#guard encodeP (.union (.exitOf .nat .nat) recSuccess) (.ctor 0 [.nat 1]) = some jSuccess
-- tuples: an array of the items, exact arity; a list beside a tuple selects by arity
def vTup : Val := .list [intVal 1, .str "x", .bool true]
#guard encodeP tup3 vTup = some (.arr [jn 1, .str "x", .bool true])
#guard decodeP tup3 (.arr [jn 1, .str "x", .bool true]) = some vTup
#guard decodeP tup3 (.arr [jn 1, .str "x"]) = none
#guard decodeP (.union (.tuple [.int, .int, .int]) (.list .int)) (.arr [jn 1, jn 2]) =
  some (.list [intVal 1, intVal 2])
#guard decodeP (.union (.list .int) (.tuple [.int, .int, .int])) (.arr [jn 1, jn 2, jn 3]) =
  some (.list [intVal 1, intVal 2, intVal 3])
-- the codec refuses `app`, `null`, `undefined`, `number`, `bytes` by name (`isSupported`): owed
#guard [stream, .null, .undefined, .number, .bytes].all (fun t => !isSupportedP t)
#guard encodeP .bytes (.bytes [1, 2]) = none
-- on every positive input above, the guarded decoder equals the unguarded one (tested): the
-- canonical-branch check and the strict field set already make these reads exact
def exactOn (t : PTy) (j : Json) : Bool := decodeExactP t j == decodeP t j
#guard [(rAB, jobj [("b", .str "x"), ("a", jn 1)]), (rOpt, jobj [("b", .str "x")]),
  (rMap, jobj [("b", jn 2), ("a", jn 1)]), (rTU, jobj [("x", jn 1), ("_tag", .str "A")]),
  (.int, intJson (-15)), (overlapEE, jFailure),
  (.union tagA recAB, jobj [("_tag", .str "A"), ("x", jn 1)]),
  (.union tagA recAB, jobj [("a", .str "A"), ("b", jn 1)]),
  (.union (.except .nat .nat) rx, jobj [("x", jn 1)]),
  (tup3, .arr [jn 1, .str "x", .bool true])].all (fun p => exactOn p.1 p.2)

/-! ## §13b The row adapter beside the codec (route A, row 122): probe R's paired control (tested) -/

def userTy : PTy := .record [("id", .nat), ("name", .string)]
def wider : Json := jobj [("id", jn 2), ("name", .str "bob"), ("role", .str "member")]
def bob : Val := rv [("id", .nat 2), ("name", .str "bob")]
-- the paired control: the adapter strips the undeclared key, the codec refuses it
#guard adaptP userTy wider = some bob && decodeP userTy wider = none
-- the adapter is a projection, not exact: the adapted value's encoding has two keys, `wider` three
#guard encodeP userTy bob = some (jobj [("id", jn 2), ("name", .str "bob")])
-- both refuse a missing and a duplicated declared key; a duplicated undeclared key: adapter drops, codec refuses
#guard adaptP userTy (jobj [("id", jn 2)]) = none && decodeP userTy (jobj [("id", jn 2)]) = none
#guard adaptP userTy (jobj [("id", jn 2), ("id", jn 3), ("name", .str "b")]) = none
def dupUndeclared : Json := jobj [("id", jn 2), ("name", .str "b"), ("x", .null), ("x", .null)]
#guard adaptP userTy dupUndeclared = some (rv [("id", .nat 2), ("name", .str "b")]) && decodeP userTy dupUndeclared = none
-- stripped at depth by the adapter, refused at depth by the codec
def nestedTy : PTy := .record [("user", userTy)]
#guard adaptP nestedTy (jobj [("user", wider)]) = some (rv [("user", bob)]) && decodeP nestedTy (jobj [("user", wider)]) = none
-- probe R's `codec_sub_adapt` on union-free types (tested on the codec's positive inputs above)
#guard [(rAB, jobj [("b", .str "x"), ("a", jn 1)]), (rOpt, jobj [("b", .str "x")]),
  (rMap, jobj [("b", jn 2), ("a", jn 1)]), (tup3, .arr [jn 1, .str "x", .bool true]),
  (userTy, jobj [("name", .str "bob"), ("id", jn 2)])].all (fun p => adaptP p.1 p.2 == decodeP p.1 p.2)
-- **but not at a union whose earlier branch names a subset of a later one's**: the adapter strips
-- into the earlier branch (as rc.112's default `anyOf` does, question 2 E7h), the codec answers the
-- later; `codec_sub_adapt` holds on union-free types and needs a premise at unions
def subsetUnion : PTy := .union (.record [("a", .nat)]) (.record [("a", .nat), ("b", .nat)])
def jAB : Json := jobj [("a", jn 1), ("b", jn 2)]
#guard decodeP subsetUnion jAB = some (rv [("a", .nat 1), ("b", .nat 2)])
#guard adaptP subsetUnion jAB = some (rv [("a", .nat 1)])

/-! ## §14 Red controls: each claim is false, and `#guard_msgs` asserts its `#guard` fails -/
/-- RED: today's production decoder is exact at row 128's witness (it decodes the `Success` image). -/
def red_productionExact : Bool := Effect4.Schema.decode (.union (.except .nat .nat) (.exitOf .nat .nat)) jSuccess == none
/--
error: Expression
  red_productionExact
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_productionExact

/-- RED: the adapter and the codec agree wherever the codec answers (`codec_sub_adapt` at a union of nested field sets). -/
def red_codecSubAdaptUnion : Bool := adaptP subsetUnion jAB == decodeP subsetUnion jAB
/--
error: Expression
  red_codecSubAdaptUnion
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_codecSubAdaptUnion

/-- RED: under row 119's positional clause no value fits two record types (it does: positional values carry no names; row 165's named values are the repair). -/
def red_sharedImage : Bool :=
  !(posRecordFits vShared [("_tag", .lit "A"), ("x", .nat)] && posRecordFits vShared [("a", .string), ("b", .nat)])
/--
error: Expression
  red_sharedImage
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_sharedImage

/-- RED: today's `ofSchema` refuses `number >= 5` (it reads it as `nat` by the check's id). -/
def red_ge5 : Bool := Effect4.Schema.Bridge.ofSchema ge5 == none
/--
error: Expression
  red_ge5
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_ge5

/-- RED: the handle named `effect/schema/TypeParameter` round-trips (the `var` repair takes the name: hence `wf`). -/
def red_typeParameter : Bool := readsAs (schema (.handle "effect/schema/TypeParameter")) (.handle "effect/schema/TypeParameter")
/--
error: Expression
  red_typeParameter
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_typeParameter

/-- RED: a record with a repeated name round-trips (it does not: hence the formation refusal). -/
def red_repeat : Bool := readsAs (schema (.record [("a", .nat), ("a", .string)])) (.record [("a", .nat), ("a", .string)])
/--
error: Expression
  red_repeat
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_repeat

/-- RED: the writer's nested union equals rc.112's flat one without `N_S`. -/
def red_flatWithoutNS : Bool := schema lit3 == flat3
/--
error: Expression
  red_flatWithoutNS
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_flatWithoutNS

/-- RED: the bridge-level `N_S` (no property sort) identifies a permuted struct with the canonical
writing (it does not: a statement against the normalizing writer would need `N_Sp`). -/
def red_unsortedNS : Bool := N_S (schema rAB) == N_S permutedBA
/--
error: Expression
  red_unsortedNS
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_unsortedNS

/-- RED: the strict codec admits rc.112 `optional`'s `null` for an explicit undefined. -/
def red_optionalNull : Bool := (decodeP rOpt (jobj [("a", .null), ("b", .str "x")])).isSome
/--
error: Expression
  red_optionalNull
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_optionalNull

/-- RED: the copy's `int` decoder refuses 2^53 as rc.112's `isInt` does. -/
def red_int2p53 : Bool := decodeP .int (jn (2 ^ 53)) == none
/--
error: Expression
  red_int2p53
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_int2p53

end SeatS.K2

#print axioms SeatS.K2.PTy.ind'
#print axioms SeatS.K2.nameLt_irrefl
#print axioms SeatS.K2.nameLt_trans
#print axioms SeatS.K2.nameLt_total
#print axioms SeatS.K2.insF_last
#print axioms SeatS.K2.foldl_insF_of_sorted
#print axioms SeatS.K2.canonF_of_sorted
#print axioms SeatS.K2.insF_map
#print axioms SeatS.K2.canonF_map
#print axioms SeatS.K2.readProps_cons_plain
#print axioms SeatS.K2.readProps_cons_opt
#print axioms SeatS.K2.readProps_schemaProps
#print axioms SeatS.K2.rOption
#print axioms SeatS.K2.rRef
#print axioms SeatS.K2.rResult
#print axioms SeatS.K2.rFiber
#print axioms SeatS.K2.rDeferred
#print axioms SeatS.K2.rCause
#print axioms SeatS.K2.rExit
#print axioms SeatS.K2.rUint8
#print axioms SeatS.K2.readElems_schemaElems
#print axioms SeatS.K2.readArgs_schemaList
#print axioms SeatS.K2.retract
#print axioms SeatS.K2.ofSchemaL_schema
#print axioms SeatS.K2.ofSchemaExact_exact
#print axioms SeatS.K2.ofSchemaExact_le
#print axioms SeatS.K2.ofSchemaExact_schema
#print axioms SeatS.K2.encodeP_eq_some
#print axioms SeatS.K2.decodeP_of_encodeP
#print axioms SeatS.K2.hasTy_decodeP
#print axioms SeatS.K2.adapt_memberP
#print axioms SeatS.K2.encodeP_injective
#print axioms SeatS.K2.encodeP_sub_of_member
#print axioms SeatS.K2.encodeP_sub
#print axioms SeatS.K2.decodeExactP_exact
#print axioms SeatS.K2.decodeExactP_retract
#print axioms SeatS.K2.decodeExactP_le
#print axioms SeatS.K2.sortedF_iff_names
#print axioms SeatS.K2.sortedF_transfer
#print axioms SeatS.K2.fieldEncoders_names
#print axioms SeatS.K2.fieldDecoders_names
#print axioms SeatS.K2.fieldCheckers_names
#print axioms SeatS.K2.prepared_agrees
