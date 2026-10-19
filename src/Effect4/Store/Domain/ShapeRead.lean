module

public import Effect4.Store.Domain.Canonical
public import Effect4.Data.Ascii
meta import Effect4.Data.Json
meta import Effect4.Store.Carrier.Digest
meta import Effect4.Store.Carrier.Val

/-!
# Store.ShapeRead — reading a canonical carrier back from its cases print

`ShapeDoc.print` (`Store/Domain/Shape.lean`) writes a value tree as JSON, the names from the shape
and the structure from the value, every sum by its cases. This module reads that JSON back, under
the same shape, and normalises an agent's JSON into it. The public print, each list an array, is
`Canonical.print` (`Store/Domain/ShapeJson.lean`; decisions row 418, D2).

**The reader accepts only the cases print.** Each case checks that the JSON is what the
cases print writes for the value it reads: a number is the binary64 of a natural, hex is lowercase
and exact, a field list is the shape's in order, a case name names the case its tag prints. So
whatever reads is that value's print, with no fragment condition (`readIn_exact`,
`Laws/Store/ShapeRead.lean`).

**The round trip has a fragment.** JSON numbers are binary64, so a natural above 2^53 prints
inexactly. An option is invisible in JSON (`some a` prints as `a`), so an option of a shape that
prints `null` is ambiguous. On values with neither, reading the print gives the value back.

**No budget bounds a reading.** An option layer reads the same JSON value under the option's
item, so a definition that returns to its own name through options alone would unwrap forever. A
reading therefore records the names it has unfolded since the last JSON node (`seen`), and a layer
that meets one of them again refuses: the layers return to it before a node, so the shape there
holds only options of options, which print `null`. The readers are well founded on the JSON
value's size, then on the definitions whose names `seen` lacks (`unseenDefs`), then on the shape's
size, as the membership checker under a table is (`Val.hasTyIn`, `Program/TyDecls.lean`).

**An agent's JSON reads through the profile.** JSON whose objects come in any order, and whose
lists may be arrays, is read by the located reader of `Store/Domain/ShapeJson.lean`, which refuses
at a place, and is exact modulo this module's normaliser (`ShapeDoc.order`).
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64)

/-- The natural a positive binary64 integer datum stands for, by its exponent and significand; a
candidate only, which `natOfBinary64` checks. -/
def natCandidate (bits : UInt64) : Nat :=
  let b := bits.toNat
  let e := b / 2 ^ 52
  let sig := b % 2 ^ 52 + 2 ^ 52
  if b = 0 then 0
  else if 1023 + 52 ≤ e then sig * 2 ^ (e - (1023 + 52)) else sig / 2 ^ ((1023 + 52) - e)

/-- **The natural a binary64 datum spells**, where the datum is a non-negative finite binary64
(a pattern below `binary64Infinity`) and is the binary64 of that natural (`binary64OfNat`). Its
domain is the naturals binary64 holds exactly: below 2^1024, with at most 53 significant bits,
every natural up to 2^53 among them (the MCP face's profile is the naturals up to 2^53). A
negative or non-finite datum, a fraction and an inexact spelling read as none, so the natural
read is the number a binary64 host reads (`natOfBinary64_finite`). -/
def natOfBinary64 (bits : UInt64) : Option Nat :=
  if bits.toNat < Effect4.Arch.binary64Infinity ∧
      Effect4.Arch.binary64OfNat (natCandidate bits) = bits then
    some (natCandidate bits)
  else none

/-- **Bytes from their hex spelling**, where the spelling is the canonical one (`hexString`). The
spelling is read through its UTF-8 bytes (`Data.Ascii.bytesOf`), since a hex digit is one ASCII
byte: a traversal of the `String` as characters would reach `Classical.choice` through Lean's UTF-8
decoding, and `ByteArray.toList` is no primitive of the OCaml route. -/
def canonicalHex? (h : String) : Option Bytes :=
  (bytesOfHexCodes ((Effect4.Data.Ascii.bytesOf h).map (·.toNat))).bind fun d =>
    if hexString d = h then some d else none

/-- **The wire tag of a case name**, where the tag's case is that name: the first case with the
name, checked against `caseAt`, which the printer reads. -/
def tagOfName (name : String) (cases : List (String × Nat × List (String × Shape))) :
    Option (Nat × List (String × Shape)) :=
  (cases.find? fun c => decide (c.1 = name)).bind fun (_, tag, _) =>
    match caseAt tag cases with
    | some (name', fields) => if name' = name then some (tag, fields) else none
    | none => none

/-- The entry of an object with a name: the first. -/
def entryOf (name : String) : List (String × Json) → Option Json
  | [] => none
  | (n, j) :: rest => if n = name then some j else entryOf name rest

/-! ## The names unfolded since the last node -/

/-- **The definitions whose names `seen` does not hold**: the measure of the option layers a
reading passes before a JSON node. `TyDecls.unseen` (`Program/TyExpand.lean`) is the same measure
over a type table. -/
def unseenDefs (defs : List (String × Shape)) (seen : List String) : Nat :=
  (defs.filter fun d => !seen.contains d.1).length

/-- **The measure falls** when `seen` gains a name that the table binds. A step of
`optionLayer?_lt`. -/
theorem unseenDefs_cons_lt {defs : List (String × Shape)} {seen : List String} {n : String}
    {s : Shape} (hm : (n, s) ∈ defs) (hn : seen.contains n = false) :
    unseenDefs defs (n :: seen) < unseenDefs defs seen := by
  unfold unseenDefs
  have hfilter : defs.filter (fun d => !(n :: seen).contains d.1) =
      (defs.filter fun d => !seen.contains d.1).filter fun d => !(n :: seen).contains d.1 := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro d _
    cases h' : (n :: seen).contains d.1 with
    | true => rfl
    | false =>
      have hs : seen.contains d.1 = false := by
        rw [List.contains_cons, Bool.or_eq_false_iff] at h'
        exact h'.2
      rw [hs]
      rfl
  rw [hfilter, List.length_filter_lt_length_iff_exists]
  refine ⟨(n, s), List.mem_filter.mpr ⟨hm, ?_⟩, ?_⟩
  · rw [hn]
    rfl
  · rw [List.contains_cons, beq_iff_eq.mpr rfl, Bool.true_or, Bool.not_true]
    exact Bool.false_ne_true

/-- **One option layer of a reading**, where the shape's head is an option: its item, and the
names unfolded after the layer, where a name that `s` unfolds joins `seen`. None where the head is
no option, or where `seen` holds the name already: the layers returned to it before a JSON node,
so they never reach one. -/
def optionLayer? (defs : List (String × Shape)) (s : Shape) (seen : List String) :
    Option (Shape × List String) :=
  match headShape defs s with
  | .option item =>
    match s with
    | .named n => if seen.contains n then none else some (item, n :: seen)
    | _ => some (item, seen)
  | _ => none

/-- **One option layer falls in the measure**: a layer under a name unfolds a name that `seen`
lacks, and a layer under an `option` shape reads its item, which is smaller. The termination
step of every reader that passes option layers. -/
theorem optionLayer?_lt {defs : List (String × Shape)} {s item : Shape}
    {seen seen' : List String} (h : optionLayer? defs s seen = some (item, seen')) :
    Prod.Lex (· < ·) (· < ·) (unseenDefs defs seen', sizeOf item)
      (unseenDefs defs seen, sizeOf s) := by
  unfold optionLayer? at h
  split at h
  · rename_i item' hs
    cases s with
    | named n =>
      cases hn : seen.contains n with
      | true =>
        simp only [hn, ↓reduceIte] at h
        cases h
      | false =>
        simp only [hn, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        have hm : (n, Shape.option item') ∈ defs := by
          unfold headShape candidates at hs
          dsimp only at hs
          split at hs
          · rename_i s' rest hl'
            subst hs
            exact (mem_lookupAll n _ defs).mp (hl' ▸ List.mem_cons_self)
          · cases hs
        obtain ⟨rfl, rfl⟩ := h
        exact Prod.Lex.left _ _ (unseenDefs_cons_lt hm hn)
    | option i =>
      cases h
      cases hs
      exact Prod.Lex.right _ (by simp only [Shape.option.sizeOf_spec]; omega)
    | _ => cases hs
  · cases h

/-- An object's entry is smaller than its entries. The termination step of the readers that read
a field by its name. -/
theorem sizeOf_entryOf_lt {name : String} :
    ∀ {entries : List (String × Json)} {j : Json}, entryOf name entries = some j →
      sizeOf j < sizeOf entries
  | [], _, h => by cases h
  | (n, j') :: rest, j, h => by
    unfold entryOf at h
    split at h
    · cases h
      simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
      omega
    · have := sizeOf_entryOf_lt h
      simp only [List.cons.sizeOf_spec]
      omega

/-! ## The strict reader -/

mutual
/-- **Read a value tree under a shape** from its cases print; none where the JSON is not the
cases print of a value fitting the shape's head. An option layer reads the same value under
the item, and refuses a name it unfolded since the last JSON node (`optionLayer?`). -/
def readIn (defs : List (String × Shape)) (seen : List String) (s : Shape) (j : Json) :
    Option Val :=
  match headShape defs s, j with
  | .unit, .null => some .unit
  | .option _, .null => some .none
  | .option _, j' =>
    match _hl : optionLayer? defs s seen with
    | some (item, seen') => (readIn defs seen' item j').map .some
    | none => none
  | .bool, .bool b => some (.bool b)
  | .nat, .number x => (natOfBinary64 x.bits).map .nat
  | .string, .str t => some (.str t)
  | .bytes, .str h => (canonicalHex? h).map .bytes
  | .digest, .str h => (canonicalHex? h).map .bytes
  | .list item, .arr js => (readList defs item js).map .list
  | .pair f g, .arr [a, b] =>
    (readIn defs [] f a).bind fun x => (readIn defs [] g b).map fun y => .pair x y
  | .struct _ fields, .obj entries => (readFields defs fields entries).map (.ctor 0)
  | .sum _ cases, .str name =>
    if allNullary cases then
      (tagOfName name cases).bind fun (tag, fields) =>
        if fields.isEmpty then some (.ctor tag []) else none
    else none
  | .sum _ cases, .obj (("_tag", .str name) :: entries) =>
    if allNullary cases then none
    else (tagOfName name cases).bind fun (tag, fields) =>
      (readFields defs fields entries).map (.ctor tag)
  | .ref k, .str h => (canonicalHex? h).map (.ref k.byte)
  | .anyRef, .obj [("kind", .str kn), ("address", .str h)] =>
    (Kind.ofName? kn).bind fun k =>
      if kindJson k.byte = .str kn then (canonicalHex? h).map (.ref k.byte) else none
  | _, _ => none
termination_by (sizeOf j, unseenDefs defs seen, sizeOf s)
decreasing_by
  · exact Prod.Lex.right _ (optionLayer?_lt _hl)
  all_goals
    apply Prod.Lex.left
    simp only [Json.arr.sizeOf_spec, Json.obj.sizeOf_spec, List.cons.sizeOf_spec,
      Prod.mk.sizeOf_spec]
    omega

/-- Read the elements of a list, each under the item shape. -/
def readList (defs : List (String × Shape)) (item : Shape) : List Json → Option (List Val)
  | [] => some []
  | j :: js => (readIn defs [] item j).bind fun x => (readList defs item js).map (x :: ·)
termination_by js => (sizeOf js, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega

/-- Read the fields of a struct or a case: the shape's names, in its order, and no other. -/
def readFields (defs : List (String × Shape)) :
    List (String × Shape) → List (String × Json) → Option (List Val)
  | [], [] => some []
  | (k, s) :: fields, (k', j) :: entries =>
    if k' = k then
      (readIn defs [] s j).bind fun x => (readFields defs fields entries).map (x :: ·)
    else none
  | _, _ => none
termination_by _ entries => (sizeOf entries, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    omega
end

/-! ## The list rule: a list family's JSON is an array

`ts/eff/eff.gen.ts` types the program's four lists (`Terms`, `Stmts`, `Effs`, `LayerTerms`) as
arrays, and its Effect Schema codecs read them so. The cases print writes them case by case,
`{"_tag":"cons","head":…,"tail":…}`. So the normaliser below reads either, and the public print
writes arrays (`Canonical.print`, through `ShapeDoc.printTree`, `Store/Domain/ShapeJson.lean`).
The shape, so the canonical bytes and every digest, does not change. -/

/-- **The list rule's parts**: a sum whose cases are exactly `nil`, with no field, and `cons`, with
the fields `head` and `tail`, under two different tags. Where the rule holds: the two tags, the
head's shape and the tail's shape. -/
def listParts? (cases : List (String × Nat × List (String × Shape))) :
    Option (Nat × Nat × Shape × Shape) :=
  match cases with
  | [(n0, t0, []), (n1, t1, [(k0, head), (k1, tail)])] =>
    if n0 = "nil" ∧ n1 = "cons" ∧ k0 = "head" ∧ k1 = "tail" ∧ t0 ≠ t1 then some (t0, t1, head, tail)
    else none
  | _ => none

/-- **The list rule**: the item's shape, where the rule holds (`listParts?`). -/
def listItem? (cases : List (String × Nat × List (String × Shape))) : Option Shape :=
  (listParts? cases).map fun parts => parts.2.2.1

/-- The empty list's cases print: the `nil` case. -/
def nilObject : Json := .obj [("_tag", .str "nil")]

mutual
/-- **Put each object's entries in its shape's field order**, under a shape: JSON objects are
unordered, and the cases print orders a structure's fields, and a case's after its `_tag`, by
declaration. The named normaliser of the JSON form: the profile's reader, which reads an agent's
JSON in any order, is exact modulo it (`Store/Domain/ShapeJson.lean`). An array under a list
family (`listParts?`) becomes the family's cases print (`orderSpine`): each element ordered
under the head's shape of its cell, the rest under the tail field's shape, which names the family
again. An object that lacks a field, or holds another, is left as it is, and reads as none. An
option layer orders the same value under the item; a layer that returns to a name it unfolded
since the last JSON node (`optionLayer?`) leaves the value as it is. -/
def orderIn (defs : List (String × Shape)) (seen : List String) (s : Shape) (j : Json) : Json :=
  match headShape defs s, j with
  | .option _, .null => .null
  | .option _, j' =>
    match _hl : optionLayer? defs s seen with
    | some (item, seen') => orderIn defs seen' item j'
    | none => j'
  | .list item, .arr js => .arr (orderList defs item js)
  | .pair f g, .arr [a, b] => .arr [orderIn defs [] f a, orderIn defs [] g b]
  | .sum _ cases, .arr js =>
    match listParts? cases with
    | some (_, _, item, tail) => orderSpine defs item tail js
    | none => .arr js
  | .struct _ fields, .obj entries =>
    match orderFields defs fields entries with
    | some ordered => if ordered.length = entries.length then .obj ordered else .obj entries
    | none => .obj entries
  | .sum _ cases, .obj entries =>
    match entryOf "_tag" entries with
    | some (.str name) =>
      match tagOfName name cases with
      | some (_, fields) =>
        match orderFields defs fields entries with
        | some ordered =>
          if ordered.length + 1 = entries.length then .obj (("_tag", .str name) :: ordered)
          else .obj entries
        | none => .obj entries
      | none => .obj entries
    | _ => .obj entries
  | _, j' => j'
termination_by (sizeOf j, unseenDefs defs seen, sizeOf s)
decreasing_by
  · exact Prod.Lex.right _ (optionLayer?_lt _hl)
  all_goals
    apply Prod.Lex.left
    simp only [Json.arr.sizeOf_spec, Json.obj.sizeOf_spec, List.cons.sizeOf_spec]
    omega

/-- Order the elements of a list, each under the item shape. -/
def orderList (defs : List (String × Shape)) (item : Shape) : List Json → List Json
  | [] => []
  | j :: js => orderIn defs [] item j :: orderList defs item js
termination_by js => (sizeOf js, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega

/-- The shape's fields, each looked up by name among the entries and ordered under its shape;
none where an entry is missing. -/
def orderFields (defs : List (String × Shape)) :
    List (String × Shape) → List (String × Json) → Option (List (String × Json))
  | [], _ => some []
  | (n, s) :: fields, entries =>
    match _he : entryOf n entries with
    | some j => (orderFields defs fields entries).map ((n, orderIn defs [] s j) :: ·)
    | none => none
termination_by fields entries => (sizeOf entries, 0, fields.length)
decreasing_by
  · exact Prod.Lex.left _ _ (sizeOf_entryOf_lt _he)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))

/-- A list family's array, from one element on, as its cases print: `nil`, or `cons` of the
element ordered under the cell's head shape and the rest under its tail shape, where that shape is
a list family again. A rest whose shape is no list family is left as an array, and reads as
none. -/
def orderSpine (defs : List (String × Shape)) (item tail : Shape) : List Json → Json
  | [] => nilObject
  | j :: js =>
    .obj [("_tag", .str "cons"), ("head", orderIn defs [] item j),
      ("tail", match headShape defs tail with
        | .sum _ cases =>
          match listParts? cases with
          | some (_, _, item', tail') => orderSpine defs item' tail' js
          | none => .arr js
        | _ => .arr js)]
termination_by js => (sizeOf js, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega
end

/-- **Read a value tree under a shape document** from its cases print. -/
def ShapeDoc.read (doc : ShapeDoc) (j : Json) : Option Val :=
  readIn doc.defs [] doc.root j

/-- **Read a canonical carrier from its cases print** (`ShapeDoc.print` under its shape). -/
def Canonical.ofJson {α : Type} [Canonical α] (j : Json) : Option α :=
  ((Canonical.shape α).read j).bind Canonical.ofVal

/-- **Order a document's JSON**: `orderIn` under its root. The named normaliser of the profile's
reader (`Store/Domain/ShapeJson.lean`), whose exactness is stated modulo it. -/
def ShapeDoc.order (doc : ShapeDoc) (j : Json) : Json :=
  orderIn doc.defs [] doc.root j

end Effect4.Store
