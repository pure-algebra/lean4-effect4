module

public import Effect4.Store.Domain.ShapeRead
public import Effect4.Data.NatJson
public import Effect4.Data.Located
meta import Effect4.Data.Json
meta import Effect4.Data.NatJson
meta import Effect4.Store.Carrier.Digest
meta import Effect4.Store.Carrier.Val

/-!
# Store.ShapeJson — a value tree read from, and printed to, the profile's JSON tree

The tool's JSON is the profile's tree (`Effect4.NatJson`): JSON whose numbers are naturals. This
module reads a value tree from it under a shape document, refusing at a place, and prints a value
tree to it as the tools print it. It is the one implementation of a carrier's JSON: the OCaml
route lowers it, and the binary64 tree reads and prints through it (`NatJson.ofBinary64`,
`NatJson.toBinary64`).

**The reader** (`ShapeDoc.readLocated`) reads JSON an agent writes: an object's entries in any
order, and a list family as an array or as its `cons` cases. It refuses with a reason at a site
(`JsonRefusal`):
- a value at a path, where the value does not fit (`expected` names the shape there, as the
  document writes it);
- a field missing from an object, at that object's path;
- a key repeated, a key that names no field, or a case name the sum lacks, at the object;
- a natural above `safeBound`, or a number that is no natural, at the number.

No budget bounds the reading, so no refusal says that one ran out. The reader recurses on the
tree's size, then on the definitions not yet unfolded since the last node, then on the shape's
size (`Store/Domain/ShapeRead.lean`). An option layer that returns to a name it unfolded since the
last node refuses the value as `expected`: under each name's first definition, the shape there
holds only options of options, which print `null`.

A path is the input's own: an array's element keeps its index, even inside a list family's
array, and no path passes through a `cons` cell the input did not write. A refusal names one
site, and that site is in the input (`readLocated_site`, `Laws/Store/ShapeRead.lean`).

**Exactness.** Whatever the reader reads is the value whose canonical print is the input,
normalised by `ShapeDoc.order` (`readLocated_exact`). The reader takes its steps as the normaliser
does, so the law is proved by one induction beside it.

**The printer** (`ShapeDoc.printTree`) is `ShapeDoc.print` with each list family written as the
array of its elements, the encoding `ts/eff/eff.gen.ts` types. `Canonical.print`, a carrier's one
public JSON (decisions row 418, D2), is its image on the binary64 tree.

The old `Option` readers are projections of the located one: `ShapeDoc.readAny`, and
`Canonical.ofJsonAnyOrder` on the binary64 tree.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.NatJson

open Effect4 (Json Float64)

mutual
/-- **A binary64 tree as the profile's tree**: a number becomes the natural it spells
(`Store.natOfBinary64`), or a numeral with no text when it spells none. -/
def ofBinary64 : Json → NatJson
  | .null => .null
  | .bool b => .bool b
  | .number x =>
    match Store.natOfBinary64 x.bits with
    | some n => .nat n
    | none => .numeral ""
  | .str s => .str s
  | .arr js => .arr (ofBinary64List js)
  | .obj entries => .obj (ofBinary64Entries entries)

/-- `ofBinary64` over a list. -/
def ofBinary64List : List Json → List NatJson
  | [] => []
  | j :: js => ofBinary64 j :: ofBinary64List js

/-- `ofBinary64` over an object's entries. -/
def ofBinary64Entries : List (String × Json) → List (String × NatJson)
  | [] => []
  | (k, j) :: entries => (k, ofBinary64 j) :: ofBinary64Entries entries
end

mutual
/-- **The profile's tree as a binary64 tree**: a natural becomes the binary64 the host parses
(`Arch.Json.ofNat`), and a numeral becomes NaN, which spells no natural. -/
def toBinary64 : NatJson → Json
  | .null => .null
  | .bool b => .bool b
  | .nat n => Arch.Json.ofNat n
  | .numeral _ => .number Float64.nan
  | .str s => .str s
  | .arr ts => .arr (toBinary64List ts)
  | .obj entries => .obj (toBinary64Entries entries)

/-- `toBinary64` over a list. -/
def toBinary64List : List NatJson → List Json
  | [] => []
  | t :: ts => toBinary64 t :: toBinary64List ts

/-- `toBinary64` over an object's entries. -/
def toBinary64Entries : List (String × NatJson) → List (String × Json)
  | [] => []
  | (k, t) :: entries => (k, toBinary64 t) :: toBinary64Entries entries
end

end Effect4.NatJson

namespace Effect4.Store

open Effect4 (Json Float64 NatJson JsonStep JsonSite Located)

/-- **Why the profile's reader refuses**, in its own alphabet. -/
inductive JsonReason where
  /-- The value does not fit the shape there, which the reason names as the document writes it. -/
  | expected (shape : Shape)
  /-- The object holds a key that names none of its fields. -/
  | unknownField (name : String)
  /-- The object repeats a key. -/
  | duplicateField (name : String)
  /-- The sum has no case of that name. -/
  | unknownCase (name : String)
  /-- A natural above the profile's largest, which the reason names. -/
  | naturalOutsideProfile (limit : Nat)
  /-- The value tree fits the shape, and the carrier refuses it. -/
  | carrierValue
  /-- The profile does not carry the shape. -/
  | unsupportedProfile

/-- **A refusal of the profile's reader**: a reason at a site. -/
abbrev JsonRefusal : Type := Located JsonSite JsonReason

/-- The first key an object repeats. -/
def repeatedKey : List (String × NatJson) → Option String
  | [] => none
  | (k, _) :: rest => if rest.any (fun e => decide (e.1 = k)) then some k else repeatedKey rest

/-- The first key of an object that names none of the fields; `_tag` too, when `tagged`. -/
def unknownKey (fields : List (String × Shape)) (tagged : Bool) :
    List (String × NatJson) → Option String
  | [] => none
  | (k, _) :: rest =>
    if (tagged && decide (k = "_tag")) || fields.any (fun f => decide (f.1 = k)) then
      unknownKey fields tagged rest
    else some k

/-- **An object's last checks**, once its fields have read: no key that names no field, and as
many entries as the fields and the `_tag` take. Then the constructor. -/
def closeObject (s : Shape) (fields : List (String × Shape)) (tagged : Bool) (tag : Nat)
    (entries : List (String × NatJson)) (p : List JsonStep) (args : List Val) :
    Except JsonRefusal Val :=
  match unknownKey fields tagged entries with
  | some k => .error ⟨.value p, .unknownField k⟩
  | none =>
    if fields.length + (if tagged then 1 else 0) = entries.length then .ok (.ctor tag args)
    else .error ⟨.value p, .expected s⟩

/-- A kind byte's name, where the byte is registered (`kindJson`'s string). -/
def kindName? (b : UInt8) : Option String := (Kind.ofByte? b).map (·.name)

/-- An object's entry is smaller than its entries. The termination step of the located reader's
fields (`readFieldsAt`). -/
theorem NatJson.sizeOf_entryOf_lt {name : String} :
    ∀ {entries : List (String × NatJson)} {t : NatJson}, NatJson.entryOf name entries = some t →
      sizeOf t < sizeOf entries
  | [], _, h => by cases h
  | (n, t') :: rest, t, h => by
    unfold NatJson.entryOf at h
    split at h
    · cases h
      simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
      omega
    · have := NatJson.sizeOf_entryOf_lt h
      simp only [List.cons.sizeOf_spec]
      omega

mutual
/-- **Read a value tree under a shape** from the profile's tree at path `p`, or refuse at a place.
It takes its steps as the normaliser does (`orderIn`), so the reader reads what the normaliser and
the strict reader together read. `seen` holds the names unfolded since the last node: an option
layer that meets one again refuses the value (`optionLayer?`). -/
def readAt (defs : List (String × Shape)) (seen : List String) (s : Shape) (t : NatJson)
    (p : List JsonStep) : Except JsonRefusal Val :=
  match headShape defs s, t with
  | .option _, .null => .ok .none
  | .option _, t' =>
    match _hl : optionLayer? defs s seen with
    | some (item, seen') => (readAt defs seen' item t' p).map .some
    | none => .error ⟨.value p, .expected s⟩
  | .list item, .arr ts => (readItems defs item ts p 0).map .list
  | .pair f g, .arr [a, b] =>
    (readAt defs [] f a (p ++ [.index 0])).bind fun x =>
      (readAt defs [] g b (p ++ [.index 1])).map fun y => .pair x y
  | .sum _ cases, .arr ts =>
    match listParts? cases with
    | some (t0, t1, item, tail) => readSpine defs t0 t1 item tail ts p 0
    | none => .error ⟨.value p, .expected s⟩
  | .struct _ fields, .obj entries =>
    match repeatedKey entries with
    | some k => .error ⟨.value p, .duplicateField k⟩
    | none => (readFieldsAt defs fields entries p).bind (closeObject s fields false 0 entries p)
  | .sum _ cases, .obj entries =>
    if allNullary cases then .error ⟨.value p, .expected s⟩
    else
      match NatJson.entryOf "_tag" entries with
      | some (.str name) =>
        match tagOfName name cases with
        | some (tag, fields) =>
          match repeatedKey entries with
          | some k => .error ⟨.value p, .duplicateField k⟩
          | none =>
            (readFieldsAt defs fields entries p).bind (closeObject s fields true tag entries p)
        | none => .error ⟨.value p, .unknownCase name⟩
      | some _ => .error ⟨.value (p ++ [.key "_tag"]), .expected s⟩
      | none => .error ⟨.missing p "_tag", .expected s⟩
  | .unit, .null => .ok .unit
  | .bool, .bool b => .ok (.bool b)
  | .nat, .nat n =>
    if n ≤ safeBound then .ok (.nat n)
    else .error ⟨.value p, .naturalOutsideProfile safeBound⟩
  | .nat, .numeral text =>
    .error ⟨.value p,
      if NatJson.allDigits text then .naturalOutsideProfile safeBound else .expected s⟩
  | .string, .str x => .ok (.str x)
  | .bytes, .str h =>
    match canonicalHex? h with
    | some d => .ok (.bytes d)
    | none => .error ⟨.value p, .expected s⟩
  | .digest, .str h =>
    match canonicalHex? h with
    | some d => .ok (.bytes d)
    | none => .error ⟨.value p, .expected s⟩
  | .sum _ cases, .str name =>
    if allNullary cases then
      match tagOfName name cases with
      | some (tag, []) => .ok (.ctor tag [])
      | some (_, _ :: _) => .error ⟨.value p, .expected s⟩
      | none => .error ⟨.value p, .unknownCase name⟩
    else .error ⟨.value p, .expected s⟩
  | .ref k, .str h =>
    match canonicalHex? h with
    | some d => .ok (.ref k.byte d)
    | none => .error ⟨.value p, .expected s⟩
  | .anyRef, .obj [("kind", .str kn), ("address", .str h)] =>
    match Kind.ofName? kn with
    | some k =>
      if kindName? k.byte = some kn then
        match canonicalHex? h with
        | some d => .ok (.ref k.byte d)
        | none => .error ⟨.value p, .expected s⟩
      else .error ⟨.value p, .expected s⟩
    | none => .error ⟨.value p, .expected s⟩
  | _, _ => .error ⟨.value p, .expected s⟩
termination_by (sizeOf t, unseenDefs defs seen, sizeOf s)
decreasing_by
  · exact Prod.Lex.right _ (optionLayer?_lt _hl)
  all_goals
    apply Prod.Lex.left
    simp only [NatJson.arr.sizeOf_spec, NatJson.obj.sizeOf_spec, List.cons.sizeOf_spec]
    omega

/-- Read a list's elements under the item shape, the `i`-th at path `p ++ [.index i]`. -/
def readItems (defs : List (String × Shape)) (item : Shape) :
    List NatJson → List JsonStep → Nat → Except JsonRefusal (List Val)
  | [], _, _ => .ok []
  | t :: ts, p, i =>
    (readAt defs [] item t (p ++ [.index i])).bind fun x =>
      (readItems defs item ts p (i + 1)).map (x :: ·)
termination_by ts => (sizeOf ts, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega

/-- Read the fields of a structure or a case, in the shape's order, each at the first entry with
its name. A field with no entry is refused as missing from the object at `p`. -/
def readFieldsAt (defs : List (String × Shape)) :
    List (String × Shape) → List (String × NatJson) → List JsonStep →
      Except JsonRefusal (List Val)
  | [], _, _ => .ok []
  | (n, s) :: fields, entries, p =>
    match _he : NatJson.entryOf n entries with
    | some t =>
      (readAt defs [] s t (p ++ [.key n])).bind fun x =>
        (readFieldsAt defs fields entries p).map (x :: ·)
    | none => .error ⟨.missing p n, .expected s⟩
termination_by fields entries => (sizeOf entries, 0, fields.length)
decreasing_by
  · exact Prod.Lex.left _ _ (NatJson.sizeOf_entryOf_lt _he)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))

/-- **Read a list family's array**, from its `i`-th element on: `nil` (tag `t0`) at the end, else
`cons` (tag `t1`) of the element under the cell's head shape and the rest under its tail shape,
which must be a list family again. Each element keeps its index in the array at `p`. -/
def readSpine (defs : List (String × Shape)) :
    Nat → Nat → Shape → Shape → List NatJson → List JsonStep → Nat → Except JsonRefusal Val
  | t0, _, _, _, [], _, _ => .ok (.ctor t0 [])
  | _, t1, item, tail, t :: ts, p, i =>
    (readAt defs [] item t (p ++ [.index i])).bind fun x =>
      (match headShape defs tail with
       | .sum _ cases =>
         match listParts? cases with
         | some (t0', t1', item', tail') => readSpine defs t0' t1' item' tail' ts p (i + 1)
         | none => .error ⟨.value p, .expected tail⟩
       | _ => .error ⟨.value p, .expected tail⟩).map fun rest => .ctor t1 [x, rest]
termination_by _ _ _ _ ts => (sizeOf ts, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega
end

/-- **Read a value tree under a shape document** from the profile's tree, or refuse at a place. -/
def ShapeDoc.readLocated (doc : ShapeDoc) (t : NatJson) : Except JsonRefusal Val :=
  readAt doc.defs [] doc.root t []

/-- The located reader's projection: the value tree it reads, or none. -/
def ShapeDoc.readAny (doc : ShapeDoc) (t : NatJson) : Option Val := (doc.readLocated t).toOption

/-- **Read a canonical carrier from the profile's tree**: its value tree, then the carrier. A tree
that fits the shape and that the carrier refuses is refused at the root. -/
def Canonical.readLocated {α : Type} [Canonical α] (t : NatJson) : Except JsonRefusal α :=
  ((Canonical.shape α).readLocated t).bind fun v =>
    match Canonical.ofVal v with
    | some a => .ok a
    | none => .error ⟨.value [], .carrierValue⟩

/-- **Read a canonical carrier from JSON whose objects may be in any order**, and whose lists may
be arrays: the located reader's projection, on the binary64 tree's profile tree. -/
def Canonical.ofJsonAnyOrder {α : Type} [Canonical α] (j : Json) : Option α :=
  (Canonical.readLocated (NatJson.ofBinary64 j)).toOption

/-! ## The printer -/

/-- A kind byte as the profile's printer writes it: its name, or `null` for an unregistered
byte (`kindJson`). -/
def kindTree (b : UInt8) : NatJson :=
  match kindName? b with
  | some name => .str name
  | none => .null

mutual
/-- **The printer to the profile's tree**: `printIn`, with each list family (`listParts?`) written
as the array of its elements, each under its cell's head shape. A list family's value that is no
chain of its family's cells prints by its cases, as `printIn` prints it. -/
def printTreeIn (defs : List (String × Shape)) : Shape → Val → NatJson
  | _, .unit => .null
  | _, .bool b => .bool b
  | _, .nat n => .nat n
  | _, .str s => .str s
  | _, .bytes d => .str (hexString d)
  | _, .none => .null
  | s, .some a =>
    match headShape defs s with
    | .option item => printTreeIn defs item a
    | _ => printTreeIn defs .unit a
  | s, .list xs =>
    match headShape defs s with
    | .list item => .arr (printTreeList defs item xs)
    | _ => .arr (printTreeList defs .unit xs)
  | s, .pair a b =>
    match headShape defs s with
    | .pair f g => .arr [printTreeIn defs f a, printTreeIn defs g b]
    | _ => .arr [printTreeIn defs .unit a, printTreeIn defs .unit b]
  | s, .ctor i args =>
    match headShape defs s with
    | .struct _ fields => .obj (printTreeFields defs fields args)
    | .sum _ cases =>
      match (match listParts? cases with
        | some (t0, t1, item, tail) =>
          if i = t0 then (if args.isEmpty then some [] else none)
          else if i = t1 then
            match args with
            | [x, rest] => (printTail defs tail rest).map (printTreeIn defs item x :: ·)
            | _ => none
          else none
        | none => none) with
      | some elements => .arr elements
      | none =>
        match caseAt i cases with
        | some (name, fields) =>
          if allNullary cases then .str name
          else .obj (("_tag", .str name) :: printTreeFields defs fields args)
        | none => .obj [("_ctor", .nat i), ("args", .arr (printTreeList defs .unit args))]
    | _ => .obj [("_ctor", .nat i), ("args", .arr (printTreeList defs .unit args))]
  | s, .ref k d =>
    match headShape defs s with
    | .anyRef => .obj [("kind", kindTree k), ("address", .str (hexString d))]
    | _ => .str (hexString d)
  | _, .handle k n => .obj [("handle", .nat k.toNat), ("key", .nat n)]
  -- `-(n+1)` by its digits, as `toString` writes the integer: the lowered route has no `Int.add`.
  | _, .negInt n => .obj [("int", .str ("-" ++ toString (n + 1)))]
  | _, .float b => .obj [("float64", .str (hexString (be64 b.toNat)))]

/-- The elements of a list, each under the item shape. -/
def printTreeList (defs : List (String × Shape)) : Shape → List Val → List NatJson
  | _, [] => []
  | item, x :: xs => printTreeIn defs item x :: printTreeList defs item xs

/-- The fields of a struct or case, named in declaration order. -/
def printTreeFields (defs : List (String × Shape)) :
    List (String × Shape) → List Val → List (String × NatJson)
  | (n, s) :: fields, a :: args => (n, printTreeIn defs s a) :: printTreeFields defs fields args
  | _, _ => []

/-- **The rest of a list family's array**: the elements after a cell, read off the cell's tail
under the tail's shape, while each tail is its family's `cons` or `nil`. -/
def printTail (defs : List (String × Shape)) : Shape → Val → Option (List NatJson)
  | tail, .ctor i args =>
    match headShape defs tail with
    | .sum _ cases =>
      match listParts? cases with
      | some (t0, t1, item, tail') =>
        if i = t0 then (if args.isEmpty then some [] else none)
        else if i = t1 then
          match args with
          | [x, rest] => (printTail defs tail' rest).map (printTreeIn defs item x :: ·)
          | _ => none
        else none
      | none => none
    | _ => none
  | _, _ => none
end

/-- **The printer of a shape document to the profile's tree**: the value under the root, each list
family as an array. -/
def ShapeDoc.printTree (doc : ShapeDoc) (v : Val) : NatJson := printTreeIn doc.defs doc.root v

/-- **A carrier's public JSON**, as the binary64 tree: its print to the profile's tree
(`ShapeDoc.printTree`), each list as an array; the encoding `ts/eff/eff.gen.ts` types and `toJson`
writes (decisions row 418, D2). The profile's reader reads it. -/
def Canonical.print {α : Type} [Canonical α] (a : α) : Json :=
  ((Canonical.shape α).printTree (Canonical.toVal a)).toBinary64

end Effect4.Store
