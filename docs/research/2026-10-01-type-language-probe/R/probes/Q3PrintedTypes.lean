import Effect4.Store.Carrier.Utf8
import Effect4.Program.Ty
import TypeScript.TypeRef
import TypeScript.Identifier
import TypeScript.Render

/-!
# Seat R, question 3: the printed types, the parser arm, and the assignability vectors

Type-language probe, 2026-10-01. A model, not the tree.

* `TTy` is the type language's printable formers with row 119's record (and stage 4's field
  modifiers and row 125's string-keyed map, as data, to print them); `ofTyM` is
  `Codegen/Types.lean:268-321`'s `ofNormalized` with a record arm (readonly fields, canonical
  order) and a map arm, into the vendored `TypeScript.TypeRef`, rendered by the vendored
  `TypeScript.Render.type`. Optional fields have no vendored spelling (`TypeRef.object` carries
  `(name, readonly, type)` only), so `renderFields` spells them beside it.
* `Legacy` is a verbatim copy of `Codegen/Types.lean:32-266` (`parseLegacy`, private there)
  with one arm added between `BEGIN`/`END` markers: object types, the printed image only.
  `#guard`s check `parseLegacy (render t) = some t` on the printed forms.
* `vectors` writes row 68's record pairs in `tools/Tools/TyVectors.lean`'s nine columns, with an
  exact `sub` (canonical names equal, fields below) and a written-order mutant as the red
  control; `host/assignability/run.ts` asks tsgo.
-/

set_option autoImplicit false

namespace SeatR.Types

open TypeScript

/-! ## 1. Names, their order, the canonical field list -/

/-- The UTF-8 byte order on names: the key order `Ty.key` uses for a `lit` (`Ty.lean:155-176`). -/
def nameLt (a b : String) : Bool :=
  Effect4.Program.Ty.ltKey (Effect4.Program.Ty.key (.lit a)) (Effect4.Program.Ty.key (.lit b))

/-- Insert by name; an equal name already present wins, so a left fold keeps the first. -/
def ins {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs => if nameLt p.1 q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by name, the first of a repeated name kept. -/
def canon {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc p => ins p acc) []

theorem ins_map {α β : Type} (f : α → β) (p : String × α) (l : List (String × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [List.map_cons, ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp only [List.map_cons, ins, if_neg h1, if_pos h2]
      · simp only [List.map_cons, ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (String × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

/-- The canonicaliser is payload-polymorphic: it commutes with any map of the payloads. -/
theorem canon_map {α β : Type} (f : α → β) (xs : List (String × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : String × α) (l : List (String × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [ins, if_pos h1, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2] at h
        exact Or.inr h
      · simp only [ins, if_neg h1, if_neg h2, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem mem_foldl_ins {α : Type} (x : String × α) (xs acc : List (String × α))
    (h : x ∈ xs.foldl (fun a p => ins p a) acc) : x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    simp only [List.foldl_cons] at h
    rcases ih (ins y acc) h with h' | h'
    · rcases mem_ins y x acc h' with h'' | h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- Every field of the canonical list is a field of the input. -/
theorem mem_canon {α : Type} (x : String × α) (xs : List (String × α)) (h : x ∈ canon xs) :
    x ∈ xs := by
  rcases mem_foldl_ins x xs [] h with h' | h'
  · cases h'
  · exact h'

/-- The value of a name in a field list, first match. -/
def lookupName {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (m, a) :: rest => if m = n then some a else lookupName n rest


/-! ## 2. The printable type formers -/

/-- Stage 4's policy, as data: `optionalKey` prints `a?: τ`, `optional` prints `a?: τ | undefined`
(rc.112 `Schema.ts:2395-2521`). -/
inductive FieldMod
  | req
  | optKey
  | opt
deriving DecidableEq

inductive TTy where
  | never
  | unknown
  | unit
  | nat
  | string
  | bool
  | lit (s : String)
  | option (t : TTy)
  | list (t : TTy)
  | prod (a b : TTy)
  | union (a b : TTy)
  | record (fields : List (String × FieldMod × TTy))
  /-- Row 125's keyed map at string keys: rc.112's `Schema.Record(Schema.String, V)`. -/
  | map (value : TTy)

def unionParts : TypeRef → List TypeRef
  | .union members => members
  | value => [value]

def unionOf (members : List TypeRef) : TypeRef :=
  match members.eraseDups with
  | [value] => value
  | canonical => .union canonical

mutual
/-- `ofNormalized` with a record arm: readonly fields in canonical order; `none` where the
vendored carrier has no spelling (an optional field). -/
def ofTyM : TTy → Option TypeRef
  | .never => some (.name ["never"] [])
  | .unknown => some (.name ["unknown"] [])
  | .unit => some (.name ["void"] [])
  | .nat => some (.name ["number"] [])
  | .string => some (.name ["string"] [])
  | .bool => some (.name ["boolean"] [])
  | .lit value => some (.literal value)
  | .option inner => do
      let value ← ofTyM inner
      pure (.name ["Option", "Option"] [value])
  | .list inner => do
      let value ← ofTyM inner
      pure (.name ["ReadonlyArray"] [value])
  | .prod left right => do
      let a ← ofTyM left
      let b ← ofTyM right
      pure (.tuple [a, b] true)
  | .union left right => do
      let a ← ofTyM left
      let b ← ofTyM right
      pure (unionOf (unionParts a ++ unionParts b))
  | .record fs => do
      let fields ← ofFields fs
      pure (.object ((canon fields).map fun p => (p.1, true, p.2)))
  | .map value => do
      let v ← ofTyM value
      pure (.name ["Readonly"] [.name ["Record"] [.name ["string"] [], v]])
def ofFields : List (String × FieldMod × TTy) → Option (List (String × TypeRef))
  | [] => some []
  | (n, m, t) :: rest => do
      if m != .req then none
      let r ← ofTyM t
      let rs ← ofFields rest
      pure ((n, r) :: rs)
end

def renderTy (t : TTy) : Option String := (ofTyM t).map (TypeScript.Render.type house0)

/-- The field list with modifiers, spelled beside the vendored renderer (which has no `?`). -/
def renderFields (fields : List (String × FieldMod × String)) : String :=
  let one := fun (p : String × FieldMod × String) =>
    "readonly " ++ (if targetIdentifier p.1 then p.1 else TypeScript.Render.quoted house0 p.1) ++
      (match p.2.1 with
       | .req => ": " ++ p.2.2
       | .optKey => "?: " ++ p.2.2
       | .opt => "?: " ++ p.2.2 ++ " | undefined")
  if fields.isEmpty then "{}" else "{ " ++ String.intercalate "; " (fields.map one) ++ " }"

def userT : TTy :=
  .record [("role", .req, .union (.lit "admin") (.lit "member")), ("id", .req, .nat), ("name", .req, .string)]

-- records: readonly, canonical order whatever the written order (`host/types/printed-types.ts`)
#guard renderTy userT == some "{ readonly id: number; readonly name: string; readonly role: \"admin\" | \"member\" }"
#guard renderTy (.record [("default", .req, .bool), ("content-type", .req, .string)]) ==
  some "{ readonly \"content-type\": string; readonly \"default\": boolean }"
#guard renderTy (.record [("__proto__", .req, .string)]) == some "{ readonly __proto__: string }"
#guard renderTy (.record []) == some "{}"
-- nested, and inside the existing formers
#guard renderTy (.option (.record [("status", .req, .nat), ("body", .req, .string)])) ==
  some "Option.Option<{ readonly body: string; readonly status: number }>"
-- a tagged union is a union of records with a literal `_tag`
#guard renderTy (.union (.record [("_tag", .req, .lit "Deposit"), ("amount", .req, .nat)])
                        (.record [("_tag", .req, .lit "Withdraw"), ("amount", .req, .nat)])) ==
  some "{ readonly _tag: \"Deposit\"; readonly amount: number } | { readonly _tag: \"Withdraw\"; readonly amount: number }"
-- row 125's map at string keys, as rc.112's `Schema.Record(String, V)` types it
#guard renderTy (.map .nat) == some "Readonly<Record<string, number>>"
-- an optional field has no vendored spelling; beside it, stage 4's two spellings
#guard renderTy (.record [("a", .optKey, .nat)]) == none
#guard renderFields [("a", .optKey, "number")] == "{ readonly a?: number }"
#guard renderFields [("a", .opt, "number")] == "{ readonly a?: number | undefined }"

/-! ## 3. The parser arm: a copy of `parseLegacy` with object types -/

namespace Legacy

abbrev Bytes := List UInt8

def whitespace (byte : UInt8) : Bool :=
  byte == 32 || byte == 9 || byte == 10 || byte == 13

def skipSpace (bytes : Bytes) : Bytes := bytes.dropWhile whitespace

def hexDigit (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

def readHex : Nat → Nat → Bytes → Option (Nat × Bytes)
  | 0, value, rest => some (value, rest)
  | count + 1, value, byte :: rest => do
      let digit ← hexDigit byte
      readHex count (value * 16 + digit) rest
  | _ + 1, _, [] => none

def scalarBytes (value : Nat) : Option Bytes :=
  if value < 0x110000 && !(0xd800 ≤ value && value ≤ 0xdfff) then
    some (String.utf8EncodeChar (Char.ofNat value))
  else none

def readBracedUnicode (value digits : Nat) : Bytes → Option (Nat × Bytes)
  | [] => none
  | byte :: rest =>
      if byte == 125 then
        if digits == 0 then none else some (value, rest)
      else do
        let digit ← hexDigit byte
        let next := value * 16 + digit
        if next < 0x110000 then readBracedUnicode next (digits + 1) rest else none

def readUnicode (bytes : Bytes) : Option (Bytes × Bytes) := do
  match bytes with
  | [] => none
  | byte :: rest =>
      if byte == 123 then do
        let (value, tail) ← readBracedUnicode 0 0 rest
        let encoded ← scalarBytes value
        pure (encoded, tail)
      else do
        let (value, tail) ← readHex 4 0 bytes
        if 0xd800 ≤ value && value ≤ 0xdbff then
          match tail with
          | slash :: u :: more =>
              if slash == 92 && u == 117 then do
                let (low, remaining) ← readHex 4 0 more
                if 0xdc00 ≤ low && low ≤ 0xdfff then do
                  let encoded ← scalarBytes
                    (0x10000 + (value - 0xd800) * 0x400 + (low - 0xdc00))
                  pure (encoded, remaining)
                else none
              else none
          | _ => none
        else do
          let encoded ← scalarBytes value
          pure (encoded, tail)

def readEscape : Bytes → Option (Bytes × Bytes)
  | [] => none
  | byte :: rest =>
      if byte == 34 || byte == 39 || byte == 92 || byte == 47 then some ([byte], rest)
      else if byte == 98 then some ([8], rest)
      else if byte == 102 then some ([12], rest)
      else if byte == 110 then some ([10], rest)
      else if byte == 114 then some ([13], rest)
      else if byte == 116 then some ([9], rest)
      else if byte == 118 then some ([11], rest)
      else if byte == 48 then
        if rest.head?.any (fun next => 48 ≤ next && next ≤ 57) then none
        else some ([0], rest)
      else if byte == 120 then do
        let (value, tail) ← readHex 2 0 rest
        let encoded ← scalarBytes value
        pure (encoded, tail)
      else if byte == 117 then readUnicode rest
      else if byte == 10 then some ([], rest)
      else if byte == 13 then
        match rest with
        | next :: tail => if next == 10 then some ([], tail) else some ([], rest)
        | [] => some ([], [])
      else none

def readLiteral : Nat → UInt8 → Bytes → Bytes → Option (String × Bytes)
  | 0, _, _, _ => none
  | fuel + 1, quote, reversed, bytes =>
      match bytes with
      | [] => none
      | byte :: rest =>
          if byte == quote then do
            let value ← Effect4.Store.decodeString reversed.reverse
            pure (value, rest)
          else if byte == 92 then do
            let (escaped, tail) ← readEscape rest
            readLiteral fuel quote (escaped.reverse ++ reversed) tail
          else if byte == 10 || byte == 13 then none
          else readLiteral fuel quote (byte :: reversed) rest

def readIdentifier (bytes : Bytes) : Option (String × Bytes) := do
  let bytes := skipSpace bytes
  match bytes with
  | [] => none
  | first :: _ =>
      if identifierStart first then do
        let chunk := bytes.takeWhile identifierContinue
        let name ← Effect4.Store.decodeString chunk
        pure (name, bytes.drop chunk.length)
      else none

def readQualified : Nat → List String → Bytes → Option (List String × Bytes)
  | 0, _, _ => none
  | fuel + 1, reversed, bytes =>
      match skipSpace bytes with
      | [] => some (reversed.reverse, [])
      | byte :: rest =>
          if byte == 46 then do
            let (name, tail) ← readIdentifier rest
            if targetIdentifier name then readQualified fuel (name :: reversed) tail
            else none
          else some (reversed.reverse, skipSpace bytes)

def primitiveName (name : String) : Bool :=
  ["any", "unknown", "never", "void", "undefined", "null", "number", "string",
   "boolean", "object", "symbol", "bigint"].contains name

def typeHead (name : String) : Bool :=
  targetIdentifier name && !["keyof", "infer", "unique"].contains name

def unionParts : TypeRef → List TypeRef
  | .union members => members
  | value => [value]

/-- Union members in canonical target form: flattened, without duplicates, and a single
member standing alone. Distinct core types can share one target spelling (`nat` and
`int` are both `number`), so this identification is the target's, not the core's; it is
what lets a declared type be compared with a projected one by structural equality. -/
def unionOf (members : List TypeRef) : TypeRef :=
  match members.eraseDups with
  | [value] => value
  | canonical => .union canonical

def finishUnion (reversed : List TypeRef) : TypeRef :=
  unionOf (reversed.reverse.flatMap unionParts)

mutual
  def readType : Nat → Bytes → Option (TypeRef × Bytes)
    | 0, _ => none
    | fuel + 1, bytes => do
        let (first, rest) ← readAtom fuel bytes
        readUnion fuel [first] rest

  def readUnion : Nat → List TypeRef → Bytes → Option (TypeRef × Bytes)
    | 0, _, _ => none
    | fuel + 1, reversed, bytes =>
        match skipSpace bytes with
        | [] => some (finishUnion reversed, [])
        | byte :: rest =>
            if byte == 124 then do
              let (next, tail) ← readAtom fuel rest
              readUnion fuel (next :: reversed) tail
            else some (finishUnion reversed, skipSpace bytes)

  def readAtom : Nat → Bytes → Option (TypeRef × Bytes)
    | 0, _ => none
    | fuel + 1, bytes => do
        let bytes := skipSpace bytes
        match bytes with
        | [] => none
        | byte :: rest =>
            if byte == 34 || byte == 39 then do
              let (value, tail) ← readLiteral fuel byte [] rest
              pure (.literal value, tail)
            else if byte == 40 then do
              let (value, tail) ← readType fuel rest
              match skipSpace tail with
              | close :: remaining => if close == 41 then some (value, remaining) else none
              | [] => none
            else if byte == 91 then do
              let (items, tail) ← readTypes fuel 93 true rest
              pure (.tuple items false, tail)
            -- BEGIN object arm (seat R): `{ readonly name: T; … }`, the printed image only
            else if byte == 123 then do
              let (fields, tail) ← readFields fuel rest
              pure (.object fields, tail)
            -- END object arm
            else do
              let (name, tail) ← readIdentifier bytes
              if name == "readonly" then
                match skipSpace tail with
                | opening :: remaining =>
                    if opening == 91 then do
                      let (items, after) ← readTypes fuel 93 true remaining
                      pure (.tuple items true, after)
                    else none
                | [] => none
              else if primitiveName name then
                pure (.name [name] [], tail)
              else if typeHead name then do
                let (qualified, tail) ← readQualified (fuel + 1) [name] tail
                match skipSpace tail with
                | opening :: remaining =>
                    if opening == 60 then do
                      let (args, after) ← readTypes fuel 62 false remaining
                      pure (.name qualified args, after)
                    else pure (.name qualified [], skipSpace tail)
                | [] => pure (.name qualified [], [])
              else none

  def readTypes : Nat → UInt8 → Bool → Bytes → Option (List TypeRef × Bytes)
    | 0, _, _, _ => none
    | fuel + 1, closing, allowEmpty, bytes => do
        let bytes := skipSpace bytes
        match bytes with
        | [] => none
        | byte :: rest =>
            if byte == closing then
              if allowEmpty then pure ([], rest) else none
            else do
              let (item, tail) ← readType fuel bytes
              match skipSpace tail with
              | close :: remaining =>
                  if close == closing then pure ([item], remaining)
                  else if close == 44 then do
                    let (items, after) ← readTypes fuel closing true remaining
                    pure (item :: items, after)
                  else none
              | [] => none

  -- BEGIN object arm (seat R): the fields after `{`. Each field is `readonly`, a name (an
  -- identifier, or a quoted literal as the renderer quotes a non-identifier), `:` and a type;
  -- fields are separated by `;`; `}` closes. `{}` is the empty record.
  def readFields : Nat → Bytes → Option (List (String × Bool × TypeRef) × Bytes)
    | 0, _ => none
    | fuel + 1, bytes => do
        match skipSpace bytes with
        | [] => none
        | byte :: rest =>
            if byte == 125 then pure ([], rest)
            else do
              let (kw, afterKw) ← readIdentifier (byte :: rest)
              if kw != "readonly" then none
              else do
                let (name, afterName) ← readFieldName fuel afterKw
                match skipSpace afterName with
                | colon :: afterColon =>
                    if colon != 58 then none
                    else do
                      let (ty, afterTy) ← readType fuel afterColon
                      match skipSpace afterTy with
                      | 59 :: more => do
                          let (others, tail) ← readFields fuel more
                          if others.isEmpty then none else pure ((name, true, ty) :: others, tail)
                      | 125 :: more => pure ([(name, true, ty)], more)
                      | _ => none
                | [] => none

  def readFieldName : Nat → Bytes → Option (String × Bytes)
    | 0, _ => none
    | fuel + 1, bytes =>
        match skipSpace bytes with
        | [] => none
        | byte :: rest =>
            if byte == 34 || byte == 39 then do
              let (value, tail) ← readLiteral fuel byte [] rest
              if targetIdentifier value then none else pure (value, tail)
            else do
              let (name, tail) ← readIdentifier (byte :: rest)
              if targetIdentifier name then pure (name, tail) else none
  -- END object arm
end

/-- Read the admitted legacy type spelling into structural target syntax.
The parser has an input-derived recursion bound and refuses any unconsumed
suffix; neither exhaustion nor malformed input yields a raw target snippet. -/
def parseLegacy (text : String) : Option TypeRef := do
  let bytes := text.toUTF8.data.toList
  let (value, rest) ← readType (2 * bytes.length + 4) bytes
  if (skipSpace rest).isEmpty then some value else none


end Legacy

/-- Read back what the printer renders. -/
def readsBack (t : TTy) : Bool :=
  match ofTyM t with
  | some ref => Legacy.parseLegacy (TypeScript.Render.type house0 ref) == some ref
  | none => false

#guard readsBack userT
#guard readsBack (.record [("default", .req, .bool), ("content-type", .req, .string)])
#guard readsBack (.record [("a\"b", .req, .nat), ("名前", .req, .string)])
#guard readsBack (.record [])
#guard readsBack (.option (.record [("status", .req, .nat), ("body", .req, .string)]))
#guard readsBack (.record [("user", .req, .record [("id", .req, .nat), ("name", .req, .string)]), ("ok", .req, .bool)])
#guard readsBack (.union (.record [("_tag", .req, .lit "A"), ("a", .req, .nat)]) (.record [("_tag", .req, .lit "B"), ("b", .req, .string)]))
#guard readsBack (.map (.record [("id", .req, .nat)]))
-- the arm reads exactly the printed image: no other spelling of a record type
#guard Legacy.parseLegacy "{ a: number }" == none
#guard Legacy.parseLegacy "{ readonly a: number, readonly b: string }" == none
#guard Legacy.parseLegacy "{ readonly \"a\": number }" == none
#guard Legacy.parseLegacy "{ readonly a?: number }" == none
#guard Legacy.parseLegacy "{ readonly a: number; }" == none
-- and nothing it read before changes
#guard Legacy.parseLegacy "Box<readonly [number, 'tag']> | never" ==
  some (.union [.name ["Box"] [.tuple [.name ["number"] [], .literal "tag"] true], .name ["never"] []])

/-! ## 4. Row 68's record pairs -/

def sameNames (fs gs : List (String × FieldMod × TTy)) : Bool :=
  (canon fs).map Prod.fst == (canon gs).map Prod.fst

/-- The model order, bounded by fuel (an executable comparator for the vectors only; no law is
stated about it): exact records (same canonical names, each field below), depth covariant, the
existing formers as `Ty.sub` treats them (unions by members, `lit` below `string`). `written`
switches the record arm to written order: the red control. -/
def subF (written : Bool) : Nat → TTy → TTy → Bool
  | 0, _, _ => false
  | _ + 1, .never, _ => true
  | _ + 1, _, .unknown => true
  | fuel + 1, .union a b, t => subF written fuel a t && subF written fuel b t
  | fuel + 1, s, .union a b => subF written fuel s a || subF written fuel s b
  | fuel + 1, .record fs, .record gs =>
    if written then
      fs.map Prod.fst == gs.map Prod.fst &&
        (fs.zip gs).all (fun p => subF written fuel p.1.2.2 p.2.2.2)
    else
      sameNames fs gs &&
        fs.all (fun f => match lookupName f.1 gs with
          | some (_, g) => subF written fuel f.2.2 g
          | none => false)
  | fuel + 1, .option a, .option b => subF written fuel a b
  | fuel + 1, .list a, .list b => subF written fuel a b
  | fuel + 1, .prod a b, .prod c d => subF written fuel a c && subF written fuel b d
  | fuel + 1, .map a, .map b => subF written fuel a b
  | _ + 1, .nat, .nat | _ + 1, .string, .string | _ + 1, .bool, .bool | _ + 1, .unit, .unit => true
  | _ + 1, .lit s, .lit u => decide (s = u)
  | _ + 1, .lit _, .string => true
  | _ + 1, _, _ => false

def sub (a b : TTy) : Bool := subF false 64 a b
def subW (a b : TTy) : Bool := subF true 64 a b

mutual
/-- A type as TypeScript text in written order (no canonicalisation), so the target sees the
permutation itself. -/
def renderW : TTy → String
  | .never => "never"
  | .unknown => "unknown"
  | .unit => "void"
  | .nat => "number"
  | .string => "string"
  | .bool => "boolean"
  | .lit s => TypeScript.Render.quoted house0 s
  | .option t => "Option.Option<" ++ renderW t ++ ">"
  | .list t => "ReadonlyArray<" ++ renderW t ++ ">"
  | .prod a b => "readonly [" ++ renderW a ++ ", " ++ renderW b ++ "]"
  | .union a b => renderW a ++ " | " ++ renderW b
  | .record fs => if fs.isEmpty then "{}" else "{ " ++ String.intercalate "; " (renderWFields fs) ++ " }"
  | .map v => "Readonly<Record<string, " ++ renderW v ++ ">>"
def renderWFields : List (String × FieldMod × TTy) → List String
  | [] => []
  | (n, _, t) :: rest =>
    ("readonly " ++ (if targetIdentifier n then n else TypeScript.Render.quoted house0 n) ++ ": " ++ renderW t) ::
      renderWFields rest
end

def rAB : TTy := .record [("a", .req, .nat), ("b", .req, .string)]
def rBA : TTy := .record [("b", .req, .string), ("a", .req, .nat)]
def rA : TTy := .record [("a", .req, .nat)]
def rB : TTy := .record [("b", .req, .nat)]
def rLit : TTy := .record [("a", .req, .lit "x")]
def rStr : TTy := .record [("a", .req, .string)]
def rU : TTy := .record [("a", .req, .union .nat .string)]
def uR : TTy := .union (.record [("a", .req, .nat)]) (.record [("a", .req, .string)])
def rLU : TTy := .record [("a", .req, .union (.lit "x") (.lit "y"))]
def uRL : TTy := .union (.record [("a", .req, .lit "x")]) (.record [("a", .req, .lit "y")])
def nested1 : TTy := .record [("u", .req, rAB), ("s", .req, .nat)]
def nested2 : TTy := .record [("s", .req, .nat), ("u", .req, rBA)]
def nestedW : TTy := .record [("s", .req, .nat), ("u", .req, rA)]
def tagged1 : TTy := .union (.record [("_tag", .req, .lit "A"), ("a", .req, .nat)]) (.record [("_tag", .req, .lit "B"), ("b", .req, .string)])
def tagged2 : TTy := .union (.record [("b", .req, .string), ("_tag", .req, .lit "B")]) (.record [("a", .req, .nat), ("_tag", .req, .lit "A")])
def empty : TTy := .record []

/-- The record family and its neighbours: permutations, width both ways, depth, the factor rule
(a record with a union field against the union of records), nesting, tags, the empty record. -/
def pairs : List (String × TTy × TTy) :=
  [ ("record/perm", rAB, rBA), ("record/width", rAB, rA), ("record/names", rA, rB)
  , ("record/depth", rLit, rStr), ("record/factor", rU, uR), ("record/factor-lit", rLU, uRL)
  , ("record/nested-perm", nested1, nested2), ("record/nested-width", nested1, nestedW)
  , ("record/tagged-perm", tagged1, tagged2), ("record/empty-nat", empty, .nat)
  , ("record/empty-rec", empty, rA), ("record/prod", rAB, .prod .nat .string)
  , ("record/unknown", rAB, .unknown), ("record/never", .never, rAB)
  , ("record/option", .option rAB, .option rBA), ("record/map", .map .nat, rA)
  , ("control/lit-string", .lit "a", .string), ("control/nat-string", .nat, .string)
  , ("control/union", .union .nat .string, .nat) ]

def bit (b : Bool) : String := if b then "true" else "false"

-- the fuel is not what answers: a larger budget gives the same verdicts on every pair
#guard pairs.all fun (_, a, b) => subF false 64 a b == subF false 256 a b && subF true 64 a b == subF true 256 a b

def line (p : String × TTy × TTy) : String :=
  let (id, a, b) := p
  String.intercalate "\t" [id, renderW a, renderW b, renderW a, renderW b,
    bit (sub a b), bit (sub b a), bit (subW a b), bit (subW b a)]

#eval show IO Unit from do
  IO.println "# GENERATED by docs/research/2026-10-01-type-language-probe/R/probes/Q3PrintedTypes.lean (seat R)"
  IO.println "# id\tleft\tright\trenderLeft\trenderRight\tsubLR\tsubRL\tmutantLR\tmutantRL"
  for p in pairs do IO.println ("VEC\t" ++ line p)

end SeatR.Types
