import Lean.Data.Json
import Effect4.Laws.Store.ShapeRead

/-!
# Tools.JsonBridge — Lean's JSON and the tree's JSON, both ways

A tool reads its requests with Lean's JSON parser (`Lean.Json.parse`) and writes its answers as
`Lean.Json`. The tree's JSON (`Effect4.Json`) is what the canonical carriers print and read
(`Canonical.print`, `Canonical.ofJsonAnyOrder`, `src/Effect4/Store/Domain/ShapeRead.lean`). This
module moves a value between the two.

- **Lean's to the tree's** (`ofLeanJson`): an object's entries in Lean's order, sorted by key,
  which the shape's order puts right (`ShapeDoc.order`); a number only where it is a natural that
  binary64 holds exactly, as the binary64 the canonical print writes. A natural that binary64
  rounds is refused, not changed (`ofLeanJson_num`; Codex's JSON-01), and so is one from 2^1024
  up, whose pattern is no binary64 of it. Anything else is none.
  `fuel` bounds the depth; a request line's length is enough.
- **The tree's to Lean's** (`toLeanJson`): a number where it spells a natural, and `null` where
  it does not.
-/

namespace Tools.JsonBridge

open Effect4.Store

/-- **Lean's JSON as the tree's**, within `fuel` levels of nesting. -/
def ofLeanJson : Nat → Lean.Json → Option Effect4.Json
  | 0, _ => none
  | _ + 1, .null => some .null
  | _ + 1, .bool b => some (.bool b)
  | _ + 1, .num n =>
    if n.exponent = 0 ∧ 0 ≤ n.mantissa ∧
        natOfBinary64 (Effect4.Arch.binary64OfNat n.mantissa.toNat) = some n.mantissa.toNat then
      some (.number ⟨Effect4.Arch.binary64OfNat n.mantissa.toNat⟩)
    else none
  | _ + 1, .str s => some (.str s)
  | fuel + 1, .arr js => (js.toList.mapM (ofLeanJson fuel)).map .arr
  | fuel + 1, .obj kvs =>
    (kvs.toList.mapM fun (kv : String × Lean.Json) => (ofLeanJson fuel kv.2).map (kv.1, ·)).map
      .obj

/-- **A number converts only to the natural it was.** Whatever `ofLeanJson` makes of a JSON
number is a non-negative finite binary64 datum from which the reader takes back that number's
natural (`natOfBinary64`, the step `readIn` takes at `.nat`), and that natural is below 2^1024
(`natOfBinary64_finite`). A step of `json-read-exact` at the tool: with `Canonical.ofJson_exact`,
the program a request admits holds the naturals the request wrote, as binary64 hosts read them.
Its consumer is the tool's wire (`Tools.WireText.parseTree`), which reads every request line through it. -/
theorem ofLeanJson_num {fuel : Nat} {n : Lean.JsonNumber} {j : Effect4.Json}
    (h : ofLeanJson (fuel + 1) (.num n) = some j) :
    ∃ x : Effect4.Float64, j = .number x ∧ n.exponent = 0 ∧ 0 ≤ n.mantissa ∧
      natOfBinary64 x.bits = some n.mantissa.toNat ∧
      x.bits.toNat < Effect4.Arch.binary64Infinity ∧ n.mantissa.toNat < 2 ^ 1024 := by
  unfold ofLeanJson at h
  split at h
  · rename_i hn
    cases h
    exact ⟨_, rfl, hn.1, hn.2.1, hn.2.2, natOfBinary64_finite hn.2.2⟩
  · cases h

mutual
/-- **The tree's JSON as Lean's.** -/
def toLeanJson : Effect4.Json → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .number x =>
    match natOfBinary64 x.bits with
    | some n => .num (Lean.JsonNumber.fromNat n)
    | none => .null
  | .str s => .str s
  | .arr js => .arr (toLeanList js).toArray
  | .obj entries => Lean.Json.mkObj (toLeanEntries entries)

/-- A list of the tree's JSON values as Lean's. -/
def toLeanList : List Effect4.Json → List Lean.Json
  | [] => []
  | j :: js => toLeanJson j :: toLeanList js

/-- An object's entries as Lean's. -/
def toLeanEntries : List (String × Effect4.Json) → List (String × Lean.Json)
  | [] => []
  | (k, j) :: entries => (k, toLeanJson j) :: toLeanEntries entries
end

/-- **A value's JSON print, as Lean's JSON**: its generated canonical print with each list as an
array (`Canonical.printArrays`), the one structured projection the tools give of a carrier. It is
the encoding `ts/eff/eff.gen.ts` types, and `Canonical.ofJsonAnyOrder` reads it. -/
def printJson {α : Type} [Canonical α] (a : α) : Lean.Json :=
  toLeanJson (Canonical.printArrays a)

/-! ## A value on the wire: its canonical bytes in hex, or its JSON print

Every carrier a tool takes or gives travels one of two ways, read by one function each, at every
canonical carrier: a program, a filling, a hole table, a row table, service declarations. -/

/-- The nesting a request's JSON may take. -/
def depth : Nat := 4096

/-- **A value from its canonical bytes in lowercase hex**: the store's exact decoder. -/
def ofHex? {α : Type} [Canonical α] (hex : String) : Option α :=
  (bytesOfHex hex.toList).bind Canonical.decode

/-- **A value's canonical bytes**, in lowercase hex. -/
def toHex {α : Type} [Canonical α] (a : α) : String := hexString (Canonical.encode a)

/-- **A value from its JSON print**: its objects in any order, its lists as arrays or as their
cases (`Canonical.ofJsonAnyOrder`). -/
def read? {α : Type} [Canonical α] (j : Lean.Json) : Option α :=
  (ofLeanJson depth j).bind Canonical.ofJsonAnyOrder

/-! ## Where a refused JSON value stops fitting its shape

The reader decides (`read?`); this walk only explains a refusal, as `Api.explain` explains a
build that admission refused. It walks the shape and the author's own JSON together: objects by
key in any order, a list family as an array or as its cases, a field-free sum as one of its
strings. It answers the first place where the JSON leaves the shape, with the path of keys and
indices to it, what the shape wants there and what stands there. Where it finds no fault, it says
nothing, and the refusal stands without a place. -/

/-- A shape as a short name: a primitive, a named definition, or a list, an option or a pair of
those. The catalogue names its forms so (`Tools.Catalogue`). -/
def shapeText : Shape → String
  | .unit => "unit"
  | .bool => "bool"
  | .nat => "nat"
  | .string => "string"
  | .bytes => "bytes"
  | .digest => "digest"
  | .list item => s!"list {shapeText item}"
  | .option item => s!"option {shapeText item}"
  | .pair a b => s!"pair {shapeText a} {shapeText b}"
  | .struct name _ => name
  | .sum name _ => name
  | .ref kind => s!"ref {kind.name}"
  | .anyRef => "anyRef"
  | .named name => name
  | .value => "raw value tree"

/-- **A miss**: the path of keys and indices to the place, what the shape wants there, and what
stands there. -/
structure Miss where
  path : List String := []
  wanted : String
  found : String

/-- The miss one step further in. -/
def Miss.under (step : String) (m : Miss) : Miss := { m with path := step :: m.path }

/-- The miss as JSON: its path joined with dots, and an index in brackets. -/
def Miss.toJson (m : Miss) : Lean.Json :=
  let place := m.path.foldl (fun acc step =>
    if step.all Char.isDigit then acc ++ "[" ++ step ++ "]"
    else if acc.isEmpty then step else acc ++ "." ++ step) ""
  Lean.Json.mkObj [("at", .str place), ("wanted", .str m.wanted), ("found", .str m.found)]

/-- What stands at a place, in words. -/
def foundText : Lean.Json → String
  | .null => "null"
  | .bool b => s!"the Boolean {b}"
  | .num n => s!"the number {n}"
  | .str t => s!"the string {t.quote}"
  | .arr js => s!"an array of {js.size}"
  | .obj _ => "an object"

/-- What a sum wants: its strings, an array, or an object with its case's `_tag`. -/
def sumWanted (name : String) (cases : List (String × Nat × List (String × Shape))) : String :=
  let tags := ", ".intercalate (cases.map (·.1))
  if allNullary cases then s!"{name}: one of the strings {tags}"
  else match listItem? cases with
    | some item => s!"{name}: an array of {shapeText item}"
    | none => s!"{name}: an object whose _tag is one of {tags}"

mutual
/-- The first place where a JSON value leaves a shape, within `fuel` levels. -/
def locateIn (defs : List (String × Shape)) : Nat → Shape → Lean.Json → Option Miss
  | 0, _, _ => none
  | n + 1, shape, j =>
    match shape, j with
    | .named name, j =>
      match lookupAll name defs with
      | s :: _ => locateIn defs n s j
      | [] => none
    | .unit, .null => none
    | .bool, .bool _ => none
    | .nat, .num x =>
      if (ofLeanJson 1 (.num x)).isSome then none
      else some { wanted := "nat: a natural that binary64 holds exactly", found := foundText j }
    | .string, .str _ => none
    | .bytes, .str h | .digest, .str h | .ref _, .str h =>
      if (canonicalHex? h).isSome then none
      else some { wanted := s!"{shapeText shape}: lowercase hex", found := foundText j }
    | .option _, .null => none
    | .option item, j => locateIn defs n item j
    | .list item, .arr js => locateItems defs n item 0 js.toList
    | .pair a b, .arr js =>
      match js.toList with
      | [x, y] =>
        match locateIn defs n a x with
        | some m => some (m.under "0")
        | none => (locateIn defs n b y).map (·.under "1")
      | _ => some { wanted := shapeText shape ++ ": an array of two", found := foundText j }
    | .struct name fields, .obj _ => locateFields defs n name fields j
    | .sum name cases, j =>
      let wanted := sumWanted name cases
      match listItem? cases, j with
      | some item, .arr js => locateItems defs n item 0 js.toList
      | _, .str t =>
        if allNullary cases && cases.any (·.1 == t) then none
        else some { wanted, found := foundText j }
      | _, .obj _ =>
        if allNullary cases then some { wanted, found := foundText j }
        else match j.getObjVal? "_tag" with
          | .ok (.str t) =>
            match cases.find? (·.1 == t) with
            | some (_, _, fields) => locateFields defs n t fields j
            | none => some ((Miss.mk [] wanted (foundText (.str t))).under "_tag")
          | _ => some { wanted, found := "an object with no string _tag" }
      | _, _ => some { wanted, found := foundText j }
    | .anyRef, .obj _ => none
    | shape, j => some { wanted := shapeText shape, found := foundText j }

/-- The first miss among a list's items, each under its index. -/
def locateItems (defs : List (String × Shape)) : Nat → Shape → Nat → List Lean.Json → Option Miss
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | n + 1, item, i, j :: js =>
    match locateIn defs n item j with
    | some m => some (m.under (toString i))
    | none => locateItems defs n item (i + 1) js

/-- The first miss among an object's fields: a field the shape names and the object lacks, a
field's value, or a key the shape does not name. -/
def locateFields (defs : List (String × Shape)) : Nat → String → List (String × Shape) →
    Lean.Json → Option Miss
  | 0, _, _, _ => none
  | n + 1, owner, fields, j =>
    let named := "_tag" :: fields.map (·.1)
    let extra := match j with
      | .obj kvs => (kvs.toList.map fun (kv : String × Lean.Json) => kv.1).find? fun k =>
          !named.contains k
      | _ => none
    match extra with
    | some k =>
      some { wanted := s!"{owner}: the fields {", ".intercalate (fields.map Prod.fst)}",
             found := s!"the key {k.quote}" }
    | none => locateEach defs n owner fields j

/-- Each field of a shape, in its order, read at its key. -/
def locateEach (defs : List (String × Shape)) : Nat → String → List (String × Shape) →
    Lean.Json → Option Miss
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | n + 1, owner, (k, s) :: rest, j =>
    match j.getObjVal? k with
    | .error _ => some { wanted := s!"{owner}: the field {k} ({shapeText s})", found := "none" }
    | .ok v =>
      match locateIn defs n s v with
      | some m => some (m.under k)
      | none => locateEach defs n owner rest j
end

/-- **Where a carrier's JSON stops fitting its shape**, if the walk finds a place. -/
def locate {α : Type} [Canonical α] (j : Lean.Json) : Option Miss :=
  let doc := Canonical.shape α
  locateIn doc.defs depth doc.root j

end Tools.JsonBridge
