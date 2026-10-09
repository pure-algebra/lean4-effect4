import Effect4.Store.Domain.ShapeRead
import Effect4.Store.Domain.ProgramWire

/-!
# Probe MCP-1 (finite): a tool's JSON Schema as a fold of the store's shape alphabet

Seat MCP, 2026-10-09. Evidence for `docs/research/2026-10-09-mcp-code-mode-design.md` §4. Not
part of the tree, reached by no root, built by no target. Run it with:

    scratch/lean-slot.sh lake env lean docs/research/2026-10-09-mcp-code-mode/ShapeSchemaProbe.lean

**The question.** Every canonical carrier states its shape (`Canonical.shape`,
`src/Effect4/Store/Domain/Canonical.lean`). The JSON print (`ShapeDoc.print`,
`src/Effect4/Store/Domain/Shape.lean`) and the JSON reader (`Canonical.ofJson`,
`src/Effect4/Store/Domain/ShapeRead.lean`) are two images of that shape. Can the JSON Schema an
MCP tool advertises be a third image of the same shape, computed by one fold, and how does it
relate to the reader?

**What it does.**

1. `schemaOf`: one structural fold from `Shape` to a JSON Schema 2020-12 node, read off the
   printer's rules case by case (null, boolean, natural, string, hex bytes, list, option, pair,
   struct, sum with `_tag`, reference, named by `$ref`).
2. `valid`: a validator of exactly the keywords `schemaOf` writes, with fuel.
3. Checks on the wire corpus (`Effect4.Program.Wire.Corpus.all`, eight programs) at the program
   shape (`Canonical.shape (Eff NativeOp)`): the print of each program validates, and reads back.
4. Red controls: an extra field, an unknown tag and a negative natural are refused by both the
   validator and the reader; a natural above `2^53` that binary64 holds is refused by the schema and
   read by the reader (the schema is narrower); objects out of shape order validate, are refused by
   `ofJson` and read by `ofJsonAnyOrder` (the reader a tool must use is the one with the normaliser).
5. Measures: the number of named shapes and the rendered size of the program schema.

Every result is a finite evaluation over named inputs: it proves nothing about other values.
-/

set_option autoImplicit false

namespace ProbeMcp

open Effect4 Effect4.Store Effect4.Program
open Effect4.Arch (Json.ofNat)

/-- The JSON profile's bound for a natural: `2^53`, the last natural such that every natural up
to it is exact in binary64 (`Effect4.Arch.binary64OfNat`). -/
def natMax : Nat := 9007199254740992

def jstr (s : String) : Json := .str s
def jobj (kvs : List (String × Json)) : Json := .obj kvs

mutual
/-- **The schema of a shape**: one node of JSON Schema 2020-12 per constructor of the Q5
alphabet, read off `printIn`'s rules. A `named` shape refers to `$defs`. -/
def schemaOf : Shape → Json
  | .unit => jobj [("type", jstr "null")]
  | .bool => jobj [("type", jstr "boolean")]
  | .nat => jobj [("type", jstr "integer"), ("minimum", Json.ofNat 0), ("maximum", Json.ofNat natMax)]
  | .string => jobj [("type", jstr "string")]
  | .bytes => jobj [("type", jstr "string"), ("pattern", jstr "^([0-9a-f]{2})*$")]
  | .digest => jobj [("type", jstr "string"), ("pattern", jstr "^[0-9a-f]{64}$")]
  | .list item => jobj [("type", jstr "array"), ("items", schemaOf item)]
  | .option item => jobj [("anyOf", .arr [schemaOf item, jobj [("type", jstr "null")]])]
  | .pair a b => jobj [("type", jstr "array"), ("prefixItems", .arr [schemaOf a, schemaOf b]),
      ("minItems", Json.ofNat 2), ("maxItems", Json.ofNat 2)]
  | .struct _ fields => objectSchema [] fields
  | .sum _ cases =>
    if allNullary cases then jobj [("enum", .arr (caseNames cases))]
    else jobj [("oneOf", .arr (caseSchemas cases))]
  | .ref _ => jobj [("type", jstr "string"), ("pattern", jstr "^[0-9a-f]{64}$")]
  | .anyRef => jobj [("type", jstr "object"),
      ("properties", jobj [("kind", jobj [("type", jstr "string")]),
        ("address", jobj [("type", jstr "string"), ("pattern", jstr "^[0-9a-f]{64}$")])]),
      ("required", .arr [jstr "kind", jstr "address"]), ("additionalProperties", .bool false)]
  | .named n => jobj [("$ref", jstr ("#/$defs/" ++ n))]

/-- An object whose properties are the fields, all required, and no other. `lead` comes first
(a case's `_tag`). -/
def objectSchema (lead : List (String × Json)) (fields : List (String × Shape)) : Json :=
  jobj [("type", jstr "object"),
    ("properties", jobj (lead ++ fieldSchemas fields)),
    ("required", .arr ((lead.map fun kv => jstr kv.1) ++ fieldNames fields)),
    ("additionalProperties", .bool false)]

def fieldSchemas : List (String × Shape) → List (String × Json)
  | [] => []
  | (n, s) :: rest => (n, schemaOf s) :: fieldSchemas rest

def fieldNames : List (String × Shape) → List Json
  | [] => []
  | (n, _) :: rest => jstr n :: fieldNames rest

def caseNames : List (String × Nat × List (String × Shape)) → List Json
  | [] => []
  | (n, _, _) :: rest => jstr n :: caseNames rest

def caseSchemas : List (String × Nat × List (String × Shape)) → List Json
  | [] => []
  | (n, _, fields) :: rest =>
    objectSchema [("_tag", jobj [("const", jstr n)])] fields :: caseSchemas rest
end

/-- The first binding of each name, in table order: the binding `headShape` reads. -/
def firstBindings : List (String × Shape) → List (String × Shape) → List (String × Shape)
  | [], acc => acc.reverse
  | (n, s) :: rest, acc =>
    if acc.any (fun kv => kv.1 == n) then firstBindings rest acc else firstBindings rest ((n, s) :: acc)

/-- **The schema of a shape document**: the root's node, with every name's first binding under
`$defs`. -/
def docSchema (doc : ShapeDoc) : List (String × Json) × Json :=
  ((firstBindings doc.defs []).map fun (n, s) => (n, schemaOf s), schemaOf doc.root)

/-! ## A validator of the keywords `schemaOf` writes -/

/-- An integer's value, read from its binary64 datum: a natural, or the negation of one. -/
def intOf? (j : Json) : Option Int :=
  match j with
  | .number x =>
    match natOfBinary64 x.bits with
    | some n => some (Int.ofNat n)
    | none =>
      -- the sign bit set, and the magnitude a natural
      if x.bits.toNat ≥ 2 ^ 63 then
        (natOfBinary64 (UInt64.ofNat (x.bits.toNat - 2 ^ 63))).map fun n => -(Int.ofNat n)
      else none
  | _ => none

def typeOk (t : String) (j : Json) : Bool :=
  match t, j with
  | "null", .null => true
  | "boolean", .bool _ => true
  | "integer", j => (intOf? j).isSome
  | "string", .str _ => true
  | "array", .arr _ => true
  | "object", .obj _ => true
  | _, _ => false

/-- The two patterns `schemaOf` writes, decided by the reader's own hex reader. -/
def patternOk (p : String) (s : String) : Bool :=
  if p == "^([0-9a-f]{2})*$" then (canonicalHex? s).isSome
  else if p == "^[0-9a-f]{64}$" then
    match canonicalHex? s with
    | some b => b.length == 32
    | none => false
  else false

def lookup (k : String) : List (String × Json) → Option Json
  | [] => none
  | (k', v) :: rest => if k' == k then some v else lookup k rest

def strs : List Json → List String
  | [] => []
  | .str s :: rest => s :: strs rest
  | _ :: rest => strs rest

/-- **Validate** an instance against a schema node, within `fuel` steps, `$ref` resolved in
`defs`. Each keyword of the node must hold. -/
def valid (defs : List (String × Json)) : Nat → Json → Json → Bool
  | 0, _, _ => false
  | fuel + 1, .obj kws, j => kws.all fun (k, v) => keyword defs fuel kws k v j
  | _ + 1, _, _ => false
where
  keyword (defs : List (String × Json)) (fuel : Nat) (kws : List (String × Json)) :
      String → Json → Json → Bool
    | "type", .str t, j => typeOk t j
    | "minimum", m, j => match intOf? m, intOf? j with
      | some lo, some x => lo ≤ x
      | _, _ => false
    | "maximum", m, j => match intOf? m, intOf? j with
      | some hi, some x => x ≤ hi
      | _, _ => false
    | "pattern", .str p, .str s => patternOk p s
    | "pattern", _, _ => false
    | "items", s, .arr xs =>
      -- 2020-12: `items` applies after the `prefixItems`
      let skip := match lookup "prefixItems" kws with
        | some (.arr ps) => ps.length
        | _ => 0
      (xs.drop skip).all fun x => valid defs fuel s x
    | "items", _, _ => true
    | "prefixItems", .arr ps, .arr xs => (ps.zip xs).all fun (s, x) => valid defs fuel s x
    | "prefixItems", _, _ => true
    | "minItems", m, .arr xs => match intOf? m with
      | some n => (n : Int) ≤ xs.length
      | none => false
    | "maxItems", m, .arr xs => match intOf? m with
      | some n => (xs.length : Int) ≤ n
      | none => false
    | "minItems", _, _ => true
    | "maxItems", _, _ => true
    | "properties", .obj props, .obj entries =>
      entries.all fun (k, x) => match lookup k props with
        | some s => valid defs fuel s x
        | none => true
    | "properties", _, _ => true
    | "required", .arr names, .obj entries =>
      (strs names).all fun n => (lookup n entries).isSome
    | "required", _, _ => true
    | "additionalProperties", .bool false, .obj entries =>
      match lookup "properties" kws with
      | some (.obj props) => entries.all fun (k, _) => (lookup k props).isSome
      | _ => entries.isEmpty
    | "additionalProperties", _, _ => true
    | "const", c, j => c == j
    | "enum", .arr cs, j => cs.any fun c => c == j
    | "anyOf", .arr ss, j => ss.any fun s => valid defs fuel s j
    | "oneOf", .arr ss, j => (ss.filter fun s => valid defs fuel s j).length == 1
    | "$ref", .str r, j =>
      if r.startsWith "#/$defs/" then
        match lookup (r.drop 8).toString defs with
        | some s => valid defs fuel s j
        | none => false
      else false
    | _, _, _ => false

/-- The steps a validation gets: generous, eight a JSON node. -/
def fuelFor (j : Json) : Nat := 64 * readBudget j + 256

/-- Validate an instance against a shape document's schema. -/
def validDoc (doc : ShapeDoc) (j : Json) : Bool :=
  let (defs, root) := docSchema doc
  valid defs (fuelFor j) root j

/-! ## A renderer, for the measures and the listing -/

mutual
def render : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .number x => match natOfBinary64 x.bits with
    | some n => toString n
    | none => "<binary64>"
  | .str s => "\"" ++ s ++ "\""
  | .arr xs => "[" ++ ",".intercalate (renderList xs) ++ "]"
  | .obj kvs => "{" ++ ",".intercalate (renderEntries kvs) ++ "}"
def renderList : List Json → List String
  | [] => []
  | x :: xs => render x :: renderList xs
def renderEntries : List (String × Json) → List String
  | [] => []
  | (k, v) :: rest => ("\"" ++ k ++ "\":" ++ render v) :: renderEntries rest
end

/-! ## The program shape and the corpus -/

abbrev P := Eff NativeOp

def progDoc : ShapeDoc := Canonical.shape P

def printOf (p : P) : Json := Canonical.print p

/-- Replace the value at a key of a JSON object, at the root. -/
def setKey (k : String) (v : Json) : Json → Json
  | .obj kvs => .obj (kvs.map fun (k', v') => if k' == k then (k', v) else (k', v'))
  | j => j

/-- `p42`'s print, with its natural replaced. -/
def p42With (n : Json) : Json :=
  jobj [("_tag", jstr "succeed"), ("value", jobj [("_tag", jstr "lit"),
    ("value", jobj [("_tag", jstr "nat"), ("value", n)])])]

/-- A negative number: the binary64 of `1` with the sign bit set. -/
def minusOne : Json := .number ⟨UInt64.ofNat ((Effect4.Arch.binary64OfNat 1).toNat + 2 ^ 63)⟩

-- Reverse the entries of every object: out of shape order.
mutual
def reverseObjs : Json → Json
  | .obj kvs => .obj (reverseEntries kvs).reverse
  | .arr xs => .arr (reverseList xs)
  | j => j
def reverseList : List Json → List Json
  | [] => []
  | x :: xs => reverseObjs x :: reverseList xs
def reverseEntries : List (String × Json) → List (String × Json)
  | [] => []
  | (k, v) :: rest => (k, reverseObjs v) :: reverseEntries rest
end

end ProbeMcp

open ProbeMcp Effect4 Effect4.Store Effect4.Program

-- the program shape: its root and the number of names it binds
#eval s!"root: {repr progDoc.root}; named shapes (first bindings): {(firstBindings progDoc.defs []).length}"

-- green (tested): the print of every corpus program validates against the derived schema
#eval Wire.Corpus.all.map fun (name, p) => (name, validDoc progDoc (printOf p))

-- green (tested): and reads back through the shape reader, as the round trip on the JSON profile says
#eval Wire.Corpus.all.map fun (name, p) => (name, Canonical.ofJson (α := P) (printOf p) == some p)

-- red (tested): an extra field at the root; the schema refuses it, and so does the reader
#eval let j := match printOf Wire.Corpus.p42 with
    | .obj kvs => Json.obj (kvs ++ [("extra", .null)])
    | j => j
  (validDoc progDoc j, (Canonical.ofJson (α := P) j).isSome)

-- red (tested): an unknown constructor tag
#eval let j := setKey "_tag" (jstr "succeeed") (printOf Wire.Corpus.p42)
  (validDoc progDoc j, (Canonical.ofJson (α := P) j).isSome)

-- red for the schema, green for the reader (tested): a negative number. The schema refuses it.
-- The reader reads it, as the natural 2^2048: `binary64OfNat` does not saturate above 2^1024,
-- so its image holds negative and non-finite bit patterns, and `natOfBinary64` reads them back.
#eval (validDoc progDoc (p42With minusOne), (Canonical.ofJson (α := P) (p42With minusOne)).isSome)
#eval (natOfBinary64 (UInt64.ofNat ((Effect4.Arch.binary64OfNat 1).toNat + 2 ^ 63)) == some (2 ^ 2048),
  Effect4.Arch.binary64OfNat (2 ^ 2048) == UInt64.ofNat ((Effect4.Arch.binary64OfNat 1).toNat + 2 ^ 63))
-- and 2^1024 prints as the bit pattern of +Infinity, which no JSON text spells
#eval Effect4.Arch.binary64OfNat (2 ^ 1024) == 0x7FF0000000000000

-- control (tested): 2^53 itself; both accept
#eval (validDoc progDoc (p42With (Effect4.Arch.Json.ofNat (2 ^ 53))),
  (Canonical.ofJson (α := P) (p42With (Effect4.Arch.Json.ofNat (2 ^ 53)))).isSome)

-- red for the iff (tested): 2^53 + 2, which binary64 holds: the schema refuses, the reader reads
#eval (validDoc progDoc (p42With (Effect4.Arch.Json.ofNat (2 ^ 53 + 2))),
  (Canonical.ofJson (α := P) (p42With (Effect4.Arch.Json.ofNat (2 ^ 53 + 2)))).isSome)

-- red for the plain reader (tested): objects out of shape order validate; `ofJson` refuses them,
-- and `ofJsonAnyOrder` (the named normaliser, `ShapeDoc.order`) reads them
#eval Wire.Corpus.all.map fun (name, p) =>
  let j := reverseObjs (printOf p)
  (name, validDoc progDoc j, (Canonical.ofJson (α := P) j).isSome,
    Canonical.ofJsonAnyOrder (α := P) j == some p)

-- measure: the rendered size of the program's schema, its root and its definitions
#eval let (defs, root) := docSchema progDoc
  let text := render (jobj [("$schema", jstr "https://json-schema.org/draft/2020-12/schema"),
    ("$defs", jobj defs), ("$ref", (match root with
      | .obj [("$ref", r)] => r
      | _ => .null))])
  s!"definitions: {defs.length}; rendered bytes: {text.utf8ByteSize}"

-- listing: the `Eff` family's constructors as the builder API reads them, each with its fields
#eval match firstBindings progDoc.defs [] |>.find? (fun kv => kv.1 == "Eff") with
  | some (_, .sum _ cases) =>
    cases.map fun (c : String × Nat × List (String × Shape)) => (c.1, c.2.2.map fun (f : String × Shape) => f.1)
  | _ => []
