import Lean.Data.Json

/-!
# Conform.Manifest.Readers — a family's constructor list, as each producer wrote it

**What it is.** Nine total readers, each recovering *"the constructors of one family, in order, as
one artefact spells them"* from a text or JSON file, plus the two normalisations that turn a
foreign spelling back into a Lean constructor name. A reader never guesses: it returns
`Except String (Array String)` and its error names the line it could not parse. That is what makes
a mirror check able to say `unresolved` rather than `pass` when a grammar stops working.

**Depends on.** `Lean.Json` only. No repository module, no `Effect4` name: which file, which
family, which reader and which normalisation are configuration (`Conform.Manifest.Mirror`, and for
this tree `tools/Conform/Effect4/mirrors.json`).

**The nine grammars**, each documented at its reader and each a *text* grammar — no TypeScript
parser, no OCaml parser, deliberately:

| id | shape | example artefact |
| --- | --- | --- |
| `json-inventory` | `{"families":[{"family":…,"constructors":[…]}]}` | a frozen family inventory |
| `text-manifest` | `Name (alias) inductive: c1 c2(arg) …` | a generator's manifest line |
| `ts-tag-union` | `export type X =` then `\| { readonly _tag: "c" … }` | a generated `.gen.ts` type |
| `ts-tagged-union` | `export const X = Schema.TaggedUnion({` then `c: {…},` | the schema beside it |
| `ocaml-ctor-names` | `let ctor_names_t : string list = ["a"; "b"]` | a generated name table |
| `ocaml-type-block` | `type [_] t =` then `\| Ctor …` | a variant **or** a GADT block |
| `ocaml-match-arms` | a `function` / `match … with` header then `\| Ctor … ->` | a hand-written arm list |
| `ts-literals` | `export const X = Schema.Literals(["a", "b"])` | the schema of an all-nullary family |
| `ts-switch-cases` | a header line then `case "c":` arms | a generated `.gen.ts` dispatch |

**Properties.**
* **Total and refusing.** Every reader returns an `Except`; none of them defaults, truncates or
  skips a line it does not understand — *by construction*. A reader that cannot find its key says
  so with the key it looked for.
* **Order is data.** Every reader returns the constructors in the artefact's own order, so a
  reordering is visible; a check that only wants the set can still take one — *by construction*.
* **Normalisation is separate from parsing.** A reader returns the artefact's own spellings; the
  mapping back to Lean names is `Rename` and a per-mirror alias table, which are configuration —
  *by construction*.
-/

namespace Conform.Manifest

open Lean (Json)

/-! ## 0. Small text helpers -/

/-- The lines of a file, `\r` stripped, so a manifest written on the PC reads the same. -/
def lines (text : String) : Array String :=
  (text.splitOn "\n").toArray.map fun l => l.replace "\r" ""

/-- The ASCII trim, as a `String`. -/
def tr (s : String) : String := s.trimAscii.toString

/-- `String.drop`, as a `String`. -/
def dropS (s : String) (n : Nat) : String := (s.drop n).toString

/-- The number of leading spaces of a line. -/
def indentOf (l : String) : Nat :=
  (l.toList.takeWhile (· == ' ')).length

/-- The identifier at the front of `s`: letters, digits, `_`, `'`. Empty when `s` starts with
something else. -/
def leadingIdent (s : String) : String :=
  String.ofList (s.toList.takeWhile fun c => c.isAlphanum || c == '_' || c == '\'')

/-- Split on spaces that are **outside** parentheses, so `interrupt(term option)` is one item and
not two. Refuses nothing: an unbalanced line simply yields one long item, which the caller's
comparison then reports. -/
def splitTopLevel (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : List Char := []
  let mut depth := 0
  for c in s.toList do
    if c == '(' then depth := depth + 1; cur := c :: cur
    else if c == ')' then depth := depth - 1; cur := c :: cur
    else if c == ' ' && depth == 0 then
      if !cur.isEmpty then out := out.push (String.ofList cur.reverse)
      cur := []
    else cur := c :: cur
  if !cur.isEmpty then out := out.push (String.ofList cur.reverse)
  return out

/-- The text between the first pair of `"` in `s`, or `none`. -/
def quoted? (s : String) : Option String :=
  match s.splitOn "\"" with
  | _ :: v :: _ => some v
  | _ => none

/-! ## 1. Normalisation: a foreign spelling back to a Lean constructor name -/

/-- How an artefact's constructor spelling maps back to the Lean constructor's short name. -/
inductive Rename
  /-- The artefact writes the Lean name. -/
  | identity
  /-- OCaml's convention: an initial capital and `_`-separated words. `Exit_of ↦ exitOf`,
  `Never ↦ never`. Applied after the mirror's `stripPrefix`, so `Ty_exitOf ↦ exitOf` with
  `stripPrefix = "Ty_"`. -/
  | ocamlCtor
deriving DecidableEq, Inhabited

namespace Rename

def id : Rename → String
  | .identity => "identity"
  | .ocamlCtor => "ocaml-ctor"

/-- Lower the first character, then collapse `_x` into `X`. -/
private def ocamlToCamel (s : String) : String := Id.run do
  match s.toList with
  | [] => return ""
  | c :: rest =>
    let mut out : List Char := [c.toLower]
    let mut underscore := false
    for d in rest do
      if d == '_' then underscore := true
      else if underscore then out := d.toUpper :: out; underscore := false
      else out := d :: out
    return String.ofList out.reverse

def apply : Rename → String → String
  | .identity, s => s
  | .ocamlCtor, s => ocamlToCamel s

end Rename

/-! ## 2. The readers

Each takes the file's text and the key that names the family *in that artefact's own vocabulary*
(a Lean name for a manifest, `Ty` for a TypeScript type, `ty` for an OCaml one). -/

/-- The keys a JSON inventory uses, so the reader is not welded to one file's field names. -/
structure JsonShape where
  /-- The top-level key holding the array of families. -/
  array : String := "families"
  /-- The key naming a family inside one entry. -/
  key : String := "family"
  /-- The key holding the constructor list. -/
  list : String := "constructors"
deriving Inhabited

/-- `{"families": [{"family": "…", "constructors": ["a", "b"]}, …]}` — the shape a frozen family
inventory has. Refuses a file that is not JSON, a constructor list that is not an array of
strings, and a key no entry carries. -/
def jsonInventory (shape : JsonShape) (text : String) (key : String) :
    Except String (Array String) := do
  let j ← Json.parse text
  let arr ← match j.getObjVal? shape.array with
    | .ok (.arr xs) => pure xs
    | .ok _ => throw s!"`{shape.array}` is not an array"
    | .error e => throw s!"no `{shape.array}` key: {e}"
  for entry in arr do
    match entry.getObjVal? shape.key with
    | .ok (.str n) =>
      if n == key then
        match entry.getObjVal? shape.list with
        | .ok (.arr cs) =>
          let mut out : Array String := #[]
          for c in cs do
            match c with
            | .str s => out := out.push s
            | _ => throw s!"`{key}`: a `{shape.list}` entry is not a string"
          return out
        | .ok _ => throw s!"`{key}`: `{shape.list}` is not an array"
        | .error _ => throw s!"`{key}`: no `{shape.list}` key"
    | _ => pure ()
  throw s!"no entry with `{shape.key}` = `{key}`"

/-- `Effect4.Program.Ty (ty) inductive: never unit nat … handle(string) option(ty)` — a generator's
one-line-per-family manifest. The key is the line's first whitespace-separated token — a dotted
Lean name, not an identifier; items are separated by spaces **outside** parentheses, so
`interrupt(term option)` is one item; an item's constructor is the text before its first `(`. A
`structure:` line lists **fields**, not constructors, and is refused as such rather than read as a
one-constructor family. -/
def textManifest (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  for h : i in [0:ls.size] do
    let l := ls[i]
    let t := tr l
    if t.isEmpty then continue
    -- the key is the whole first token, dots included: a Lean name, not an identifier
    if (t.splitOn " ").headD "" != key then continue
    match l.splitOn ": " with
    | head :: rest =>
      if (head.splitOn "structure").length > 1 then
        throw s!"line {i + 1}: `{key}` is a structure line; it lists fields, not constructors"
      if (head.splitOn "inductive").length == 1 then
        throw s!"line {i + 1}: `{key}` is neither an `inductive:` nor a `structure:` line"
      let body := ": ".intercalate rest
      let items := (splitTopLevel body).filter fun s => !(tr s).isEmpty
      let mut out : Array String := #[]
      for it in items do
        let n := leadingIdent (tr it)
        if n.isEmpty then throw s!"line {i + 1}: `{it}` does not start with a constructor name"
        out := out.push n
      return out
    | [] => throw s!"line {i + 1}: no `: ` between the header and the constructors"
  throw s!"no manifest line whose first token is `{key}`"

/-- ```
export type Ty =
  | { readonly _tag: "never" }
  | { readonly _tag: "handle"; readonly target: string }
```
The generated TypeScript union. The block is the run of lines whose trimmed form starts with `|`
right after `export type <key> =`; each must carry a `_tag: "…"` literal. -/
def tsTagUnion (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  let header := "export type " ++ key ++ " ="
  for h : i in [0:ls.size] do
    if tr ls[i] == header then
      let mut out : Array String := #[]
      let mut j := i + 1
      while hj : j < ls.size do
        let l := tr ls[j]
        if !l.startsWith "|" then break
        match l.splitOn "_tag: " with
        | _ :: rest :: _ =>
          match quoted? rest with
          | some tag => out := out.push tag
          | none => throw s!"line {j + 1}: `_tag:` is not followed by a string literal"
        | _ => throw s!"line {j + 1}: an alternative of `{key}` carries no `_tag:`"
        j := j + 1
      if out.isEmpty then throw s!"`{header}` has no alternatives"
      return out
  throw s!"no `{header}` line"

/-- ```
export const Ty = Schema.TaggedUnion({
  never: {},
  handle: { target: Schema.String },
})
```
The schema beside the type. The block runs to the first line whose trimmed form starts with `})`;
every non-blank line inside must be `<name>: …`. -/
def tsTaggedUnion (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  let header := "export const " ++ key ++ " = Schema.TaggedUnion({"
  for h : i in [0:ls.size] do
    if tr ls[i] == header then
      let mut out : Array String := #[]
      let mut j := i + 1
      let mut closed := false
      while hj : j < ls.size do
        let l := tr ls[j]
        if l.startsWith "})" then
          closed := true
          break
        if !l.isEmpty then
          let n := leadingIdent l
          if n.isEmpty || !(dropS l n.length).startsWith ":" then
            throw s!"line {j + 1}: `{l}` is not a `<name>: …` member of `{key}`"
          out := out.push n
        j := j + 1
      unless closed do throw s!"`{key}`'s tagged union is never closed"
      if out.isEmpty then throw s!"`{key}`'s tagged union has no members"
      return out
  throw s!"no `{header}` line"

/-- `let ctor_names_ty : string list = ["never"; "unit"; …]` — a generated OCaml name table: the
one artefact that already *is* the list, so it needs no normalisation. -/
def ocamlCtorNames (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  let header := "let ctor_names_" ++ key ++ " : string list = ["
  for h : i in [0:ls.size] do
    let l := ls[i]
    if l.startsWith header then
      match (dropS l header.length).splitOn "]" with
      | body :: _ =>
        let items := (body.splitOn ";").filter fun s => !(tr s).isEmpty
        let mut out : Array String := #[]
        for it in items do
          match quoted? it with
          | some s => out := out.push s
          | none => throw s!"line {i + 1}: `{tr it}` is not a string literal"
        return out
      | [] => throw s!"line {i + 1}: the list is never closed by `]`"
  throw s!"no `{header}…` line"

/-- ```
type _ ty =
  | Never : never ty
  | Exit_of : 'a ty * 'e ty -> ('a, 'e) exit ty
```
or the plain variant
```
type ty =
  | Ty_never
  | Ty_handle of string
```
`key` is the type's spelling after `type ` or `and ` — `_ ty` for the GADT above, `ty` for the
variant. The block is the run of lines whose trimmed form starts with `|`, **one constructor per
line**; a constructor split across lines is outside this grammar, and a check that meets one must
say so rather than guess. -/
def ocamlTypeBlock (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  for h : i in [0:ls.size] do
    let l := tr ls[i]
    if l == "type " ++ key ++ " =" || l == "and " ++ key ++ " =" then
      let mut out : Array String := #[]
      let mut j := i + 1
      while hj : j < ls.size do
        let t := tr ls[j]
        if !t.startsWith "|" then break
        let n := leadingIdent (tr (dropS t 1))
        if n.isEmpty then throw s!"line {j + 1}: `{t}` has no constructor name after `|`"
        out := out.push n
        j := j + 1
      if out.isEmpty then throw s!"`type {key} =` is followed by no `|` alternative"
      return out
  throw s!"no `type {key} =` or `and {key} =` line"

/-- ```
export const tyJson = (v: Ty): Json => {
  switch (v._tag) {
    case "never": return ["never"]
```
A generated TypeScript dispatch. `key` is the header line, trimmed; the block is the run of
`case "<name>":` lines after it, ending at the first line whose trimmed form starts with `}`. A
`default:` line is **not** a constructor and is refused, because in this grammar a `default` is
exactly the drift hazard the audit exists for and must not be read as one more arm. -/
def tsSwitchCases (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  for h : i in [0:ls.size] do
    if tr ls[i] == key then
      let mut out : Array String := #[]
      let mut j := i + 1
      while hj : j < ls.size do
        let t := tr ls[j]
        if t.startsWith "}" then break
        if t.startsWith "switch " || t.isEmpty then
          j := j + 1
          continue
        if t.startsWith "default:" then
          throw s!"line {j + 1}: `{key}` has a `default:` arm; this grammar reads named cases only"
        if !t.startsWith "case " then
          throw s!"line {j + 1}: `{t}` is not a `case \"…\":` of `{key}`"
        match quoted? t with
        | some n => out := out.push n
        | none => throw s!"line {j + 1}: `{t}` has no string literal after `case`"
        j := j + 1
      if out.isEmpty then throw s!"`{key}` has no `case` arm"
      return out
  throw s!"no line equal to `{key}`"

/-- `export const RowKind = Schema.Literals(["sync", "async", "program"])` — the generated schema
of a family whose constructors are all nullary, which the generator writes as a union of string
literals rather than as a tagged union. -/
def tsLiterals (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  let header := "export const " ++ key ++ " = Schema.Literals(["
  for h : i in [0:ls.size] do
    let l := tr ls[i]
    if l.startsWith header then
      match (dropS l header.length).splitOn "]" with
      | body :: _ =>
        let items := (body.splitOn ",").filter fun s => !(tr s).isEmpty
        let mut out : Array String := #[]
        for it in items do
          match quoted? it with
          | some s => out := out.push s
          | none => throw s!"line {i + 1}: `{tr it}` is not a string literal"
        return out
      | [] => throw s!"line {i + 1}: the literal list is never closed by `]`"
  throw s!"no `{header}…` line"

/-- A hand-written OCaml arm list: `key` is a whole header line, trimmed — typically
`let rec key : ty -> int list = function` — and the block is the run of `| Ctor …` lines at the
indentation of the first of them, ending at the first non-blank line indented *less* than that (so
the next `let` ends it). A hand copy has no other stable anchor, and naming the line makes the
configuration say exactly what it pinned.

One allowance, because it is the other half of the same idiom: a single `match … with` line may
stand between the header and the arms (`let rec json_ty (v : ty) : … =` then `  match v with`).
Anything else between them is a refusal. -/
def ocamlMatchArms (text : String) (key : String) : Except String (Array String) := do
  let ls := lines text
  for h : i in [0:ls.size] do
    if tr ls[i] == key then
      let mut out : Array String := #[]
      let mut j := i + 1
      let mut armIndent : Option Nat := none
      let mut allowedMatch := true
      while hj : j < ls.size do
        let raw := ls[j]
        let t := tr raw
        if t.isEmpty then
          j := j + 1
          continue
        match armIndent with
        | none =>
          if allowedMatch && t.startsWith "match " && t.endsWith " with" then
            allowedMatch := false
            j := j + 1
            continue
          if !t.startsWith "|" then
            throw s!"line {j + 1}: the line after `{key}` is neither `match … with` nor an `|` alternative"
          armIndent := some (indentOf raw)
          let n := leadingIdent (tr (dropS t 1))
          if n.isEmpty then throw s!"line {j + 1}: `{t}` has no constructor name after `|`"
          out := out.push n
        | some ind =>
          if indentOf raw < ind then break
          if indentOf raw == ind && t.startsWith "|" then
            let n := leadingIdent (tr (dropS t 1))
            if n.isEmpty then throw s!"line {j + 1}: `{t}` has no constructor name after `|`"
            out := out.push n
        j := j + 1
      if out.isEmpty then throw s!"`{key}` is followed by no `|` alternative"
      return out
  throw s!"no line equal to `{key}`"

/-! ## 3. The reader table

The one place a configuration's `reader` string becomes a function. A new grammar is one entry
here and one row in the table above; nothing else in `Conform` changes. -/

/-- A reader as the configuration selects it. `unresolved` is **not** a reader: it is the honest
declaration that an artefact restates the family in a form no text grammar recovers — a
hand-written checker keyed on the *target's* vocabulary, say — so the check owes a row saying so
rather than silently omitting the artefact from the census. -/
inductive Kind
  | jsonInventory (shape : JsonShape)
  | textManifest
  | tsTagUnion
  | tsTaggedUnion
  | ocamlCtorNames
  | ocamlTypeBlock
  | ocamlMatchArms
  | tsLiterals
  | tsSwitchCases
  | unresolved (reason : String)
deriving Inhabited

namespace Kind

def id : Kind → String
  | .jsonInventory _ => "json-inventory"
  | .textManifest => "text-manifest"
  | .tsTagUnion => "ts-tag-union"
  | .tsTaggedUnion => "ts-tagged-union"
  | .ocamlCtorNames => "ocaml-ctor-names"
  | .ocamlTypeBlock => "ocaml-type-block"
  | .ocamlMatchArms => "ocaml-match-arms"
  | .tsLiterals => "ts-literals"
  | .tsSwitchCases => "ts-switch-cases"
  | .unresolved _ => "unresolved"

def isUnresolved : Kind → Option String
  | .unresolved reason => some reason
  | _ => none

end Kind

/-- Run the reader. `unresolved` never runs: the caller branches on `Kind.isUnresolved` first.
Named `readWith` at the `Manifest` level, not `Kind.read`, so that each arm's right-hand side
names the reader function and not the constructor of the same name. -/
def readWith : Kind → (text : String) → (key : String) → Except String (Array String)
  | .jsonInventory shape, t, k => jsonInventory shape t k
  | .textManifest, t, k => textManifest t k
  | .tsTagUnion, t, k => tsTagUnion t k
  | .tsTaggedUnion, t, k => tsTaggedUnion t k
  | .ocamlCtorNames, t, k => ocamlCtorNames t k
  | .ocamlTypeBlock, t, k => ocamlTypeBlock t k
  | .ocamlMatchArms, t, k => ocamlMatchArms t k
  | .tsLiterals, t, k => tsLiterals t k
  | .tsSwitchCases, t, k => tsSwitchCases t k
  | .unresolved reason, _, _ => throw reason

end Conform.Manifest
