import Lean.Data.Json

/-!
# Conform.Core.Policy — strict readers for the configuration a check is driven by

**What it is.** The helpers a check uses to read its policy and configuration files (JSON): an
object whose keys are all known, a field that is present and of the expected shape, a list of
strings, a name. Every check in `Conform` is generic in what it audits, so the *specific*
families, roots, covers and manifests reach it through files read here, and the readers refuse
anything they do not understand rather than defaulting it.

**Depends on.** `Lean.Json`. Nothing from this repository.

**Properties.**
* **Unknown keys are refusals.** `Policy.object` is given the complete key list and fails on any
  other key, naming it, so a misspelled `cover` cannot silently become "no cover" —
  *by construction*.
* **Missing is not empty.** A field the schema requires and the file lacks is a refusal
  (`Policy.field`); a field the schema makes optional is read by `Policy.field?` and its
  absence is `none`, never `[]` — *by construction*.
* **Errors carry the path.** Every failure message begins with the JSON path from the root
  (`families[3].cover`), so the file can be fixed without reading the check's source —
  *by construction*.
-/

namespace Conform.Policy

open Lean (Json)

/-- A reader over one JSON value at a named path. -/
abbrev Reader := ReaderT String (Except String)

def fail {α} (msg : String) : Reader α := fun path => .error s!"{path}: {msg}"

def path : Reader String := fun p => .ok p

def at_ {α} (segment : String) (r : Reader α) : Reader α := fun p =>
  r (if p.isEmpty then segment else p ++ "." ++ segment)

def index {α} (i : Nat) (r : Reader α) : Reader α := fun p => r s!"{p}[{i}]"

/-- Run a reader at the root. -/
def run {α} (r : Reader α) (rootName : String := "$") : Except String α := r rootName

/-- Read a JSON file and run a reader on it. -/
def load {α} (file : System.FilePath) (r : Json → Reader α) : IO α := do
  let text ← IO.FS.readFile file
  let json ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{file}: not JSON: {e}")
  match run (r json) file.toString with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- An object with exactly the listed keys admitted; unknown keys are refusals. Returns a
lookup that itself refuses a key outside the list (a programming error, reported as one). -/
def object (json : Json) (known : List String) : Reader (String → Option Json) := do
  match json.getObj? with
  | .ok kvs =>
    for k in kvs.keys do
      unless known.contains k do
        fail s!"unknown key `{k}` (known: {", ".intercalate known})"
    pure fun k => if known.contains k then kvs.get? k else none
  | .error _ => fail "expected an object"

/-- The library's accessor, with this module's error message and path in place of its own. -/
private def lift {α} (r : Except String α) (expected : String) : Reader α :=
  match r with
  | .ok a => pure a
  | .error _ => fail s!"expected {expected}"

def string (json : Json) : Reader String := lift json.getStr? "a string"

def bool (json : Json) : Reader Bool := lift json.getBool? "a boolean"

/-- `Json.getNat?` admits exactly the non-negative integers written without an exponent. -/
def nat (json : Json) : Reader Nat := lift json.getNat? "a natural number"

def array {α} (json : Json) (item : Json → Reader α) : Reader (Array α) := do
  let xs ← lift json.getArr? "an array"
  xs.mapIdxM fun i x => index i (item x)

def strings (json : Json) : Reader (Array String) := array json string

/-- A required field. -/
def field {α} (get : String → Option Json) (name : String) (r : Json → Reader α) : Reader α :=
  match get name with
  | some j => at_ name (r j)
  | none => fail s!"missing required key `{name}`"

/-- An optional field: absent is `none`, never a default value. -/
def field? {α} (get : String → Option Json) (name : String) (r : Json → Reader α) :
    Reader (Option α) :=
  match get name with
  | some j => at_ name (some <$> r j)
  | none => pure none

/-- One of a finite set of spellings, else a refusal that lists them. -/
def enum {α} (json : Json) (table : List (String × α)) : Reader α := do
  let s ← string json
  match table.lookup s with
  | some a => pure a
  | none => fail s!"`{s}` is not one of {", ".intercalate (table.map (·.1))}"

/-- A dotted Lean name. -/
def name (json : Json) : Reader Lean.Name := do
  let s ← string json
  if s.isEmpty then fail "empty name" else pure s.toName

end Conform.Policy
