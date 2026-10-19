import Lean
import OCaml5.Lcnf.Builtins

/-!
# OCaml5.Lcnf.Identity

**What it is.** The identity of a lowered node (Codex's R6.1): five parts, and two consumers share
a node only when all five agree.

| part | what it is | where it is read |
| --- | --- | --- |
| `lean` | the mono declaration the code is translated from; a specialisation is its own declaration (`f._at_.g.spec_N`) | the manifest's `lean` column |
| `code` | that declaration's code, `DeclHash`'s hash of the whole mono `Decl` | the manifest's `declHash` column |
| `profile` | the target profile: the carrier implementation the code is lowered against, `flat` or an extern table with its prelude | the manifest's identity line |
| `owner` | the type owner: the unit that declares the types the code names, beside the program types' owner every unit opens | the manifest's identity line |
| `catalogue` | the builtin catalogue (`OCaml5.Lcnf.Builtins`): each row's constant and its OCaml form, hashed | the manifest's identity line |

`OCaml5.Lcnf.Gen` writes one unit per recipe artifact by one walk of all its consumers' roots
(`Export`'s consumers, the walk's phases), so the consumers of one unit share every node they
reach, and its five parts agree by construction. It writes the unit's three shared parts as the
first line of the unit's closure manifest (`identityLine`). `compareUnits` reads two manifests and
says, for each declaration both hold, whether the two rows are one node and otherwise which part
differs first: what a merge of the two units would have to change. `lake exe lcnfgen --identity`
prints that comparison.

**Depends on.** `Lean.Name`, `OCaml5.Lcnf.Builtins` (the catalogue).

**Properties.**
* **Identity is all five parts.** `NodeKey.mismatch?` is `none` exactly when the five parts agree,
  and otherwise names the first part that differs, in the order of the table — *tested*.
* **A different carrier implementation is never one node** (R6.1's red control): two rows with one
  name and one code, lowered flat and over the engine's carriers, differ in `profile` — *tested*.
* **The identity line reads back.** `parseManifest` reads what `identityLine` and the manifest's
  columns write, and refuses a manifest without the line or the two columns — *tested*.
* **No proof obligation.** This is a finite check of manifests (decisions row 391), not a theorem
  about the lowering.
-/

namespace OCaml5.Lcnf.Identity

open Lean

/-- The five parts of a lowered node's identity. -/
structure NodeKey where
  lean : Name
  code : UInt64
  profile : String
  owner : String
  catalogue : UInt64
deriving BEq, Repr, Inhabited

/-- A part of the identity, in the order `mismatch?` reads them. -/
inductive Part where
  | lean | code | profile | owner | catalogue
deriving DecidableEq, Repr, Inhabited

/-- The part's name in a report. -/
def Part.name : Part → String
  | .lean => "declaration"
  | .code => "code"
  | .profile => "profile"
  | .owner => "type owner"
  | .catalogue => "catalogue"

/-- The first part in which two keys differ, or `none` when they are one node. -/
def NodeKey.mismatch? (a b : NodeKey) : Option Part :=
  if a.lean != b.lean then some .lean
  else if a.code != b.code then some .code
  else if a.profile != b.profile then some .profile
  else if a.owner != b.owner then some .owner
  else if a.catalogue != b.catalogue then some .catalogue
  else none

/-- The builtin catalogue's hash: each row's constant with its form's spelling, in table order. -/
def catalogue : UInt64 := hash (builtins.map fun b => (b.lean, b.form.spelling))

/-- The target profile of a run: `flat`, or the extern table and the prelude it lowers against. -/
def profileOf (externs prelude : Option String) : String :=
  match externs, prelude with
  | none, none => "flat"
  | e, p => "externs " ++ e.getD "-" ++ " prelude " ++ p.getD "-"

/-- What every node of one unit shares: the unit (the type owner), the profile and the catalogue. -/
structure UnitKey where
  unit : String
  profile : String
  catalogue : UInt64
deriving BEq, Repr, Inhabited

/-- One row of a closure manifest, as identity reads it: the declaration and its code. -/
structure Row where
  lean : Name
  code : UInt64
deriving BEq, Repr, Inhabited

/-- A row's whole key in its unit. -/
def UnitKey.key (u : UnitKey) (r : Row) : NodeKey :=
  { lean := r.lean, code := r.code, profile := u.profile, owner := u.unit, catalogue := u.catalogue }

/-- The first line of a closure manifest: the unit's shared parts. -/
def identityLine (u : UnitKey) : String :=
  s!"# identity: unit {u.unit}; profile {u.profile}; catalogue {u.catalogue}"

/-- The unit key an identity line states. -/
def parseIdentity (line : String) : Except String UnitKey := do
  let some rest := line.dropPrefix? "# identity: "
    | throw s!"no identity line: {line}"
  let parts := rest.toString.splitOn "; "
  let field (k : String) : Except String String :=
    match parts.findSome? (fun p => (p.dropPrefix? (k ++ " ")).map (·.toString)) with
    | some v => pure v
    | none => throw s!"the identity line names no {k}: {line}"
  let unit ← field "unit"
  let profile ← field "profile"
  let some catalogue := (← field "catalogue").toNat?
    | throw s!"the identity line's catalogue is no number: {line}"
  return { unit := unit, profile := profile, catalogue := catalogue.toUInt64 }

/-- A closure manifest's unit key and rows: the identity line, then the column header, then one
row per declaration. Only the `lean` and `declHash` columns are read. -/
def parseManifest (text : String) : Except String (UnitKey × List Row) := do
  let lines := (text.splitOn "\n").filter (!·.isEmpty)
  let (first, header, body) ← match lines with
    | first :: header :: body => pure (first, header, body)
    | _ => throw "a closure manifest holds an identity line and a column header"
  let u ← parseIdentity first
  let columns := header.splitOn "\t"
  let some leanAt := columns.idxOf? "lean"
    | throw "the manifest has no `lean` column"
  let some codeAt := columns.idxOf? "declHash"
    | throw "the manifest has no `declHash` column"
  let rows ← body.mapM fun line => do
    let cells := line.splitOn "\t"
    let some lean := cells[leanAt]? | throw s!"a row without its `lean` cell: {line}"
    let some code := cells[codeAt]?.bind (·.toNat?) | throw s!"a row without a numeric `declHash`: {line}"
    pure { lean := lean.toName, code := code.toUInt64 : Row }
  return (u, rows)

/-- Two units compared: the declarations both hold, how many of them are one node, and how many
differ by each part (the first part that differs). -/
structure Comparison where
  first : String
  second : String
  common : Nat
  shared : Nat
  differ : List (Part × Nat)
deriving Repr, Inhabited

/-- Compare two units' rows by declaration. -/
def compareUnits (a : UnitKey × List Row) (b : UnitKey × List Row) : Comparison := Id.run do
  let index : Std.HashMap Name Row := b.2.foldl (fun m r => m.insert r.lean r) {}
  let mut common := 0
  let mut shared := 0
  let mut differ : List (Part × Nat) := []
  for r in a.2 do
    let some s := index[r.lean]? | continue
    common := common + 1
    match (a.1.key r).mismatch? (b.1.key s) with
    | none => shared := shared + 1
    | some p =>
      differ := match differ.lookup p with
        | some n => differ.map fun (q, k) => if q == p then (q, n + 1) else (q, k)
        | none => differ ++ [(p, 1)]
  return { first := a.1.unit, second := b.1.unit, common, shared, differ }

/-- The comparison as one line of the generator's report. -/
def Comparison.line (c : Comparison) : String :=
  let parts := c.differ.map fun (p, n) => s!"{n} differ in {p.name}"
  s!"{c.first} and {c.second}: {c.common} in both, {c.shared} of them one node" ++
    (if parts.isEmpty then "" else "; " ++ ", ".intercalate parts)

/-! ## Controls -/

private def flatUnit : UnitKey := { unit := "Api_gen", profile := "flat", catalogue := 7 }
private def engineUnit : UnitKey :=
  { unit := "Api_engine", profile := profileOf (some "externs.txt") (some "prelude.ml"), catalogue := 7 }
private def run : Row := { lean := `Effect4.Api.run, code := 42 }

-- one node: every part agrees
#guard (flatUnit.key run).mismatch? (flatUnit.key run) == none
-- R6.1's red control: one name and one code, lowered over two carrier implementations, are two
-- nodes, and the profile is the part that says so
#guard (flatUnit.key run).mismatch? (engineUnit.key run) == some .profile
-- the order of the parts: a different code is reported before a different profile; the type
-- owner and the catalogue each decide alone
#guard (flatUnit.key run).mismatch? (engineUnit.key { run with code := 43 }) == some .code
#guard (flatUnit.key run).mismatch? ({ flatUnit with unit := "Lanes_gen" }.key run) == some .owner
#guard (flatUnit.key run).mismatch? ({ flatUnit with catalogue := 8 }.key run) == some .catalogue
#guard (flatUnit.key run).mismatch? (flatUnit.key { run with lean := `Effect4.Api.replay }) == some .lean

-- the identity line and the two columns read back; a manifest without the line is refused
private def manifest (u : UnitKey) (rows : List Row) : String :=
  "\n".intercalate ([identityLine u, "lean\tocaml\tdeclHash"]
    ++ rows.map fun r => s!"{r.lean}\tx\t{r.code}") ++ "\n"
#guard match parseManifest (manifest engineUnit [run]) with
  | .ok (u, rows) => u == engineUnit && rows == [run]
  | .error _ => false
#guard match parseManifest "lean\tocaml\tdeclHash\nA.b\tx\t1\n" with
  | .error _ => true
  | .ok _ => false

-- a comparison counts the declarations both units hold, and sorts the rest by the first part
-- that differs
#guard
  let c := compareUnits (flatUnit, [run, { lean := `A.only, code := 1 }])
    (engineUnit, [run, { lean := `B.only, code := 2 }])
  c.common == 1 && c.shared == 0 && c.differ == [(.profile, 1)]
#guard
  let c := compareUnits (flatUnit, [run]) (flatUnit, [run])
  c.common == 1 && c.shared == 1 && c.differ.isEmpty

end OCaml5.Lcnf.Identity
