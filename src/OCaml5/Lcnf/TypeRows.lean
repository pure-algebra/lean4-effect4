import Lean
import OCaml5.Ml.Syntax

/-!
# OCaml5.Lcnf.TypeRows

**What it is.** The table of the Lean type constants that the LCNF route spells natively, one
row per constant, as `OCaml5.Lcnf.builtins` is for values. A row is data: the constant, the
number of Lean arguments it takes, its OCaml spelling over the converted arguments, and its
contract. The lookup (`builtinTy?`, `isBuiltinType`), the names (`builtinTypeNames`), the
reserved type names (`reservedTypeNames`) and the fidelity inventory
(`Conform.Effect4.Lcnf.typeFidelityTable`) are computed from the rows. The module also owns the
contract's class (`Fidelity`), which the value table shares.

**Depends on.** `OCaml5.Ml.Syntax` (a spelling is an OCaml type) and `Lean.Name`.

**Properties.**
* **One owner.** A type constant has a row here, or the route declares it from its Lean
  declaration (`OCaml5.Lcnf.Types`). No second list names a row: *by construction*.
* **A spelling is data.** An OCaml type constructor over the converted arguments by position,
  or a tuple of them. Every position is an argument of the row, used once: *checked*
  (`typeRowProblems`, the `#guard`s at the foot).
* **Every row has a contract.** `fidelity`, `domain` and `note` have no default. The class is a
  reading of the row against the Lean type's representation. No theorem proves a row. An
  exact row states no domain, and a row exact under a domain states its domain: *checked*.
* **A row's name is taken.** The unqualified OCaml names the rows spell are reserved, so a Lean
  type of the same short name is renamed (`OCaml5.Lcnf.typeName`) rather than shadowing the one
  a row means: *by construction*.
* **`Char` is its code point.** Lean's compiler represents a `Char` as its `UInt32` value. The
  row spells it `int`, which holds every Unicode scalar value.

**What it does not own.** The value rows (`OCaml5.Lcnf.builtins`), the extern seam's carrier
rows (`OCaml5.Lcnf.Externs`), and the declarations the route emits for every other type
(`OCaml5.Lcnf.Types`).
-/

namespace OCaml5.Lcnf

open Lean

/-! ## 1. The contract of a row -/

/-- How faithfully an OCaml form or an OCaml type reproduces the Lean constant it stands for.
The class is a claim about the row, read against the Lean definition. -/
inductive Fidelity
  /-- The OCaml form denotes the same function on the whole Lean domain. -/
  | exact
  /-- The OCaml form denotes the same function on a stated sub-domain, and something else
  outside it. The domain is the row's `domain` field. -/
  | domain
  /-- The OCaml form denotes a different function that agrees on the values this tree
  produces, or differs in a way the row states. -/
  | approximate
  /-- The OCaml form denotes a different function and the difference can be reached. -/
  | unsound
  deriving DecidableEq, Repr, Inhabited

namespace Fidelity
protected def toString : Fidelity → String
  | .exact => "exact"
  | .domain => "exact-under-domain"
  | .approximate => "approximate"
  | .unsound => "unsound"
instance : ToString Fidelity := ⟨Fidelity.toString⟩

/-- What is wrong with a class and its stated domain: an exact row states no domain, and a row
exact under a domain states one. Every table of the route checks its rows with it. -/
def problems (fidelity : Fidelity) (domain : String) : List String :=
  match fidelity with
  | .exact => if domain.isEmpty then [] else ["an exact row states a domain"]
  | .domain => if domain.isEmpty then ["a row exact under a domain states none"] else []
  | _ => []
end Fidelity

/-! ## 2. The type rows -/

/-- The OCaml spelling of a type row over the Lean type's converted arguments, by position. -/
inductive TySpelling where
  /-- A type constructor, postfix as OCaml writes it: `con "result" [1, 0]` on `[ε, α]` is
  `(α, ε) result`. -/
  | con (name : String) (args : List Nat)
  /-- A tuple: `tuple [0, 1]` on `[α, β]` is `α * β`. -/
  | tuple (args : List Nat)
  deriving Inhabited

namespace TySpelling

/-- The argument positions the spelling reads. -/
def positions : TySpelling → List Nat
  | .con _ args => args
  | .tuple args => args

/-- The spelling applied to converted arguments. A position past the arguments reads `_`; the
table's check refuses a row that holds one. -/
def apply (s : TySpelling) (args : List Ml.Ty) : Ml.Ty :=
  let at_ (i : Nat) : Ml.Ty := args[i]?.getD .anon
  match s with
  | .con name ps => .con name (ps.map at_)
  | .tuple ps => .tuple (ps.map at_)

/-- The spelling's head, as a report writes it: the type constructor, or `*` for a tuple. -/
def head : TySpelling → String
  | .con name _ => name
  | .tuple _ => "*"

end TySpelling

/-- One row of the type table. No field of the contract has a default. -/
structure TypeRow where
  /-- The Lean type constant. -/
  lean : Name
  /-- The number of Lean arguments the row spells: the type's OCaml parameters
  (`OCaml5.Lcnf.typeParameterIndices`). -/
  arity : Nat
  spelling : TySpelling
  fidelity : Fidelity
  /-- The domain on which the row is exact (`""` when the class is `exact`). -/
  domain : String
  /-- Why: the difference, or the argument that there is none. -/
  note : String
  deriving Inhabited

private def typeRow (lean : Name) (arity : Nat) (spelling : TySpelling) (fidelity : Fidelity)
    (domain note : String) : TypeRow :=
  { lean, arity, spelling, fidelity, domain, note }

private def int : TySpelling := .con "int" []

/-- The Lean type constants with a native OCaml spelling, one row per constant. -/
def typeRows : List TypeRow := [
  typeRow ``Nat 0 int .domain "n < 2^62"
    "OCaml `int` is 63-bit, Lean `Nat` unbounded.",
  typeRow ``Int 0 int .domain "-2^62 ≤ n < 2^62"
    "and `Int` and `Nat` share one OCaml type, so an emitter cannot tell them apart in an annotation.",
  typeRow ``UInt8 0 int .exact ""
    "the range 0..255 is inside `int`.",
  typeRow ``UInt16 0 int .exact "" "",
  typeRow ``UInt32 0 int .exact "" "",
  typeRow ``UInt64 0 int .unsound "n < 2^62"
    "**the hole.** `UInt64` values reach 2^64 - 1; OCaml's `int` holds 2^62 - 1. The wire's big-endian 64-bit fields and `Effect4.Store.Val.wf`'s `… < 2 ^ 64` live in this type. Nothing in the route detects the overflow: it wraps.",
  typeRow ``USize 0 int .unsound "n < 2^62"
    "as `UInt64` — and `USize` is the shim's index type, so it is also the type every `Array` index is spelled in.",
  typeRow ``Bool 0 (.con "bool" []) .exact "" "",
  typeRow ``String 0 (.con "string" []) .approximate "the string is ASCII"
    "Lean's `String` is a sequence of Unicode scalar values; OCaml's is a byte sequence. Equality and concatenation agree; `length`, indexing and any `Char` operation do not.",
  typeRow ``Unit 0 (.con "unit" []) .exact "" "",
  typeRow ``PUnit 0 (.con "unit" []) .exact "" "",
  typeRow ``Char 0 int .exact ""
    "Lean's compiler represents a `Char` as its `UInt32` code point, and OCaml's `int` holds every Unicode scalar value, so the row is the code point itself. Its operations have no value row, so a `Char` in code is a hole.",
  typeRow ``Float 0 (.con "float" []) .exact ""
    "both are IEEE 754 binary64. No `Float` operation has a `builtin?` row, so any arithmetic is a hole.",
  typeRow ``List 1 (.con "list" [0]) .exact "" "",
  typeRow ``Array 1 (.con "list" [0]) .approximate ""
    "the shim: denotationally a sequence, operationally a different cost model (see `Array.push`, `Array.uget`).",
  typeRow ``Option 1 (.con "option" [0]) .exact "" "",
  typeRow ``Prod 2 (.tuple [0, 1]) .exact "" "",
  typeRow ``Except 2 (.con "result" [1, 0]) .exact ""
    "`Except ε α` is `(α, ε) result`, arguments swapped.",
  -- The exact clock: `Effect4.ClockMillis` is `E4_clock.t`, a Zarith integer (`ocaml/clock/`).
  typeRow `Effect4.ClockMillis 0 (.con "E4_clock.t" []) .exact ""
    "`E4_clock.t` is a Zarith integer, which holds every natural. The clock's operations are value rows (`Effect4.ClockMillis.*` in `OCaml5.Lcnf.builtins`), and its two constructors are `OCaml5.Lcnf.Clock.constructor?`."
]

/-! ## 3. What the table computes -/

/-- The table by constant. -/
def typeRowIndex : Std.HashMap Name TypeRow :=
  typeRows.foldl (fun m r => m.insert r.lean r) {}

/-- The type constants the table spells. -/
def builtinTypeNames : List Name := typeRows.map (·.lean)

/-- Whether a type constant has a row. -/
def isBuiltinType (n : Name) : Bool := typeRowIndex.contains n

/-- A type constant with a row, applied to already-converted arguments: its spelling, or `none`
when it has no row or the argument count is not the row's. -/
def builtinTy? (n : Name) (args : List Ml.Ty) : Option Ml.Ty :=
  match typeRowIndex[n]? with
  | some r => if args.length == r.arity then some (r.spelling.apply args) else none
  | none => none

/-- The unqualified OCaml type names the rows spell. A Lean type of one of these names would
shadow the one a row means, so `OCaml5.Lcnf.typeName` reserves them. -/
def reservedTypeNames : List String :=
  (typeRows.filterMap fun r =>
    match r.spelling with
    | .con name _ => if name.contains '.' then none else some name
    | .tuple _ => none).eraseDups

/-! ## 4. The table's own check -/

/-- Everything wrong with a type table: a key with two rows, a position outside the row's
arguments or read twice, a type name outside OCaml's lexical class, and a contract whose domain
disagrees with its class. Empty for this module's table, and it refuses each altered copy
below. -/
def typeRowProblems (rows : List TypeRow) : List String := Id.run do
  let mut out : List String := []
  let keys := rows.map (·.lean)
  for n in (keys.filter fun k => (keys.filter (· == k)).length > 1).eraseDups do
    out := out ++ [s!"type row {n}: the key has two rows"]
  for r in rows do
    let ps := r.spelling.positions
    for p in ps.eraseDups do
      unless p < r.arity do
        out := out ++ [s!"type row {r.lean}: position {p} is not an argument"]
      if (ps.filter (· == p)).length > 1 then
        out := out ++ [s!"type row {r.lean}: position {p} is read twice"]
    match r.spelling with
    | .con name _ =>
      unless Ml.isTypePath name do
        out := out ++ [s!"type row {r.lean}: `{name}` is not an OCaml type name"]
    | .tuple ps =>
      if ps.length < 2 then
        out := out ++ [s!"type row {r.lean}: a tuple of fewer than two parts"]
    for p in Fidelity.problems r.fidelity r.domain do
      out := out ++ [s!"type row {r.lean}: {p}"]
  return out

#guard (typeRowProblems typeRows).isEmpty
#guard typeRows.length == 19
#guard reservedTypeNames == ["int", "bool", "string", "unit", "float", "list", "option", "result"]

/-! ### Controls: each altered copy is refused, for its own reason -/

private def refuses (ps : List String) (reason : String) : Bool :=
  ps.any fun p => (p.splitOn reason).length > 1

-- two rows for one key
#guard refuses (typeRowProblems (typeRows ++ typeRows.take 1)) "type row Nat: the key has two rows"
-- a position past the arguments, and one read twice
#guard refuses (typeRowProblems [typeRow ``List 1 (.con "list" [1]) .exact "" ""])
  "type row List: position 1 is not an argument"
#guard refuses (typeRowProblems [typeRow ``Prod 2 (.tuple [0, 0]) .exact "" ""])
  "type row Prod: position 0 is read twice"
-- a name outside the type names, and a contract whose domain disagrees with its class
#guard refuses (typeRowProblems [typeRow ``Bool 0 (.con "Bool" []) .exact "" ""])
  "type row Bool: `Bool` is not an OCaml type name"
#guard refuses (typeRowProblems [typeRow ``Nat 0 int .exact "n < 2^62" ""])
  "type row Nat: an exact row states a domain"
#guard refuses (typeRowProblems [typeRow ``Nat 0 int .domain "" ""])
  "type row Nat: a row exact under a domain states none"

/-! ### Controls: the spellings the route had -/

#guard builtinTy? ``Except [.var "e", .var "a"] == some (.con "result" [.var "a", .var "e"])
#guard builtinTy? ``Prod [Ml.Ty.int, Ml.Ty.bool] == some (.tuple [Ml.Ty.int, Ml.Ty.bool])
#guard builtinTy? ``Array [Ml.Ty.int] == some (Ml.Ty.list Ml.Ty.int)
#guard builtinTy? ``Char [] == some Ml.Ty.int
#guard builtinTy? `Effect4.ClockMillis [] == some (.con "E4_clock.t" [])
-- an argument count that is not the row's has no spelling
#guard (builtinTy? ``List []).isNone && (builtinTy? ``Nat [Ml.Ty.int]).isNone
#guard (builtinTy? `Effect4.Machine.RunFiber []).isNone

end OCaml5.Lcnf
