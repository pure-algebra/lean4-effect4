import Lean
import OCaml5.Lcnf.Externs

/-!
# OCaml5.Lcnf.Prim

**What it is.** The primitive alphabet: one constructor per meaning that a Lean constant with no
mono body carries. The route's one primitive table (`OCaml5.Lcnf.Builtins`) names, in its runtime
column, the primitive the source evaluator gives each extern row; the evaluator itself
(`Conform.Lcnf.Semantics`, `Prim.apply`) imports this alphabet. A `PrimTable` is that column as
data.
-/

namespace OCaml5.Lcnf
open Lean

inductive Prim where
  | natAdd | natSub | natMul | natDiv | natMod | natPow
  | natShiftLeft | natShiftRight | natLand | natLor | natXor
  /-- `Nat.decEq`, `Nat.beq`: `Decidable (n = m)` is `Bool` at mono. -/
  | natDecEq
  | natDecLt | natDecLe
  | natSucc | natPred
  | boolNot | boolAnd | boolOr | boolDecEq
  | strAppend | strDecEq | strLength
  /-- `String.toUTF8 : String → ByteArray`, as the array of its UTF-8 bytes. -/
  | strToUTF8
  /-- A coercion that is the identity on this value domain: `ByteArray.data`,
  `UInt8.toNat`, `USize.toNat`, `UInt8.toUInt64`, … -/
  | identity
  /-- `UIntN.ofNat`: reduce mod `2 ^ bits`. -/
  | uintOfNat (bits : Nat)
  /-- `UIntN.sub`: subtraction mod `2 ^ bits`. It wraps below zero, where `Nat.sub` stops:
  `0 - 1` is `2 ^ bits - 1`. -/
  | uintSub (bits : Nat)
  | arrayToList | listToArray | arrayMkEmpty | arrayPush | arraySize
  /-- `Array.uget`/`get!`/`fget`: Lean's `get!` answers a default on an out-of-range index;
  this row is *stuck* there instead, because "the default of the element type" is not
  something the value domain can produce. A stuck row is a refusal a report can carry; a
  wrong answer is not. -/
  | arrayGet
  | listLength
  deriving DecidableEq, Repr, Inhabited

namespace Prim

/-- How many **relevant** (non-erased) arguments the row takes. -/
def arity : Prim → Nat
  | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natPow => 2
  | .natShiftLeft | .natShiftRight | .natLand | .natLor | .natXor => 2
  | .natDecEq | .natDecLt | .natDecLe => 2
  | .natSucc | .natPred => 1
  | .boolNot => 1
  | .boolAnd | .boolOr | .boolDecEq => 2
  | .strAppend | .strDecEq => 2
  | .strLength | .strToUTF8 => 1
  | .identity => 1
  | .uintOfNat _ => 1
  | .uintSub _ => 2
  | .arrayToList | .listToArray | .arrayMkEmpty | .arraySize | .listLength => 1
  | .arrayPush | .arrayGet => 2

protected def toString : Prim → String
  | .uintOfNat bits => s!"uintOfNat {bits}"
  | .uintSub bits => s!"uintSub {bits}"
  | p => (repr p).pretty.replace "OCaml5.Lcnf.Prim." ""

instance : ToString Prim := ⟨Prim.toString⟩

end Prim

/-- A primitive table: pure data. Lookup strips a `_redArg` suffix, as the compiler's own
`reduceArity` twins require and as `OCaml5.Lcnf.builtin?` does. -/
abbrev PrimTable := List (Name × Prim)

def PrimTable.lookup? (t : PrimTable) (n : Name) : Option Prim :=
  let n := stripRedArg n
  (List.find? (fun p => p.1 == n) t).map (·.2)

end OCaml5.Lcnf
