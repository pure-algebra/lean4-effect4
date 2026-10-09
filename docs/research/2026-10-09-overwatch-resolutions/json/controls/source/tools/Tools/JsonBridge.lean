import Lean.Data.Json
import Effect4.Store.Domain.ShapeRead

/-!
# Tools.JsonBridge — Lean's JSON and the tree's JSON, both ways

A tool reads its requests with Lean's JSON parser (`Lean.Json.parse`) and writes its answers as
`Lean.Json`. The tree's JSON (`Effect4.Json`) is what the canonical carriers print and read
(`Canonical.print`, `Canonical.ofJsonAnyOrder`, `src/Effect4/Store/Domain/ShapeRead.lean`). This
module moves a value between the two.

- **Lean's to the tree's** (`ofLeanJson`): an object's entries in Lean's order, sorted by key,
  which the shape's order puts right (`ShapeDoc.order`); a number only where it is a natural that
  binary64 holds exactly, as the binary64 the canonical print writes. A natural that binary64
  rounds is refused, not changed (`ofLeanJson_num`; Codex's JSON-01). Anything else is none.
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
number is a binary64 datum from which the reader takes back that number's natural
(`natOfBinary64`, the step `readIn` takes at `.nat`). A step of `json-read-exact` at the tool:
with `Canonical.ofJson_exact`, the program a request admits holds the naturals the request wrote.
Its consumer is `Tools.Session.programFrom?`, whose answers name it. -/
theorem ofLeanJson_num {fuel : Nat} {n : Lean.JsonNumber} {j : Effect4.Json}
    (h : ofLeanJson (fuel + 1) (.num n) = some j) :
    ∃ x : Effect4.Float64, j = .number x ∧ n.exponent = 0 ∧ 0 ≤ n.mantissa ∧
      natOfBinary64 x.bits = some n.mantissa.toNat := by
  unfold ofLeanJson at h
  split at h
  · rename_i hn
    cases h
    exact ⟨_, rfl, hn.1, hn.2.1, hn.2.2⟩
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

end Tools.JsonBridge
