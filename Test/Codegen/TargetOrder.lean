import Lean.Elab.Command
import Effect4.Laws.Codegen.TargetOrder

/-!
# Test.Codegen.TargetOrder

The model of tsgo's assignability (`Effect4.Laws.Codegen.TargetOrder`) against tsgo's recorded
verdicts, and `E4-PRINT-CE-001` in the model's terms.

- **The finite check.** `generated/assignability.tsv` holds tsgo 7.0.0-dev.20260629.1's verdict on
  each pair's two directions. `parseLegacy` reads each recorded spelling, and the model must give
  tsgo's verdict on every pair it reads.
- **The counterexample.** The printed value of `E4-PRINT-CE-001` has the type tsgo infers,
  `readonly [number | string, boolean]`, and its annotation is the union of pairs. The model refuses
  the first at the second, while `Ty.sub` relates their program types.
- **The controls.** At a literal position the decomposition relates the two forms, and it stops
  past 25 combinations.
-/

namespace Test.Codegen.TargetOrder

open TypeScript Effect4 Effect4.Program Effect4.Codegen.TargetOrder

/-! ## The finite check against tsgo's verdicts -/

open Lean Elab Command in
run_cmd do
  let text ← IO.FS.readFile "generated/assignability.tsv"
  -- `parseLegacy` reads no object type, so the recorded object spellings,
  -- `{ readonly a: A; readonly b?: B }`, are read here, their field types by `parseLegacy`.
  let readObject? : String → Option TypeRef := fun text => do
    let t := text.trimAscii.toString
    guard (t.startsWith "{" && t.endsWith "}")
    let inner := ((t.drop 1).dropEnd 1).trimAscii.toString
    if inner.isEmpty then return .object []
    let fields ← (inner.splitOn "; ").mapM fun field => do
      let readonly := field.startsWith "readonly "
      let body := if readonly then (field.drop 9).toString else field
      match body.splitOn ": " with
      | [lhs, rhs] =>
        let optional := lhs.endsWith "?"
        let name := if optional then (lhs.dropEnd 1).toString else lhs
        let type ← Codegen.Types.parseLegacy rhs
        pure ({ name, readonly, optional, type } : TypeRef.Field)
      | _ => none
    return .object fields
  let read : String → Option TypeRef := fun text =>
    (Codegen.Types.parseLegacy text).orElse fun _ => readObject? text
  let mut checked := 0
  let mut unread := 0
  let mut wrong : Array String := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "#" || line.isEmpty then continue
    let cols := (line.splitOn "\t").toArray
    if cols.size < 7 then continue
    match read cols[1]!, read cols[2]! with
    | some l, some r =>
      checked := checked + 1
      let lr := cols[5]! == "true"
      let rl := cols[6]! == "true"
      if assignable l r != lr || assignable r l != rl then
        wrong := wrong.push s!"{cols[0]!}: model {assignable l r}/{assignable r l}, tsgo {lr}/{rl}"
    | _, _ => unread := unread + 1
  unless wrong.isEmpty do
    throwError m!"the model disagrees with tsgo on {wrong.size} pairs: {wrong.toList.take 12}"
  unless unread == 0 && checked > 0 do
    throwError m!"{unread} recorded spellings do not parse; {checked} pairs checked"

/-! ## `E4-PRINT-CE-001` in the model's terms -/

def number : TypeRef := keyword "number"
def string : TypeRef := keyword "string"
def boolean : TypeRef := keyword "boolean"

/-- The type tsgo infers for the printed pair: a pair of a union. -/
def inferred : TypeRef := .tuple [.union [number, string], boolean] true

/-- The printed annotation: the normal form, a union of pairs. -/
def annotation : TypeRef :=
  .union [.tuple [number, boolean] true, .tuple [string, boolean] true]

-- The annotation is what the printer writes for the checker's answer type.
#guard Codegen.Types.ofTy (.prod (.union .nat .string) .bool) = some annotation

-- The attack: `Ty.sub` relates the pair of a union to the union of pairs, and the model refuses.
#guard Ty.sub (Ty.prod (.union .nat .string) .bool).normalize
  (Ty.union (.prod .nat .bool) (.prod .string .bool)).normalize
#guard assignable inferred annotation = false

-- The other direction holds in both orders.
#guard assignable annotation inferred

/-! ## Controls: a literal position decomposes, up to 25 combinations -/

def lit (s : String) : TypeRef := .literal s

-- At a literal position the pair of a union relates to the union of pairs.
#guard assignable (.tuple [.union [lit "a", lit "b"], boolean] true)
  (.union [.tuple [lit "a", boolean] true, .tuple [lit "b", boolean] true])

/-- The first `k` letters as string literal types. -/
def letters (k : Nat) : List TypeRef := (List.range k).map fun i => lit (toString (Char.ofNat (97 + i)))

/-- Every list of `w` more letters among the first three, prefixed to each list of `acc`. -/
def allTuples : Nat → List (List TypeRef) → List (List TypeRef)
  | 0, acc => acc
  | w + 1, acc => allTuples w (acc.flatMap fun t => (letters 3).map fun l => l :: t)

/-- Three positions of three literals: 27 combinations. -/
def wide : TypeRef := .tuple (List.replicate 3 (.union (letters 3))) true
def wideTarget : TypeRef := .union ((allTuples 3 [[]]).map fun items => .tuple items true)

-- Past 25 combinations the decomposition refuses, though every combination has its member.
#guard assignable wide wideTarget = false

/-- Two positions of five literals: 25 combinations. -/
def five : List TypeRef := (List.range 5).map fun i => lit (toString (Char.ofNat (97 + i)))
def narrow : TypeRef := .tuple [.union five, .union five] true
def narrowTarget : TypeRef :=
  .union (five.flatMap fun a => five.map fun b => .tuple [a, b] true)

-- At 25 combinations it relates.
#guard assignable narrow narrowTarget

end Test.Codegen.TargetOrder
