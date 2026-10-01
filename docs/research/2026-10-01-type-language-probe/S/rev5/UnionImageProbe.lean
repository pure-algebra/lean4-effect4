import Effect4.Store.Carrier.Val

open Effect4 Effect4.Store

namespace UnionProbe

inductive MiniTy where
  | record (fields : List (String × MiniTy))
  | nat
  | union (left right : MiniTy)

/-- Encode a value at a type into a simplified JSON-like representation. -/
def encodeMini : MiniTy → Val → Option (List (String × Val))
  | .record fields, .ctor 0 vs => do
      if fields.length != vs.length then none
      let entries ← (fields.zip vs).mapM fun ((name, ty), v) => do
        match ty, v with
        | .nat, .nat n => some (name, .nat n)
        | _, _ => none
      some entries
  | .union left right, v =>
      -- Union encoder prefers left branch if it matches
      match encodeMini left v with
      | some res => some res
      | none => encodeMini right v
  | _, _ => none

/-- Candidate type: union {a: nat} {b: nat} -/
def branchA : MiniTy := .record [("a", .nat)]
def branchB : MiniTy := .record [("b", .nat)]
def unionAB : MiniTy := .union branchA branchB

/-- Positional value decoded from JSON {"b": 42}: `ctor 0 [nat 42]` -/
def vDecoded : Val := .ctor 0 [.nat 42]

-- Branch-local re-encoding passes for branchB!
#guard encodeMini branchB vDecoded == some [("b", .nat 42)]

-- BUT whole-union re-encoding selects branchA because vDecoded fits branchA!
#guard encodeMini unionAB vDecoded == some [("a", .nat 42)]

/-- Therefore, the round-trip check MUST check `encodeMini unionAB v == input`.
If input was [("b", .nat 42)], checking whole-union correctly rejects this ambiguous representation! -/
def checkExactRoundTrip (ty : MiniTy) (input : List (String × Val)) (v : Val) : Bool :=
  match encodeMini ty v with
  | some out => out == input
  | none => false

-- Branch-local check would falsely accept:
#guard (encodeMini branchB vDecoded == some [("b", .nat 42)]) == true

-- Whole-union check correctly rejects:
#guard checkExactRoundTrip unionAB [("b", .nat 42)] vDecoded == false

end UnionProbe
