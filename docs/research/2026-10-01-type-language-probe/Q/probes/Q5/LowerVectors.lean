import ProbeQ5.Lower
/-! Seat Q, question 5: the vectors `Q/ocaml/lcnf/canon_check.ml` runs on the lowered code,
evaluated in Lean; the two outputs are compared line for line in `Q/logs/probes/Q5-agree.log`. -/
open ProbeQW ProbeQ5 Effect4.Store

def tyName : Ty → String
  | .nat => "nat" | .string => "string" | .int => "int" | _ => "?"
def vs : Val → String
  | .nat n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .list xs => "[" ++ ", ".intercalate (xs.attach.map fun ⟨x, _⟩ => vs x) ++ "]"
  | .ctor i xs => "ctor " ++ toString i ++ " [" ++ ", ".intercalate (xs.attach.map fun ⟨x, _⟩ => vs x) ++ "]"
  | _ => "?"
def b (x : Bool) : String := if x then "true" else "false"

def lines : List String :=
  let (ns, xs) := canonRecord ["é", "z", "a"] [.nat 1, .nat 2, .nat 3]
  let fs := canonFields [("b", .nat, false), ("a", .string, true), ("b", .int, true)]
  let s (a c : Ty) := b (Ty.sub a c)
  [ "canonRecord: " ++ ",".intercalate ns ++ " / " ++ ",".intercalate (xs.map vs)
  , "canonFields: " ++ ",".intercalate (fs.map fun (n, t, o) => n ++ ":" ++ tyName t ++ ":" ++ b o)
  , "canonRecordVal: " ++ (match canonRecordVal (.ctor 0 [.list [.str "y", .str "x"], .list [.nat 1, .nat 2]]) with
      | some v => vs v | none => "none")
  , "sub: " ++ " ".intercalate [
      s .nat .number, s .number .nat, s .undefined .unit, s .nat .bytes,
      s (.record [("a", .nat, false)]) (.record [("a", .int, false)]),
      s (.record [("a", .nat, false)]) (.record [("a", .int, true)]),
      s (.record [("b", .nat, false), ("a", .unit, false)]) (.record [("a", .unit, false), ("b", .number, false)]),
      s (.tuple [.nat]) (.tuple [.int]), s (.tuple [.nat]) (.tuple [.nat, .nat]),
      s (.map .nat .nat) (.map .int .nat), s (.map .nat .nat) (.map .nat .int),
      s (.app "Effect.Effect" [.nat, .string, .unit]) (.app "Effect.Effect" [.int, .string, .unit]),
      s (.app "Ref.Ref" [.nat]) (.app "Ref.Ref" [.int]),
      s (.app "Nominal.Unknown" [.nat]) (.app "Nominal.Unknown" [.int]),
      s (.app "Ref.Ref" [.nat]) (.app "Fiber.Fiber" [.nat])] ]

#eval IO.println ("\n".intercalate lines)
