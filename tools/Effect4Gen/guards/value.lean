/-! Value-as-data acceptance: a value tree, a shape and a shape document each written as
content, read back exactly, and refused with a byte added or removed. A described value holds
no live handle even when the value it describes is one. -/
namespace ValueAcceptance
open Effect4 Effect4.Store

def values : List Val :=
  [.unit, .bool true, .nat 0, .nat 300, .str "", .str "a b", .bytes [0, 255], .list [],
   .list [.nat 1, .str "x"], .pair (.nat 1) .none, .none, .some (.some .unit),
   .ctor 0 [], .ctor 7 [.list [.ctor 1 [.nat 2]], .bool false],
   .ref 2 (List.replicate 32 9), .handle 1 4, .list [.handle 0 0, .pair (.handle 2 5) .unit]]

def shapes : List Shape :=
  [.unit, .bool, .nat, .string, .bytes, .digest, .list .nat, .option (.list .string),
   .pair .nat (.named "T"), .struct "S" [("a", .nat), ("b", .named "T")],
   .sum "T" [("leaf", []), ("node", [("left", .named "T"), ("right", .named "T")])],
   .ref .program, .anyRef, .named "T"]

def docs : List ShapeDoc :=
  [⟨.nat, []⟩, ⟨.named "T", [("T", .sum "T" [("leaf", []), ("node", [("next", .named "T")])])]⟩,
   Canonical.shape Val, Canonical.shape Shape, Canonical.shape ShapeDoc]

#guard values.all fun x => Canonical.decode (α := Val) (Canonical.encode x) = some x
#guard values.all fun x => Canonical.decode (α := Val) (Canonical.encode x ++ [0]) = none
#guard values.all fun x => Canonical.decode (α := Val) (Canonical.encode x).dropLast = none
#guard values.all fun x => (Canonical.shape Val).accepts (Canonical.toVal x)
#guard values.all fun x => (Canonical.toVal x).handles = []
-- `Shape` has no decidable equality, so a read is compared by what it writes again; the
-- writer is injective (`Canonical.encode_injective`), so this is the same round trip.
#guard shapes.all fun x =>
  (Canonical.decode (α := Shape) (Canonical.encode x)).map Canonical.encode = some (Canonical.encode x)
#guard shapes.all fun x => (Canonical.decode (α := Shape) (Canonical.encode x ++ [0])).isNone
#guard shapes.all fun x => (Canonical.shape Shape).accepts (Canonical.toVal x)
#guard docs.all fun x =>
  (Canonical.decode (α := ShapeDoc) (Canonical.encode x)).map Canonical.encode =
    some (Canonical.encode x)
#guard docs.all fun x => (Canonical.shape ShapeDoc).accepts (Canonical.toVal x)
-- The schema of schemas describes itself.
#guard (Canonical.shape ShapeDoc).accepts (Canonical.toVal (Canonical.shape ShapeDoc))
#guard Canonical.decode (α := Val) [] = none

end ValueAcceptance
