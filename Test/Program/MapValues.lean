import Effect4.Machine.Term

/-! Finite controls for the string-map value operations of decisions rows 125, 166 and 197.
These checks distinguish the stored map pair from an ordinary program pair. -/

namespace Test.Program.MapValues

open Effect4 Effect4.Program
open Store

def empty : Val := .list []
def two : Val := .list [.pair (.str "b") (.nat 2), .pair (.str "d") (.nat 4)]

#guard NativeAtom.eval .mapEmpty [] = some empty
#guard NativeAtom.eval .mapEmpty [.unit] = none
#guard NativeAtom.eval .mapGet [empty, .str "missing"] = some .none
#guard NativeAtom.eval .mapSet [two, .str "a", .nat 1] =
  some (.list [.pair (.str "a") (.nat 1), .pair (.str "b") (.nat 2), .pair (.str "d") (.nat 4)])
#guard NativeAtom.eval .mapSet [two, .str "c", .nat 3] =
  some (.list [.pair (.str "b") (.nat 2), .pair (.str "c") (.nat 3), .pair (.str "d") (.nat 4)])
#guard NativeAtom.eval .mapSet [two, .str "e", .nat 5] =
  some (.list [.pair (.str "b") (.nat 2), .pair (.str "d") (.nat 4), .pair (.str "e") (.nat 5)])
#guard NativeAtom.eval .mapSet [two, .str "b", .str "new"] =
  some (.list [.pair (.str "b") (.str "new"), .pair (.str "d") (.nat 4)])
#guard NativeAtom.eval .mapKeys [two] = some (.list [.str "b", .str "d"])
#guard NativeAtom.eval .mapEntries [two] =
  some (.list [.list [.str "b", .nat 2], .list [.str "d", .nat 4]])

#guard NativeAtom.eval .mapFromEntries [.list []] = some empty
#guard NativeAtom.eval .mapFromEntries [.list
    [.list [.str "x", .nat 1], .list [.str "x", .nat 2]]] =
  some (.list [.pair (.str "x") (.nat 2)])
#guard NativeAtom.eval .mapFromEntries [.list
    [.list [.str "z", .nat 0], .list [.str "a", .nat 1], .list [.str "z", .nat 2]]] =
  some (.list [.pair (.str "a") (.nat 1), .pair (.str "z") (.nat 2)])

#guard NativeAtom.eval .mapGet [.list [.pair (.str "x") .unit], .str "x"] = some (.some .unit)
#guard NativeAtom.eval .mapGet [.list [.pair (.str "x") .none], .str "x"] = some (.some .none)
#guard NativeAtom.eval .mapGet [.list [.pair (.str "x") (.some .none)], .str "x"] =
  some (.some (.some .none))
#guard NativeAtom.eval .mapGet [.list [.pair (.str "x") (.handle 1 9)], .str "x"] =
  some (.some (.handle 1 9))
#guard NativeAtom.eval .mapFromEntries [.list
    [.list [.str "2", .unit], .list [.str "10", .unit]]] =
  some (.list [.pair (.str "10") .unit, .pair (.str "2") .unit])
#guard NativeAtom.eval .mapFromEntries [.list
    [.list [.str "𐀀", .unit], .list [.str "", .unit]]] =
  some (.list [.pair (.str "") .unit, .pair (.str "𐀀") .unit])
#guard NativeAtom.eval .mapGet [.list [.pair (.str "__proto__") (.nat 7)], .str "__proto__"] =
  some (.some (.nat 7))
#guard NativeAtom.eval .mapGet [.list [.pair (.str "") (.nat 8)], .str ""] = some (.some (.nat 8))

-- Malformed raw shapes refuse. Each conversion reads its own pair representation.
#guard NativeAtom.eval .mapGet [.list [.list [.str "x", .nat 1]], .str "x"] = none
#guard NativeAtom.eval .mapFromEntries [.list [.pair (.str "x") (.nat 1)]] = none
#guard NativeAtom.eval .mapFromEntries [.list [.list [.nat 0, .nat 1]]] = none
#guard NativeAtom.eval .mapFromEntries [.list [.list [.str "x"]]] = none
#guard NativeAtom.eval .mapSet [.unit, .str "x", .nat 1] = none
#guard NativeAtom.eval .mapGet [two, .nat 0] = none
#guard NativeAtom.eval .mapKeys [.list [.pair (.nat 0) .unit]] = none
#guard nativeAtom "mapGet" [two, .str "d"] = some (.some (.nat 4))

#print axioms Machine.Map.fromEntries
#print axioms Machine.Map.set
#print axioms NativeAtom.eval
#print axioms NativeAtom.ofName?_name

end Test.Program.MapValues
