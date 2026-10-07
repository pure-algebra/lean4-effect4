import Effect4.Laws.Codegen.Metadata

/-!
# Structural type metadata controls

These are finite controls of the structural target reader. The universal retraction and
exactness laws are in `Laws/Codegen/Metadata.lean`. No target compiler or runtime is involved.
-/

namespace Effect4.Test.Metadata
open Effect4.Program Effect4.Store Effect4.Codegen.Metadata TypeScript

-- Three source types remain distinct despite their common TypeScript spelling.
#guard readTy (writeTy .nat) == some Ty.nat
#guard readTy (writeTy .int) == some Ty.int
#guard readTy (writeTy .number) == some Ty.number
#guard writeTy .nat != writeTy .int
#guard writeTy .nat != writeTy .number

-- Raw order, duplicate declarations and absent optional types are retained.
#guard readTy (writeTy (.record [("z", true, .undefined), ("a", false, .nat)])) ==
  some (Ty.record [("z", true, .undefined), ("a", false, .nat)])
#guard readTy (writeTy (.record [("x", false, .nat), ("x", true, .option .string)])) ==
  some (Ty.record [("x", false, .nat), ("x", true, .option .string)])
#guard readTy (writeTy (.record [("__proto__", true, .option .undefined)])) ==
  some (Ty.record [("__proto__", true, .option .undefined)])

-- Structural metadata needs no closed-variable or byte-frame-size premise.
#guard readTy (writeTy (.var (2 ^ 64 + 1))) == some (Ty.var (2 ^ 64 + 1))
#guard writeNat (2 ^ 64 + 1) ==
  Expr.arr [.int 1, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 1]
#guard readNat (.arr []) == some 0
#guard readNat (writeNat (2 ^ 128 + 257)) == some (2 ^ 128 + 257)

-- Digits cannot truncate, change sign, or use an alternate leading-zero image.
#guard readNat (.arr [.int (-1)]) == none
#guard readNat (.arr [.int 256]) == none
#guard readNat (.arr [.int 0]) == none
#guard readNat (.arr [.int 0, .int 1]) == none
#guard readNat (.int 9007199254740993) == none
#guard readBytes (.arr [.int 0, .int 255]) == some [0, 255]

-- The value reader rejects foreign syntax, unassigned tags and wrong arities.
#guard readValue (.ident "undefined") == none
#guard readValue (.arr [.int 0]) == none
#guard readValue (.arr [.int 9, .int 0]) == none
#guard readValue (.arr [.int 2, .int 1]) == none
#guard readValue (.arr [.int 14, writeNat (2 ^ 64)]) == none

-- All value frames have one structural image, including raw non-WF float data.
#guard readValue (writeValue (.pair (.handle 255 (2 ^ 80)) (.float 0))) ==
  some (Val.pair (.handle 255 (2 ^ 80)) (.float 0))
#guard readValue (writeValue (.ctor (2 ^ 90) [.bytes [0, 255], .negInt (2 ^ 75)])) ==
  some (Val.ctor (2 ^ 90) [.bytes [0, 255], .negInt (2 ^ 75)])
#guard readValue (writeValue (.ref 255 [0, 17, 255])) == some (Val.ref 255 [0, 17, 255])

example (t : Ty) : readTy (writeTy t) = some t := readTy_writeTy t
example (e : Expr) (t : Ty) (h : readTy e = some t) : writeTy t = e := readTy_exact e t h

end Effect4.Test.Metadata
