/-!
# The constructor lane: every constructor of a natively spelled type, lowered and run

Each type that the LCNF route spells natively (its type table, `OCaml5.Lcnf.typeRows`) has no
declared record or variant in OCaml. So each of its constructors and projections is lowered by an
owner (`OCaml5.Lcnf.nativeOwner?`): a row, OCaml's own datatype, the clock, or the transparent
field. The functions below build, match and project each one, beside a user's variant and
structure for contrast. `ocaml/gen/roots.json` lowers them into
`ocaml/engine/test/ctors/ctors_gen.ml`. The dune test there makes each call of `answers` and
compares its answer with Lean's, which `write.lean` writes into `ctors.txt`.

The lane catches what the route's own module check (`Ml.checkModule`) passes and `ocamlopt`
refuses. `ByteArray.mk` built a record of no declared type, and a match on a `UInt8` called the
extern `UInt8.toBitVec`, which had no row (`docs/research/2026-10-16-ocaml-constructors/README.md`).
Lean's compiler takes `Int` and `Nat` apart by comparison, so no `cases` on either reaches the
route: `intMatch` and `natMatch` exercise that.
-/

namespace Test.Codegen.ConstructorLane

/-! ## Int: `int`, which has no constructor -/
def intOfNat (n : Nat) : Int := Int.ofNat n
def intNegSucc (n : Nat) : Int := Int.negSucc n
def intMatch : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 100
def intMatchZero (i : Int) : Bool :=
  match i with
  | .ofNat 0 => true
  | _ => false

/-! ## Nat: `int` -/
def natSucc (n : Nat) : Nat := Nat.succ n
def natZero : Nat := Nat.zero
def natMatch : Nat → Nat
  | 0 => 7
  | n + 1 => n

/-! ## Array: the runtime library's vector, `Lcnf_array` -/
def arrMk (l : List Nat) : Array Nat := Array.mk l
def arrToList (a : Array Nat) : List Nat := a.toList
def arrMatch : Array Nat → Nat
  | ⟨l⟩ => l.length

/-! ## ByteArray: a vector of bytes, `int Lcnf_array.t` -/
def baMk (a : Array UInt8) : ByteArray := ⟨a⟩
def baData (b : ByteArray) : Array UInt8 := b.data
def baMatch : ByteArray → Array UInt8
  | ⟨a⟩ => a

/-! ## String: `string` -/
def strBytes (s : String) : ByteArray := s.toByteArray
def strMatch : String → ByteArray
  | ⟨b, _⟩ => b
def strOfBytes (b : ByteArray) (h : b.IsValidUTF8) : String := String.fromUTF8 b h

/-! ## Char: its code point -/
def charOfNat (n : Nat) : Char := Char.ofNat n
def charVal (c : Char) : UInt32 := c.val
def charMatch : Char → UInt32
  | ⟨v, _⟩ => v

/-! ## The fixed-width words, BitVec and Fin: each its one field

`USize` has its rows too; Lean's own compiler refuses a match on one ("unexpected IR type"). -/
def u8OfBitVec (b : BitVec 8) : UInt8 := UInt8.ofBitVec b
def u8Match : UInt8 → BitVec 8
  | ⟨b⟩ => b
def u16OfBitVec (b : BitVec 16) : UInt16 := UInt16.ofBitVec b
def u16Match : UInt16 → BitVec 16
  | ⟨b⟩ => b
def u32OfBitVec (b : BitVec 32) : UInt32 := UInt32.ofBitVec b
def u32Match : UInt32 → BitVec 32
  | ⟨b⟩ => b
def u64OfBitVec (b : BitVec 64) : UInt64 := UInt64.ofBitVec b
def u64Match : UInt64 → BitVec 64
  | ⟨b⟩ => b
def bvMatch : BitVec 8 → Nat
  | ⟨f⟩ => f.val
def finMk (n : Nat) (h : n < 10) : Fin 10 := ⟨n, h⟩
def finMatch : Fin 10 → Nat
  | ⟨v, _⟩ => v

/-! ## Subtype: no row, a structure Lean's compiler represents by its one field -/
def subMk (n : Nat) (h : n > 0) : {n : Nat // n > 0} := ⟨n, h⟩
def subMatch : {n : Nat // n > 0} → Nat
  | ⟨v, _⟩ => v
def subVal (s : {n : Nat // n > 0}) : Nat := s.val

/-! ## OCaml's own constructors -/
def optMatch : Option Nat → Nat
  | none => 0
  | some n => n
def listMatch : List Nat → Nat
  | [] => 0
  | x :: _ => x
def prodMatch : Nat × String → Nat
  | (n, _) => n
def exceptMatch : Except String Nat → Nat
  | .ok n => n
  | .error _ => 0
def exceptMk (b : Bool) : Except String Nat := if b then .ok 1 else .error "no"
def unitMatch : Unit → Nat
  | () => 3

/-! ## A user's types: a declared variant and a declared record, for contrast -/
inductive Shade where
  | light
  | dark (level : Nat)
structure Pt where
  x : Nat
  y : Int
def shadeMatch : Shade → Nat
  | .light => 0
  | .dark n => n
def ptMk (x : Nat) (y : Int) : Pt := ⟨x, y⟩
def ptY (p : Pt) : Int := p.y

/-! ## Array's update rows: a minimal hash map over `replicate`, `uget` and `uset`

The rows that Lean's own hash maps need (slice 3.2 of the OCaml estate refactor). The lane runs
insertion, lookup, an update of a bound key, and the versions a program keeps: a map that a later
insertion is built from still answers as it did, and two insertions into one map each keep their
own binding. Above 256 buckets the vector has a frozen chunk and an open one, and the keys below
reach both. -/

/-- Buckets of `(key, value)` pairs; a key's bucket is the key modulo the bucket count. -/
structure NatMap where
  buckets : Array (List (Nat × Nat))

/-- `n + 1` empty buckets, so the bucket count is never zero. -/
def NatMap.empty (n : Nat) : NatMap := ⟨Array.replicate (n + 1) []⟩

/-- The bucket of a key. -/
def NatMap.slot (m : NatMap) (k : Nat) : USize := (k % m.buckets.size).toUSize

/-- The map with `k` bound to `v`, in place of an earlier binding of `k`. -/
def NatMap.insert (m : NatMap) (k v : Nat) : NatMap :=
  let i := m.slot k
  if h : i.toNat < m.buckets.size then
    ⟨m.buckets.uset i ((k, v) :: (m.buckets.uget i h).filter (·.1 != k)) h⟩
  else m

/-- The value bound to `k`, if any. -/
def NatMap.find? (m : NatMap) (k : Nat) : Option Nat :=
  let i := m.slot k
  if h : i.toNat < m.buckets.size then (m.buckets.uget i h).lookup k else none

/-- The bindings of `kvs`, inserted in order into `n + 1` buckets. -/
def NatMap.ofList (n : Nat) (kvs : List (Nat × Nat)) : NatMap :=
  kvs.foldl (fun m kv => m.insert kv.1 kv.2) (NatMap.empty n)

/-- Insertion and lookup: the map of `kvs` in `n + 1` buckets, read at `k`. -/
def mapFind (n : Nat) (kvs : List (Nat × Nat)) (k : Nat) : Option Nat :=
  (NatMap.ofList n kvs).find? k

/-- The layout: each bucket's bindings, in bucket order, the newest first. -/
def mapBuckets (n : Nat) (kvs : List (Nat × Nat)) : List (List (Nat × Nat)) :=
  (NatMap.ofList n kvs).buckets.toList

/-- A kept version: the map of `kvs` read at `k`, before and after one more binding of `k`. -/
def mapRetained (n : Nat) (kvs : List (Nat × Nat)) (k v : Nat) : Option Nat × Option Nat :=
  let m := NatMap.ofList n kvs
  (m.find? k, (m.insert k v).find? k)

/-- Siblings: two insertions of `k` into one map, each read, and the map they share. -/
def mapSiblings (n : Nat) (kvs : List (Nat × Nat)) (k : Nat) :
    Option Nat × Option Nat × Option Nat :=
  let m := NatMap.ofList n kvs
  let a := m.insert k 1
  let b := m.insert k 2
  (a.find? k, b.find? k, m.find? k)

private def opt : Option Nat → String
  | none => "-"
  | some n => toString n

private def bucketText (b : List (Nat × Nat)) : String :=
  ",".intercalate (b.map fun kv => s!"{kv.1}:{kv.2}")

/-- The keys of the large map: a thousand squares, so its 301 buckets fill both chunks. -/
def squares : List (Nat × Nat) := (List.range 1000).map fun i => (i, i * i)

/-- Each call the dune test makes, with Lean's answer, one per line. -/
def answers : List String := [
  s!"intOfNat 5 = {intOfNat 5}", s!"intNegSucc 4 = {intNegSucc 4}",
  s!"intMatch -3 = {intMatch (-3)}", s!"intMatch 7 = {intMatch 7}",
  s!"intMatchZero 0 = {intMatchZero 0}", s!"intMatchZero -1 = {intMatchZero (-1)}",
  s!"intMatchZero 2 = {intMatchZero 2}",
  s!"natSucc 4 = {natSucc 4}", s!"natZero = {natZero}", s!"natMatch 0 = {natMatch 0}",
  s!"natMatch 5 = {natMatch 5}",
  s!"arrMk = {(arrMk [1, 2]).toList}", s!"arrToList = {arrToList #[3, 4]}",
  s!"arrMatch = {arrMatch #[1, 2, 3]}",
  s!"baMk = {(baMk #[5, 6]).toList}",
  s!"baData = {(baData ⟨#[1, 2]⟩).toList}", s!"baMatch = {(baMatch ⟨#[7]⟩).toList}",
  s!"strBytes = {(strBytes "hé").toList}", s!"strMatch = {(strMatch "ab").toList}",
  s!"strOfBytes = {strOfBytes "hé".toByteArray "hé".isValidUTF8}",
  s!"charOfNat 65 = {(charOfNat 65).val}", s!"charOfNat 55296 = {(charOfNat 55296).val}",
  s!"charVal = {charVal 'z'}", s!"charMatch = {charMatch 'A'}",
  s!"u8OfBitVec = {u8OfBitVec 200}", s!"u8Match = {(u8Match 201).toNat}",
  s!"u16OfBitVec = {u16OfBitVec 60000}", s!"u16Match = {(u16Match 60001).toNat}",
  s!"u32OfBitVec = {u32OfBitVec 4000000000}", s!"u32Match = {(u32Match 4000000001).toNat}",
  s!"u64OfBitVec = {u64OfBitVec 123456789012}", s!"u64Match = {(u64Match 123456789013).toNat}",
  s!"bvMatch = {bvMatch 7}",
  s!"finMk = {finMk 3 (by decide)}", s!"finMatch = {finMatch 9}",
  s!"subMk = {(subMk 4 (by decide)).val}", s!"subMatch = {subMatch ⟨6, by decide⟩}",
  s!"subVal = {subVal ⟨8, by decide⟩}",
  s!"optMatch none = {optMatch none}", s!"optMatch some = {optMatch (some 4)}",
  s!"listMatch = {listMatch [9, 1]}", s!"prodMatch = {prodMatch (5, "x")}",
  s!"exceptMatch ok = {exceptMatch (.ok 3)}", s!"exceptMatch error = {exceptMatch (.error "e")}",
  s!"exceptMk true = {exceptMatch (exceptMk true)}",
  s!"exceptMk false = {exceptMatch (exceptMk false)}",
  s!"unitMatch = {unitMatch ()}", s!"shadeMatch = {shadeMatch (.dark 4)}",
  s!"ptY = {ptY (ptMk 1 (-2))}",
  s!"mapFind bound = {opt (mapFind 4 [(1, 10), (7, 70), (12, 120)] 7)}",
  s!"mapFind absent = {opt (mapFind 4 [(1, 10), (7, 70), (12, 120)] 5)}",
  s!"mapFind updated = {opt (mapFind 4 [(1, 10), (6, 60), (1, 11)] 1)}",
  s!"mapBuckets = {" | ".intercalate ((mapBuckets 2 [(1, 10), (2, 20), (4, 40), (1, 11)]).map bucketText)}",
  s!"mapRetained = {opt (mapRetained 4 [(1, 10)] 1 99).1} {opt (mapRetained 4 [(1, 10)] 1 99).2}",
  s!"mapSiblings frozen = {opt (mapSiblings 300 [(3, 30)] 8).1} {opt (mapSiblings 300 [(3, 30)] 8).2.1} {opt (mapSiblings 300 [(3, 30)] 8).2.2}",
  s!"mapSiblings open = {opt (mapSiblings 300 [(3, 30)] 290).1} {opt (mapSiblings 300 [(3, 30)] 290).2.1} {opt (mapSiblings 300 [(3, 30)] 290).2.2}",
  s!"mapLarge frozen = {opt (mapFind 300 squares 777)}",
  s!"mapLarge open = {opt (mapFind 300 squares 290)}",
  s!"mapLarge absent = {opt (mapFind 300 squares 1000)}"]

/-- The fixture: `answers` under the generated header, which `write.lean` writes beside the test. -/
def fixtureText : String :=
  "# GENERATED by Test/Codegen/ConstructorLane.lean; do not edit.\n" ++
  "# Write again: lake env lean --run ocaml/engine/test/ctors/write.lean\n" ++
  String.intercalate "\n" answers ++ "\n"

end Test.Codegen.ConstructorLane
