import Effect4.Program.Ty
import Effect4.Schema.Bridge
import Effect4.Program.Admission

/-!
# The data wave's type forms: the order, normalization and formation (decisions rows 119, 125,
157–162, 177, 178)

Finite controls on the eight appended constructors (`Effect4/Program/TyCore.lean`), from probe P's
copy (`docs/research/2026-10-01-type-language-probe/P/probes/P2Ty.lean`): TY-10's acceptance item
(a permuted record is below its normal form both ways), exact width and flags (row 178 (a)), the
map's exact key and covariant value, tuples at exact arity, a reference at its declared variances
(row 158), the leaf table's four edges with `nat ⊑ number` derived, and the formation scans. The red
control of the leaf table — a cyclic table relates two heads both ways — is kept here too.
-/

namespace Test.Program.TyWave

open Effect4.Program

-- TY-10's positive control: a permuted record is raw-below its normal form, both ways.
#guard Ty.sub (.record [("b", false, .nat), ("a", false, .string)])
  (Ty.normalize (.record [("b", false, .nat), ("a", false, .string)]))
#guard Ty.sub (Ty.normalize (.record [("b", false, .nat), ("a", false, .string)]))
  (.record [("b", false, .nat), ("a", false, .string)])
-- depth holds; width (a field dropped or added) does not; a flag must match (row 178 (a))
#guard Ty.sub (.record [("tag", false, .lit "A")]) (.record [("tag", false, .string)])
#guard !Ty.sub (.record [("a", false, .nat), ("b", false, .string)]) (.record [("a", false, .nat)])
#guard !Ty.sub (.record [("a", false, .nat)]) (.record [("a", false, .nat), ("b", false, .string)])
#guard !Ty.sub (.record [("a", false, .nat)]) (.record [("a", true, .nat)])
#guard !Ty.sub (.record [("a", true, .nat)]) (.record [("a", false, .nat)])
-- the canonical order is the UTF-8 byte order: `X` (0x58) before `_tag` (0x5F) before `a` (0x61)
#guard Ty.normalize (.record [("a", false, .nat), ("_tag", false, .lit "A"), ("X", false, .nat)]) =
  .record [("X", false, .nat), ("_tag", false, .lit "A"), ("a", false, .nat)]
-- a map: exact in the key, covariant in the value (row 125)
#guard Ty.sub (.map .string (.lit "a")) (.map .string .string)
#guard !Ty.sub (.map .string .string) (.map .string (.lit "a"))
#guard !Ty.sub (.map (.lit "k") .nat) (.map .string .nat)
-- formation: a repeated field name, located; a map's key type is `string`
#guard Ty.findRepeatedField [] (.record [("a", false, .nat), ("a", false, .string)]) = some ([], "a")
#guard Ty.findRepeatedField [] (.list (.record [("x", false, .record [("b", false, .nat), ("b", true, .nat)])])) =
  some (["inner", "x"], "b")
#guard Ty.findRepeatedField [] (.record [("a", false, .nat), ("b", false, .string)]) = none
#guard Ty.mapKeyOk .string && !Ty.mapKeyOk .nat && !Ty.mapKeyOk (.lit "a") &&
  !Ty.mapKeyOk (.union (.lit "a") (.lit "b"))
-- a pair tuple is a product; other arities stay tuples; `app t []` is `handle t` (rows 158, 159)
#guard Ty.normalize (.tuple [.nat, .string]) = .prod .nat .string
#guard Ty.normalize (.tuple [.union .string .nat, .nat, .bool]) = .tuple [.union .nat .string, .nat, .bool]
#guard Ty.normalize (.app "Stream.Stream" []) = .handle "Stream.Stream"
#guard Ty.sub (.tuple [.lit "a", .nat, .bool]) (.tuple [.string, .nat, .bool])
#guard !Ty.sub (.tuple [.nat, .nat, .nat]) (.tuple [.nat, .nat])
-- a reference reads each argument at its declaration's variance: `Fiber<out A, out E>` is
-- covariant, `Ref<in out A>` invariant, an undeclared name invariant
#guard Ty.sub (.app "Fiber.Fiber" [.lit "x", .never]) (.app "Fiber.Fiber" [.string, .nat])
#guard !Ty.sub (.app "Ref.Ref" [.lit "x"]) (.app "Ref.Ref" [.string])
#guard Ty.sub (.app "Queue.Dequeue" [.union .nat .string]) (.app "Queue.Dequeue" [.union .string .nat])
-- the leaf order, read from the table: four declared edges, `nat` below `number` their composite
#guard Ty.leafEdges.length = 4 && !Ty.leafEdges.contains (.nat, .number)
#guard Ty.leafLe .nat .number && Ty.leafLe .lit .string && !Ty.leafLe .number .nat
#guard Ty.sub .nat .int && Ty.sub .int .number && Ty.sub .nat .number && Ty.sub .undefined .unit
#guard Ty.sub (.lit "a") .string && !Ty.sub (.lit "a") (.lit "b") && !Ty.sub (.lit "a") .number
#guard !Ty.sub .int .nat && !Ty.sub .number .int && !Ty.sub .unit .undefined && !Ty.sub .null .unit
-- red control: a cyclic table (`int` below `nat` added) relates `nat` and `int` both ways
#guard Ty.leafReach ((.int, .nat) :: Ty.leafEdges) 5 .nat .int &&
  Ty.leafReach ((.int, .nat) :: Ty.leafEdges) 5 .int .nat
-- the spellings
#guard Ty.renderRaw (.record [("a", false, .nat), ("b", true, .string)]) =
  "{ readonly a: number; readonly b?: string }"
#guard Ty.renderRaw (.map .string .bool) = "Readonly<Record<string, boolean>>"
#guard Ty.renderRaw (.tuple [.nat, .string, .bool]) = "readonly [number, string, boolean]"
#guard Ty.renderRaw (.app "Queue.Dequeue" [.nat]) = "Queue.Dequeue<number>"
#guard Ty.renderRaw .null = "null" && Ty.renderRaw .undefined = "undefined" &&
  Ty.renderRaw .number = "number" && Ty.renderRaw .bytes = "Uint8Array"
-- the key keeps today's union order: the old heads' codes are unchanged
#guard Ty.key .nat = [2] && Ty.key (.lit "a") = [15, 97]
#guard Ty.normalize (.union .bytes .null) = .union .null .bytes

-- The unlowered marker refuses at the reader (decisions row 162), at every appended head and under
-- a former, while a handle of the marker's own name, the two forms that normalize away and the
-- leaves already lowered keep their images.
open Effect4.Schema in
#guard [("app", Ty.app "x" [.nat]), ("null", .null), ("undefined", .undefined), ("number", .number),
    ("bytes", .bytes)].all fun (h, t) =>
  Bridge.ofSchema (Bridge.unlowered h) == none && Bridge.ofSchema (Bridge.schema t) == none
open Effect4.Schema in
#guard Bridge.ofSchema (Ty.schema (.option (.record []))) == some (.option (.record []))
open Effect4.Schema in
#guard Bridge.ofSchema (Ty.schema (.handle "effect4/unlowered/record")) ==
  some (.handle "effect4/unlowered/record")
open Effect4.Schema in
#guard Bridge.ofSchema (Ty.schema .nat) == some .nat
open Effect4.Schema in
#guard Bridge.ofSchema (Ty.schema (.tuple [.nat, .string])) == some (.prod .nat .string)
open Effect4.Schema in
#guard Bridge.ofSchema (Ty.schema (.app "effect4/unlowered/record" [])) ==
  some (.handle "effect4/unlowered/record")
open Effect4.Schema in
#guard Bridge.ofSchema (Ty.schema (.var 0)) == none

-- Inhabitance at the record reads the canonical fields (row 127; probe P6's controls): a required
-- `never` field empties the record, an optional one is absent, the empty record and map are
-- inhabited, and of two fields with one name the first is the one kept.
#guard admitColumn (.record [("a", false, .never)]) == false
#guard inhabited (.record [("a", true, .never)])
#guard inhabited (.record [])
#guard inhabited (.map .string .never)
#guard inhabited (.record [("a", false, .nat), ("a", false, .never)])
#guard !inhabited (.record [("a", false, .never), ("a", false, .nat)])

end Test.Program.TyWave
