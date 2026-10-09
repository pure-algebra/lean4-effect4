import Effect4.Program.Sketch
import Effect4.Store.Domain.ProgramWire

/-!
# Program.SketchWire — a sketch's canonical bytes: its program's and its hole table's

A sketch is a program with its hole table (`Program/Sketch.lean`). Its bytes are two byte
strings: the program's canonical bytes (`Wire.encodeProgram`), and the hole table's, the store's
`encode` at the derived instance of `Row` (`Store/Domain/Derived/Program.lean`) and the list
instance. The pair is an exact embedding: a well-formed sketch reads back (`Sketch.decode_encode`),
and whatever reads was that sketch's bytes (`Sketch.decode_exact`), in
`Laws/Program/SketchWire.lean`. Both are the store's laws (`Canonical.decode_encode`,
`Canonical.decode_exact`) at the two carriers.

The consumer is the query tool (`tools/Tools/Query.lean`): a request may carry a hole table, and
an omission's answer carries the grown one, so the sketch it answers can be sent back. This is
the open part `sketch-wire` of R14 (decisions row 305, point 3).
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Store

/-- The canonical bytes of a hole table. -/
def Wire.encodeHoles (holes : RowTable) : Bytes := Canonical.encode holes

/-- The exact decoder of a hole table: the whole byte string is one hole table. -/
def Wire.decodeHoles (b : Bytes) : Option RowTable := Canonical.decode b

namespace Sketch

/-- **A sketch's bytes**: its program's, and its hole table's. -/
def encode (s : Sketch) : Bytes × Bytes := (Wire.encodeProgram s.program, Wire.encodeHoles s.holes)

/-- **The exact decoder of a sketch**: a program and a hole table, each the whole of its bytes. -/
def decode (b : Bytes × Bytes) : Option Sketch :=
  (Wire.decodeProgram b.1).bind fun program =>
    (Wire.decodeHoles b.2).map fun holes => { program, holes }

end Sketch

end Effect4.Program
