import Effect4.Laws.Program.Sketch

/-!
# A sketch (decisions row 288): the controls of slice SKETCH

`Program/Sketch.lean` defines a sketch, a program with its hole table, and
`Laws/Program/Sketch.lean` holds its laws. These are the fixtures of the study's section 9.7
(`docs/research/2026-10-06-seat-GAP-study.md`), on the type slicing plan's own example:

    x = succeed 5;  cell = Ref.make(x);  _ = Ref.set(cell, 7);  Ref.get(cell)

* **Green (tested).** The first child is a hole declared at `number`: the checker admits the
  sketch modulo its holes, at the original's type.
* **Red (tested): the hole declared at `string`.** The checker refuses the sketch at the write,
  before any filling exists.
* **Red (tested): the sketch at the application's own tables.** The checker refuses the program
  at the hole, as an operation outside the domain. So program admission, which reads those
  tables alone, takes no program that performs a hole.
* **Red (proved): a hole row before the application's rows** is no extension: the application's
  own call reads the hole's row (`prepend_not_extends`, `Test/Program/SignatureControls.lean`).
* **The laws at this example (proved)**: a program is a sketch (`Sketch.check_program`); the
  filled sketch is an ordinary program (H1); more holes keep the verdict (H2); the hole has its
  declared type in every environment (the hole's rule). Each premise of the hole's rule has a
  red control. One more control shows what the check does not decide: raw formation of a hole
  row.
* **The form at a row table alone (proved)**: H1 at `nativeSignature`, by the same theorem.
* **A service declaration and the requirement column (tested)**: the laws are stated at the
  application's signature, and a hole declares a requirement.
* **Red (tested): a sketch is pinned to the row count of its application.** When the application
  gains a row, a stale hole reads the row that now stands at its position.
* **Which hole rows are lawful host rows (tested)**: the signature's own admission answers.
-/

set_option autoImplicit false

namespace Test.Program.SketchControls

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

/-! ## The example -/

/-- `pair(a, b)`: the request of `Ref.set`. -/
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-- `x = FIRST; cell = Ref.make(x); _ = Ref.set(cell, 7); Ref.get(cell)`: the example's context
around its first child. -/
def context (first : NativeEff) : NativeEff :=
  .bind first
    (.bind (.perform .refMake (.var 0))
      (.bind (.perform .refSet (pairT (.var 1) (.lit (.nat 7))))
        (.perform .refGet (.var 1))))

/-- The example: the first child is `succeed 5`. -/
def original : NativeEff := context (.succeed (.lit (.nat 5)))

/-- The example as a sketch over the empty application: the first child is hole 0, declared at
the answer `answer`. -/
def sketchAt (answer : Ty) : Sketch :=
  { program := context (Sketch.hole {} 0), holes := [Row.hole "h0" answer] }

/-- The path and the reason's name of a refusal. -/
def refusedAt (r : Except TypeRefusal EffTy) : Option (List Nat × String) :=
  (Checker.refusal r).map fun why => (why.path, why.reason.head)

/-! ## Green and red: the sketch is admitted modulo its holes, or refused before a filling -/

-- tested: the original is admitted at `number`
#guard Checker.check ({} : SigApp).signature [] [] original = .ok ⟨.nat, .never, Requirement.empty⟩
-- green (tested): the hole declared at `number`; the sketch has the original's type
#guard (sketchAt .nat).check = .ok ⟨.nat, .never, Requirement.empty⟩
-- red (tested): the hole declared at `string`; the write of a number is refused, at the write
#guard refusedAt (sketchAt .string).check = some ([1, 1, 0], "requestNotSubtype")
-- red (tested): the sketch's program at the application's own tables is refused at the hole
#guard Checker.check ({} : SigApp).signature [] [] (sketchAt .nat).program =
  .error ⟨[0], .outsideDomain "external"⟩

/-! ## The laws at the example -/

/-- **A program is a sketch (proved).** The check of the original as a sketch is the checker's
answer on it. -/
theorem original_is_a_sketch :
    Sketch.check (original : Sketch) = Checker.check ({} : SigApp).signature [] [] original :=
  Sketch.check_program {} original

/-- The hole filled by `succeed 5`, with its row left in the table. -/
def filled : Sketch := { program := original, holes := [Row.hole "h0" .nat] }

/-- The original performs only the application's operations: it is a Σ-program. -/
theorem original_sigProgram : SigProgram ({} : SigApp).signature original :=
  ⟨trivial, rfl, rfl, rfl⟩

/-- **H1 at the example (proved).** The filled sketch is checked as its program: the row that
the program no longer performs changes nothing. -/
theorem filled_is_the_program :
    filled.check = Checker.check ({} : SigApp).signature [] [] original :=
  Sketch.check_filled filled {} original_sigProgram

/-- **H2 at the example (proved).** A second hole is declared, and the sketch keeps its type. -/
theorem more_holes_keep_the_type :
    Sketch.check { sketchAt .nat with holes := (sketchAt .nat).holes ++ [Row.hole "h1" .string] } =
      .ok ⟨.nat, .never, Requirement.empty⟩ :=
  Sketch.check_more_holes (sketchAt .nat) {} [Row.hole "h1" .string] (by decide +kernel)

/-- **H1 at a row table alone (proved).** The statement at `nativeSignature` is the instance of
`holes_conservative` at an application with no service declaration, by definition
(`SigApp.signature_nil`). -/
theorem holes_conservative_table (table holes : RowTable) {e : NativeEff}
    (hp : SigProgram (nativeSignature table) e) (env : TyEnv) (p : List Nat) :
    Checker.check (nativeSignature (table ++ holes)) env p e =
      Checker.check (nativeSignature table) env p e :=
  holes_conservative ⟨table, []⟩ holes hp env p

/-! ## The hole's rule, and its premises -/

/-- A hole declared at a cell of numbers, with the error `string`. -/
def cellHole : RowTable := [Row.hole "h0" (.refOf .nat) .string]

/-- **The hole's rule at a cell (proved).** The hole has its declared type in every
environment. The checker types the hole, and the signature's admission refuses the same row as
a host row that runs (`cell_hole_does_not_run` below). -/
theorem cell_hole_has_its_type (env : TyEnv) :
    HasTy (({} : SigApp).withHoles cellHole).signature env (Sketch.hole {} 0)
      ⟨.refOf .nat, .string, Requirement.empty⟩ :=
  Sketch.hole_hasTy {} cellHole 0 env rfl rfl rfl
    ((Formation.check_eq_none_iff _).mp (by decide +kernel))

-- tested: and the checker answers that type in an environment that is not empty
#guard Checker.check (({} : SigApp).withHoles cellHole).signature [.bool, .nat] [] (Sketch.hole {} 0) =
  .ok ⟨.refOf .nat, .string, Requirement.empty⟩

-- red (tested), the premise `closed`: a hole row that declares a template parameter does not
-- have its declared type; the checker closes the parameter that no request binds to `never`
#guard (Ty.var 0).closed = false
#guard Sketch.check { program := Sketch.hole {} 0, holes := [Row.hole "h0" (.var 0)] } =
  .ok ⟨.never, .never, Requirement.empty⟩

/-- A closed type that is not formed: a map whose key is a number (decisions row 193). -/
def numberKeyMap : Ty := .map .nat .string

-- red (tested), the premise `formed`: the row check refuses the hole at its use
#guard numberKeyMap.closed = true
#guard refusedAt (Sketch.check { program := Sketch.hole {} 0, holes := [Row.hole "h0" numberKeyMap] }) =
  some ([], "instantiatedFormation")

/-- A raw type that the normalizer repairs: a record with one field name twice (decisions row
192). -/
def repeatedField : Ty := .record [("a", false, .nat), ("a", false, .string)]

-- tested: what the check does not decide. The checker reads a row's columns in normal form, and
-- the normalizer drops the repeated name, so the checker types this hole. Raw formation refuses
-- the row, as program admission refuses it in an application's table. A sketch's own admission
-- is not in this slice.
#guard Sketch.check { program := Sketch.hole {} 0, holes := [Row.hole "h0" repeatedField] } =
  .ok ⟨repeatedField.normalize, .never, Requirement.empty⟩
#guard repeatedField.normalize != repeatedField
#guard (Formation.checkInput (Sketch.hole {} 0) [Row.hole "h0" repeatedField]).isSome

/-! ## The three columns: an error and a requirement -/

/-- A service key at a fresh code. -/
def greetKey : ServiceKey := ⟨⟨12⟩, ⟨12⟩⟩

-- tested: a hole's declared error joins its context's error
#guard Sketch.check { program := .bind (Sketch.hole {} 0) (.succeed (.lit (.nat 1))),
                      holes := [Row.hole "h0" .never .string] } =
  .ok ⟨.nat, .string, Requirement.empty⟩
-- tested: a hole's declared requirement is the sketch's
#guard Sketch.check { program := Sketch.hole {} 0, holes := [Row.hole "h0" .nat .never [greetKey]] } =
  .ok ⟨.nat, .never, Requirement.single greetKey⟩

/-! ## An application with a row and a service declaration -/

/-- A host row with a unit request that answers a number. -/
def hostA : Row :=
  { name := "a", spelling := "A.a", kind := .async, request := .unit, answer := .nat,
    cite := "control", registration := .external }

/-- An application: one host row, and one service declared at a fresh code. -/
def app : SigApp := ⟨[hostA], [(greetKey, .string)]⟩

/-- `g = service greet; hole 0` over `app`: the hole stands after the application's one row. -/
def withService : Sketch :=
  { program := .bind (.service greetKey) (Sketch.hole app 0), holes := [Row.hole "h0" .bool] }

-- tested: the sketch reads the application's service declaration and its own hole
#guard withService.check app = .ok ⟨.bool, .never, Requirement.single greetKey⟩
-- red (tested): at the row table alone the key has no carrier, so the laws are stated at the
-- application's signature and not at the table's
#guard refusedAt (withService.check ⟨[hostA], []⟩) = some ([0], "serviceUnknown")

/-! ## Red: a hole row before the application's rows is no extension -/

/-- `yield* A.a()`: the application's row at position 0. -/
def callA : NativeEff := .perform (.external 0) (.lit .unit)

-- tested: with a hole row put first, the application's own call answers the hole's type
#guard effTy (nativeSignature [hostA]) [] callA = some ⟨.nat, .never, Requirement.empty⟩
#guard effTy (nativeSignature ([Row.hole "h0" .string] ++ [hostA])) [] callA =
  some ⟨.string, .never, Requirement.empty⟩

/-- **Red control (proved).** A hole row put before the application's rows is not an extension:
position 0 is admitted by both tables, at two rows. So the hole table stands after the rows. -/
theorem hole_before_not_extends :
    ¬ SigExtends (nativeSignature [hostA]) (nativeSignature ([Row.hole "h0" .string] ++ [hostA])) := by
  intro h
  have hrow := (h.row (.external 0) rfl).2
  have hanswer := congrArg Row.answer hrow
  exact absurd hanswer (by decide +kernel)

/-! ## Red: a sketch is pinned to the row count of its application

A hole's stored name is a position after the application's rows. When the application gains a
row, every hole's position moves by one, and the stored program does not follow: a stale hole
is not refused as such. It reads the row that now stands at its position. A renumbering of the
program's operations is an open obligation (the slice's receipt). -/

/-- A second host row with a unit request, which answers a string. -/
def hostB : Row := { hostA with name := "b", spelling := "B.b", answer := .string }

/-- A host row whose request is a number. -/
def hostC : Row := { hostA with name := "c", spelling := "C.c", request := .nat }

/-- A sketch over the application `[hostA]`: one hole, declared at `boolean`, at the root. -/
def pinned : Sketch :=
  { program := Sketch.hole ⟨[hostA], []⟩ 0, holes := [Row.hole "h0" .bool] }

-- tested: over its own application the hole has its declared type
#guard pinned.check ⟨[hostA], []⟩ = .ok ⟨.bool, .never, Requirement.empty⟩
-- red (tested): the application gains a row with a unit request; the stale hole reads that row,
-- and the sketch is admitted at another type
#guard pinned.check ⟨[hostA, hostB], []⟩ = .ok ⟨.string, .never, Requirement.empty⟩
-- red (tested): the application gains a row with another request; the stale hole is refused, at
-- the hole, for the new row's request
#guard pinned.check ⟨[hostA, hostC], []⟩ = .error ⟨[], .requestNotSubtype "c" .unit .nat⟩
-- tested: with the hole written again at its new position the sketch has its type again
#guard Sketch.check { pinned with program := Sketch.hole ⟨[hostA, hostB], []⟩ 0 } ⟨[hostA, hostB], []⟩ =
  .ok ⟨.bool, .never, Requirement.empty⟩

/-! ## Which hole rows are lawful host rows

A hole row has the form of a row that the host answers. The signature's own admission
(`admitSig`) says which hole rows could wait at a frontier as a host row does: a hole of data
can, and a hole of a cell cannot (decisions row 97). It refuses two holes of one name. -/

-- tested: a hole of data is a lawful host row
#guard admitSig (({} : SigApp).withHoles [Row.hole "h0" .nat]) = .ok ()
-- red (tested): a hole of a cell is checked (`cell_hole_has_its_type`) and is no lawful host row
#guard admitSig (({} : SigApp).withHoles cellHole) = .error (.row 0 (.internalHandle "answer"))
-- red (tested): two holes of one name share a row key
#guard admitSig (({} : SigApp).withHoles [Row.hole "h0" .nat, Row.hole "h0" .string]) =
  .error (.duplicateRow ("h0", []))

end Test.Program.SketchControls
