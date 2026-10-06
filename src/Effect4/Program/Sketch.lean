import Effect4.Program.SigApp

/-!
# Program.Sketch — a program with its hole table

A **sketch** is a program that is not finished: some of its parts are not written yet. Each
part that is not written is a **hole**. A sketch is data: a program and its **hole table**, one
**hole row** for each hole (`Sketch`). Decisions rows 282 and 288 rule it, for requirement R14.

## A hole is a host row with a declared type

A host row is an operation that a program performs and that the host answers. Its row declares
its request, its answer, its error and its requirement (`Row`, `Program/Eff.lean`). A hole row is
such a row with a unit request (`Row.hole`): it declares the type of the program that will
stand at the hole. The hole table stands after the application's row table
(`SigApp.withHoles`), and hole `k` is the operation at position `k` after the application's
rows (`Sketch.hole`).

So a hole adds no constructor to `Eff`, `Term` or `Ty`, and no rule to the typing judgment. The
program of a sketch is an ordinary `Eff` term. Every fold, the checker, the printer and the wire
read it as they read any program.

## The checker admits a sketch modulo its holes

`Sketch.check` runs the checker on the program, at the application's typing signature extended
by the hole table. At a hole the checker reads the hole's row, as it reads any host row. A
program is a sketch with no hole, and its check is then the checker's own answer.

The laws are in `Laws/Program/Sketch.lean`. A hole has its declared type in every environment
(`Sketch.hole_hasTy`). A program that performs no hole is checked the same with any hole table
(`holes_conservative`). A sketch stays admitted when more holes are declared
(`sketch_more_holes`), and the checker reads the rows of the holes that the sketch performs and
no later row (`sketch_reads_its_holes`).

## The parallel with a planned goal, and where it stops

A sketch is to its holes as a theorem is to its planned goals (`proof_goal`, decisions row 203).

| A theorem and its planned goals | A sketch and its holes |
| --- | --- |
| `proof_goal G : P` names a statement with no proof | a hole row names a type with no program |
| downstream proofs use `G` as a theorem | the program performs the hole as an operation |
| the kernel accepts the theorem modulo `G` | the checker admits the sketch modulo its holes |
| a claim is proved only when it rests on no goal | program admission reads the application's tables alone, so it refuses a program that performs a hole |

The parallel stops at four places.

- **Truth.** A goal's statement can be false, and then no proof fills it. A hole row declares a
  type, and no judgment of this module says whether a program of that type exists.
- **Relevance.** Any proof of a goal serves. Two programs of one type behave differently, and
  no law of a sketch says anything of behaviour.
- **Number.** A goal is used wherever a proof cites it. A hole is meant for one address of one
  program. The data does not enforce that: a program can perform one hole row at two addresses,
  and each address is then filled on its own.
- **Running.** A proof with a goal does not run. A hole row has the form of a row that the host
  answers, so a run could wait at a hole as it waits at any host row. That is decided with its
  first consumer (decisions row 288, point 10), and no law of this module states a run.

## How a hole is named, and what an edit keeps

`Eff` writes a host row by its position, so a hole's stored name is its position `k` in the
hole table. The table only grows while a sketch is open, so no edit moves a position.
Declaring a hole appends a row. Filling a hole leaves its row in place, and the checker no
longer reads it. A hole is given another type by declaring a new hole. The row's spelling is the
label that the printer prints and that an author calls, as for every host row
(`Authoring.Row.call`, `Program/Authoring.lean`).

A sketch is pinned to the row count of its application, as a program is pinned to its table
(decisions row 115): `Sketch.hole app k` names the position after `app.rows`.

## The request of a hole row

It is a unit. The hole's rule then holds in every environment, and the row does not change when
the program before the hole changes. The environment of a hole is the checker's to compute. A
row that stored it would be a second owner of that fact.

This module is not a Lean module (decisions row 200): it imports `Program/SigApp.lean`, which is
not one, because `Program/Columns.lean` imports a specialization site of decisions row 202.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)

/-- A sketch: a program with its hole table. A hole of the program is a host row of `holes`,
performed at a position after the application's rows (`Sketch.hole`). The hole table defaults
to the empty one, so `{ program := e }` is the program `e` as a sketch. -/
structure Sketch where
  /-- the program, an ordinary `Eff` term -/
  program : NativeEff
  /-- the hole table: one hole row for each hole, in the order of declaration -/
  holes : RowTable := []

/-- A program is a sketch with no hole. Its check is the checker's own answer
(`Sketch.check_program`, `Laws/Program/Sketch.lean`). -/
instance : Coe NativeEff Sketch := ⟨fun program => { program }⟩

/-- An application's tables with a hole table appended after its rows. The service
declarations are unchanged. The typing signature of the result extends the application's
(`SigApp.withHoles_extends`, `Laws/Program/Sketch.lean`). -/
def SigApp.withHoles (app : SigApp) (holes : RowTable) : SigApp :=
  { app with rows := app.rows ++ holes }

/-- A hole row: a host row with a unit request that declares three columns, the answer, the
error and the requirement of the program that will stand at the hole. The spelling is the name.
It is a row that the host answers (`kind := .async`, `registration := .external`), as
`Authoring.Row.host` declares one. It transcribes no line of rc.112, so its citation is
empty. -/
def Row.hole (name : String) (answer : Ty) (error : Ty := .never)
    (requires : List ServiceKey := []) : Row :=
  { name := name, spelling := name, shape := .call, trailing := [], kind := .async,
    request := .unit, answer := answer, error := error, requires := requires, cite := "",
    typeArgs := [], registration := .external }

namespace Sketch

/-- Hole `k` over an application, as a program: it performs the row at position `k` of the hole
table, which stands after the application's rows, on a unit request. -/
def hole (app : SigApp) (k : Nat) : NativeEff :=
  .perform (.external (app.rows.length + k)) (.lit .unit)

/-- **The check of a sketch**: the checker's answer on the program at the root, at the
application's typing signature extended by the hole table. It answers the program's type or the
checker's located refusal. A sketch is **admitted modulo its holes** at the type `t` when
`s.check app = .ok t`. The checker refuses a layer reference here as it does on any program. -/
def check (s : Sketch) (app : SigApp := {}) : Except TypeRefusal EffTy :=
  Checker.check (app.withHoles s.holes).signature [] [] s.program

end Sketch

end Effect4.Program
