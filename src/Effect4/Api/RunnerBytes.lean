import Effect4.Api.RunnerDerived

/-!
# Api.RunnerBytes: the runner across a byte boundary

`Api.Runner` plays commands. A holder on any host keeps bytes: a journal is a list of rows and a
row is the canonical bytes of one `Command`. This module is the runner at that boundary and
nothing else: it reads a row, plays it, and writes the verdict. It owns no codec. Every codec
here is a generated `Canonical` instance (`Api/RunnerDerived.lean`), so the OCaml and the
TypeScript holders get the same bytes from the same declarations.

* **One row, one command.** `commandOf` answers a command only for bytes that are exactly one
  command (`commandOf_exact`): a journal has one spelling.
* **An unreadable row is not a command.** `stepBytes` answers `none` as the verdict and leaves
  the runner alone (`stepBytes_unreadable`). It is not a session refusal, because the session
  never saw a command.
* **Replay is the same action.** `replayBytes` folds `stepBytes`, and it distributes over
  concatenation (`replayBytes_append`), like `Runner.replay`.
* **Every boundary value carries its schema.** `schemas` lists the shape document of every
  type that crosses, and `schemaBytes` writes one as content, by the instance of `ShapeDoc`
  itself (`Store/Derived/Value.lean`).

A value inside a row (a call's request, a reply's answer) is written as its description, the
generated sum `Val`. A live handle therefore never enters content as a handle: a shape accepts
no handle (`Store/Shape.lean`), and a described handle is two numbers. Whether a holder should
refuse a row that describes one is a policy above this module.
-/

set_option autoImplicit false

namespace Effect4.Api.Runner

open Effect4 Effect4.Store
open Effect4.Api.HostSession (Header Phase)

/-- The row of a command. -/
def commandBytes (c : Command) : Bytes := Canonical.encode c

/-- The command of a row, exactly: `none` unless the bytes are one command and nothing else. -/
def commandOf (row : Bytes) : Option Command := Canonical.decode row

/-- The verdict of a row as content: the phase it ended in, or `none` for a row that is not a
command. -/
def verdictBytes (verdict : Option Phase) : Bytes := Canonical.encode verdict

/-- The verdict of its bytes, exactly. -/
def verdictOf (bytes : Bytes) : Option (Option Phase) := Canonical.decode bytes

/-- One row played: the next runner and the verdict. An unreadable row changes nothing. -/
def stepRow (p : Runner) (row : Bytes) : Runner × Option Phase :=
  match commandOf row with
  | none => (p, none)
  | some c => ((step p c).1, some (step p c).2)

/-- `stepRow` with the verdict written as content. -/
def stepBytes (p : Runner) (row : Bytes) : Runner × Bytes :=
  ((stepRow p row).1, verdictBytes (stepRow p row).2)

/-- A journal of rows played from a runner: the runner it reaches and every row's verdict. -/
def replayRows (p : Runner) : List Bytes → Runner × List (Option Phase)
  | [] => (p, [])
  | row :: rest =>
    ((replayRows (stepRow p row).1 rest).1,
      (stepRow p row).2 :: (replayRows (stepRow p row).1 rest).2)

/-- `replayRows` with every verdict written as content. -/
def replayBytes (p : Runner) (rows : List Bytes) : Runner × List Bytes :=
  ((replayRows p rows).1, (replayRows p rows).2.map verdictBytes)

/-- What a holder schedules by, as content. -/
def observeBytes (p : Runner) : Bytes := Canonical.encode (observe p)

/-- The calls the machine is waiting on, as content. -/
def outstandingBytes (p : Runner) : Bytes := Canonical.encode (outstanding p)

/-- The shape document of every type that crosses the boundary, by the name a holder asks
for. -/
def schemas : List (String × ShapeDoc) :=
  [ ("Command", Canonical.shape Command)
  , ("Verdict", Canonical.shape (Option Phase))
  , ("Header", Canonical.shape Header)
  , ("State", Canonical.shape HostProtocol.State)
  , ("Outstanding", Canonical.shape (List Program.Await))
  , ("Program", Canonical.shape Api.Program)
  , ("Value", Canonical.shape Val)
  , ("Schema", Canonical.shape ShapeDoc) ]

/-- One schema, by name. -/
def schemaOf (name : String) : Option ShapeDoc := List.lookup name schemas

/-- One schema as content, by name. It is read back by the `Schema` entry of this table. -/
def schemaBytes (name : String) : Option Bytes := (schemaOf name).map Canonical.encode

end Effect4.Api.Runner
