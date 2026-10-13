import Test.Dogfood.Scenario

/-!
# Test.Dogfood.Application — the record of an application's claims

Slice RECORD of the claims packet (`docs/research/2026-10-07-packet-application-claims.md`,
§3.3 and §3.4; decisions rows 307 (9) and 336 (9)). A claim of an application is a theorem or a
planned goal with its placement (`@[semantics …]`, decisions row 207). Its status is the plan's
(`#plan_status`): goal, modulo or proved. The record holds no status and no second mechanism.

* **The record is a scenario's record and one note for each of its entries.** The scenario names
  the application as its program, and `#scenario_gate` checks it as it checks any other scenario
  (`Test/Audit/ScenarioGate.lean`).
* **A note** says three things of one clause or law: its kind (where its truth comes from), the
  programs that its statement reads, and the premises that its statement assumes of whoever answers
  the rows, each with its grade (who discharges it).
* **`Record.problems`** checks the notes as data. A battery reads it with `#guard`, and its red
  controls show each finding (decisions row 301). The packet's second gate is not landed: row 375
  clears gates, and a name in a note is a name literal, which the elaborator resolves.
* **`Record.claimsOf`** answers what the record claims of one program, by kind.

What it does not establish: that a note's premises are the premises of its statement. The
statement names them. The record cannot read a statement, and no check here reads one.
-/

set_option autoImplicit false

namespace Test.Dogfood.Application

open Test.Dogfood.Scenario (Scenario Clause)

/-- Where the truth of a claim of an application comes from (the claims packet, §3.4). -/
inductive Kind
  /-- A law of every admitted program, read at this application's programs. -/
  | inherited
  /-- A fact of a program's call tree: it holds whatever answers the rows. -/
  | tree
  /-- A fact under a protocol of a row. -/
  | protocol
  /-- A fact under the laws of the rows: today, under a reference model of them. -/
  | laws
  /-- A fact of a whole run: fibers, scopes, time. -/
  | run
deriving DecidableEq, Repr

/-- Who discharges a premise of a claim: a grade of the premise, never a status of the claim
(the claims packet, §3.4). -/
inductive Grade
  /-- A theorem about a handler in Lean. -/
  | proved
  /-- The session, at each reply receipt. -/
  | monitored
  /-- A decision on one run's journal. -/
  | validated
  /-- Nobody: the claim names it. -/
  | assumed
deriving DecidableEq, Repr

/-- One premise that a claim's statement assumes of whoever answers the rows: a declaration, a
protocol or a model, with its grade. -/
structure Premise where
  name : Lean.Name
  grade : Grade
deriving DecidableEq, Repr

/-- What the record says of one clause or one law of its scenario: its kind, the programs that
its statement reads, and what its statement assumes of whoever answers the rows. -/
structure Note where
  /-- The clause's or the law's name in the scenario's record. -/
  entry : String
  kind : Kind
  /-- The application's programs that the statement reads, by name. -/
  reads : List String := []
  /-- The premises that the statement assumes, each with its grade. -/
  assumes : List Premise := []
  /-- The fragment on which the statement holds, as a declaration: a decided predicate on a
  program. A claim stated for named programs alone has none. -/
  fragment : Option Lean.Name := none

/-- The record of an application: the scenario's record, whose program is the application, and
one note for each of its clauses and laws. A status is no field: the plan derives it. -/
structure Record where
  /-- The application, as a declaration. -/
  application : Lean.Name
  /-- The names of the application's programs. -/
  programs : List String
  /-- The claim, the clauses, the laws, the named runs and the controls. -/
  scenario : Scenario
  notes : List Note

/-- The clauses and the laws of a record. -/
def Record.entries (r : Record) : List Clause := r.scenario.clauses ++ r.scenario.laws

/-- What a note says wrongly as data, each finding in a sentence: a program that the application
does not hold, a fact under a promise that assumes nothing, and a fact that holds whatever
answers yet names a premise. -/
def Note.problems (r : Record) (note : Note) : List String :=
  let quoted := r.scenario.name ++ ": the note \"" ++ note.entry ++ "\""
  (note.reads.filter (fun program => !r.programs.contains program)).map (fun program =>
    quoted ++ " reads the program \"" ++ program ++ "\", which the application does not hold") ++
  match note.kind, note.assumes with
  | .protocol, [] | .laws, [] => [quoted ++ " is a fact under a promise, and it assumes nothing"]
  | .tree, _ :: _ | .inherited, _ :: _ =>
    [quoted ++ " holds whatever answers, and it names a premise"]
  | _, _ => []

/-- What is wrong with a record's notes as data, each finding in a sentence: an entry with no
note or with two, a note that names no clause and no law, and each note's own findings. Empty for
a record with no finding. -/
def Record.problems (r : Record) : List String :=
  (r.entries.filterMap fun entry =>
    match (r.notes.filter (·.entry == entry.name)).length with
    | 1 => none
    | 0 => some (r.scenario.name ++ ": the entry \"" ++ entry.name ++ "\" has no note")
    | _ => some (r.scenario.name ++ ": the entry \"" ++ entry.name ++ "\" has two notes")) ++
  r.notes.flatMap fun note =>
    if !r.entries.any (·.name == note.entry) then
      [r.scenario.name ++ ": the note \"" ++ note.entry ++ "\" names no clause and no law"]
    else Note.problems r note

/-- **What the record claims of one program** (the claims packet's operation `claims`, §3.8, at
the record): each entry whose note reads the program, and each inherited law where the
application holds the program, with its declaration and its kind, in the record's order. The
status of each is the plan's (`#plan_status`), never the record's. -/
def Record.claimsOf (r : Record) (program : String) : List (String × Lean.Name × Kind) :=
  r.entries.filterMap fun entry =>
    (r.notes.find? (·.entry == entry.name)).bind fun note =>
      if note.reads.contains program || (note.kind == .inherited && r.programs.contains program)
      then some (entry.name, entry.claim, note.kind) else none

end Test.Dogfood.Application
