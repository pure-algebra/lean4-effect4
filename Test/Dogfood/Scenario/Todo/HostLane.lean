import Test.Dogfood.Scenario.Todo.HostRun
import Test.Dogfood.Scenario.Todo.CachedProgram

/-!
# The to-do host lane's fixture (LC-6)

The OCaml lane `ocaml/engine/test/todo/` runs the to-do's host run, lowered by the LCNF route
(`serveBuiltVal`, `serveBuiltForgetfulVal` in `Test/Dogfood/Scenario/Todo/HostRun.lean`), on each
request of one script, and compares the result's canonical bytes with Lean's. This module writes
the fixture it reads, `todo-host.txt`; the lane's writer (`ocaml/engine/test/todo/write.lean`)
prints it, and `scripts/generate.py --only fixtures` holds the committed file to it.

A request's block carries what the lowered root takes, as canonical bytes: the built program,
its rows, its type (the admission's one datum once proofs are erased), its row names and the
repository state before it. Then it carries Lean's two results, over the reference repository and
over the one that forgets a write. The script threads one repository: each request starts from
the state the reference repository left. Like the lowered roots, this module reaches no law
module, so a change of the law graph does not rerun the fixtures.

Each line below is a finite evaluation or a control (decisions row 301).
-/

namespace Test.Dogfood.Scenario.Todo.HostLane

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.Todo (Repo)
open Test.Dogfood.Scenario.Todo.Host
open Test.Dogfood.Scenario.Todo.Cached (consumerBuiltAt)
open Tools.RunChecks (literal)

/-- The script: each request's entry and literal arguments, in order. The second title lies
outside ASCII, where the lowered `String` row is exact only for its bytes (`OCaml5.Lcnf.TypeRows`):
the host run passes titles through, so its result must still be Lean's. -/
def script : List (String × List Val) :=
  [ ("add", [.str "milk"]), ("add", [.str "café 日本 🙂"]), ("list", []),
    ("complete", [.nat 1]), ("list", []), ("remove", [.nat 1]), ("list", []) ]

/-- One request of the lane: its entry, its built program, and the repository before it. -/
structure Request where
  entry : String
  built : Api.Built
  state : Repo

/-- The repository the script starts from: no to-do, the next id 1. -/
def start : Repo := (1, [])

/-- The script's requests, each built at its arguments, each starting from the state the
reference repository left. `none` when a request does not build. -/
def requestsFrom : Repo → List (String × List Val) → Option (List Request)
  | _, [] => some []
  | state, (entry, args) :: rest => do
    let lits ← args.mapM literal
    let built ← consumerBuiltAt entry (lits.map Authoring.lit)
    let after := (serveBuilt built state).2
    let more ← requestsFrom after rest
    return ⟨entry, built, state⟩ :: more

def requests : Option (List Request) := requestsFrom start script

/-- The row names of a built program as a value: each spelling and its position. -/
def namesVal (names : List (String × Nat)) : Val :=
  .list (names.map fun entry => .list [.str entry.1, .nat entry.2])

/-- Bytes in lowercase hexadecimal. -/
def hex (bytes : Store.Bytes) : String := Store.hexString bytes

/-- Lean's checked replay's verdict (`Effect4.Program.admit`) on one answer to the request's
first host call, after `Api.run`: a natural from fiber 0 at `token`. The engine's `admits` must
give the same. -/
def admitsNat (r : Request) (token : Nat) : Bool :=
  let m := (Api.run r.built.program 100000 r.built.table).machine
  (Effect4.Program.admit r.built.table m (.answerAsync ⟨0⟩ token (.ofExit (.success (.nat 7))))).isNone

/-- The value the reference repository answers the request's first host call with, when it
answers one with a success: what a host driver would hand the engine. -/
def firstAnswer (r : Request) : Option Val :=
  match (serveBuilt r.built r.state).1.1.head? with
  | some call => match call.completion with
    | .ofExit (.success v) => some v
    | _ => none
  | none => none

/-- Lean's checked replay's verdict on that answer, as `admitsNat` gives it for a natural. -/
def admitsFirst (r : Request) : Bool :=
  match firstAnswer r with
  | some v =>
    let m := (Api.run r.built.program 100000 r.built.table).machine
    (Effect4.Program.admit r.built.table m (.answerAsync ⟨0⟩ 0 (.ofExit (.success v)))).isNone
  | none => false

/-- One request's block of the fixture. -/
def Request.text (r : Request) : String :=
  "request " ++ r.entry ++ "\n" ++
  "program " ++ hex (Api.bytesOf r.built.program) ++ "\n" ++
  String.join (r.built.table.map fun row => "row " ++ hex (Store.Canonical.encode row) ++ "\n") ++
  "typed " ++ hex (Store.Canonical.encode r.built.admitted.toTypedProgram.ty) ++ "\n" ++
  "names " ++ hex (Store.Val.encode (namesVal r.built.rowNames)) ++ "\n" ++
  "state " ++ hex (Store.Val.encode (repoVal r.state)) ++ "\n" ++
  "result " ++ hex (Store.Val.encode (serveBuiltVal r.built r.state)) ++ "\n" ++
  "forgetful " ++ hex (Store.Val.encode (serveBuiltForgetfulVal r.built r.state)) ++ "\n" ++
  "admits " ++ toString (admitsNat r 0) ++ " " ++ toString (admitsNat r 1) ++ "\n" ++
  (match firstAnswer r with
    | some v => "answer " ++ hex (Store.Val.encode v) ++ " " ++ toString (admitsFirst r) ++ "\n"
    | none => "")

/-- The fixture: a header, then each request's block. `none` when a request does not build. -/
def fixtureText : Option String :=
  requests.map fun rs =>
    "# GENERATED by Test/Dogfood/Scenario/Todo/HostLane.lean; do not edit.\n" ++
    "# Write again: lake env lean --run ocaml/engine/test/todo/write.lean\n" ++
    String.join (rs.map Request.text)

-- finite evaluation: every request of the script builds
#guard (requests.map List.length) == some 7
-- finite evaluation: the script leaves two to-dos' worth of ids used and one to-do stored
#guard (requests.map fun rs => rs.getLast?.map fun r => (r.state.1, r.state.2.length)) ==
  some (some (3, 1))
-- finite evaluation: Lean refuses a natural as the answer of each request's first call (each
-- row answers a to-do, a list or an option), and refuses the stale token as well
#guard (requests.map fun rs => rs.all fun r => !admitsNat r 0 && !admitsNat r 1) == some true
-- finite evaluation: Lean admits the reference repository's own answer to each first call
#guard (requests.map fun rs => rs.all fun r => (firstAnswer r).isSome && admitsFirst r) == some true
-- finite evaluation: the typed host (`Typed.model`, the interop plan's P1) gives every request
-- the reference repository's result, byte for byte: the lane's T10 and T11 compare with it
#guard (requests.map fun rs => rs.all fun r =>
  Store.Val.encode (serveBuiltTypedVal Typed.model r.built r.state) ==
    Store.Val.encode (serveBuiltVal r.built r.state)) == some true
-- control: the repository that forgets a write answers another result on some request, so the
-- lane's comparison can tell the two hosts apart
#guard (requests.map fun rs => rs.any fun r =>
  Store.Val.encode (serveBuiltVal r.built r.state) !=
    Store.Val.encode (serveBuiltForgetfulVal r.built r.state)) == some true

end Test.Dogfood.Scenario.Todo.HostLane
