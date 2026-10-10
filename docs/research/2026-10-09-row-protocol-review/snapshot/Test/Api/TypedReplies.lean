import Effect4.Laws.Api.HostSession

/-!
# Replies at the call's checked instance: the battery (decisions row 183)

A host row from `List<A>` to `Option<A>`, called at a list of numbers. The session admits the
reply `some 1` at the call's instance `Option<number>`, which the row's own columns refuse.
Each line is a finite evaluation or a control (decisions row 301).
-/

set_option autoImplicit false

namespace Test.Api.TypedReplies

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession

/-- The template row of decisions row 183: `List<A>` to `Option<A>`. -/
def first : Row :=
  { name := "first", spelling := "L.first", kind := .async, registration := .external,
    request := .list (.var 0), answer := .option (.var 0), cite := "battery" }

def table : RowTable := [first]

/-- The list `[1]`, then the call on it: the call stands at the address `[1]`. -/
def program : Api.Program :=
  .bind (.succeed (.app "cons" (.cons (.lit (.nat 1)) (.cons (.app "nil" .nil) .nil))))
    (.perform (.external 0) (.var 0))

def header : Header := ⟨version, "session-R", "profile", table⟩

def initial : Option (Session program table) :=
  match start program table "profile" header 100 with
  | .ok s => some s
  | .error _ => none

def parked : Option (Session program table) :=
  initial.map fun s => (advance s 100 Api.evaluate).session

def call0 : Call := ⟨version, "session-R", table, 0, Api.root, .external 0, .list [.nat 1]⟩

def bound : Option (Session program table) :=
  parked.map fun s => (bindCall s call0 0).session

def reply (completion : Api.HostSession.Answer) : Reply :=
  ⟨version, "session-R", 0, ⟨Api.root, 0⟩, completion⟩

def some1 : Reply := reply (.ofExit (.success (.some (.nat 1))))
def someText : Reply := reply (.ofExit (.success (.some (.str "one"))))
def nothing : Reply := reply (.ofExit (.success .none))

-- finite evaluation: the session admits the program and parks the call on its request
#guard initial.isSome
#guard parked.map outstanding = some [⟨Api.root, 0, .external 0, .list [.nat 1]⟩]
-- finite evaluation: the registration keeps the call's address, where the checker's instance
-- answers `Option<number>`
#guard parked.map (fun s => originOf s.machine Api.root 0) = some (some [1])
#guard (instanceAt program table [1]).map (fun c => (c.request, c.answer)) =
  some (.list .nat, .option .nat)
-- finite evaluation: the session reads it from the table that `start` made, with no check
#guard initial.map (fun s => (s.callInstance [1]).map (·.answer)) = some (some (.option .nat))
-- control: the row's own columns refuse `some 1`, the one value no `Option<A>` template admits
#guard bound.map (fun s => (acceptReply table s.machine
  ⟨table, Api.root, 0, .external 0, .list [.nat 1], some1.completion⟩).isNone) = some true
-- finite evaluation: the session admits `some 1` at the call's instance, applies it, and the
-- program answers it
#guard bound.map (fun s => (submit s some1).phase) = some .preflight
#guard bound.map (fun s => (inspect (applyPending (submit s some1).session 100).session).exit) =
  some (some (.success (.some (.nat 1))))
-- control: a value outside the instance is refused
#guard bound.map (fun s => (submit s someText).phase) = some (.refused .envelope)
-- finite evaluation: the value every instance admits takes the row's own path, as before
#guard bound.map (fun s => (submit s nothing).phase) = some .preflight

end Test.Api.TypedReplies
