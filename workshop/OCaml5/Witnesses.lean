import OCaml5.Effect

/-!
# OCaml 5 spike: witnesses

Status: scaffold, 2026-09-03. Module `OCaml5.Witnesses`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, ruling 6. Owners: spike O1 (handler machine
witnesses) and O3 (value witnesses).

A witness is an OCaml source file under `workshop/OCaml5/witnesses/`, compiled and run on both
hosts by `workshop/OCaml5/tools/run-witness.sh`, whose printed rows are transcribed here next to
the `Term` the Lean machine runs. The first corpus is
`/Users/pooks/Dev/effect4_of_ocaml/ocaml/effects5_capabilities.ml`: forwarding through a handler
that answers `None`, innermost-wins shadowing, a continuation parked in a `ref` and discontinued
later, `discontinue` through `Fun.protect ~finally`, `Effect.Unhandled`, and
`Continuation_already_resumed` on a second `continue`.
-/

namespace OCaml5

universe u

/-- One row printed by an instrumented witness. The spelling is fixed by
`tools/run-witness.sh`: tab-separated, first cell the event kind. -/
abbrev Row := String

/-- A witness: the source file, the rows each host printed, and the term with the outcome and
events the Lean machine must produce. The two host row lists must be equal to each other and
to `Event.render` of the machine's trace. -/
structure Witness (ν : Type u) : Type u where
  name : String
  source : String
  nativeRows : List Row
  jsooRows : List Row
  term : Term ν
  expectedEvents : List Event
deriving Repr

/-- The row spelling of an event, to be matched byte for byte against the hosts. -/
def Event.render : Event → Row
  | .perform eff cont => s!"perform\t{eff.value}\t{cont}"
  | .reperform eff cont => s!"reperform\t{eff.value}\t{cont}"
  | .resume stack => s!"resume\t{stack}"
  | .runstack stack => s!"runstack\t{stack}"
  | .returnToParent stack => s!"return\t{stack}"
  | .raiseToParent stack => s!"raise\t{stack}"
  | .unhandled eff => s!"unhandled\t{eff.value}"
  | .alreadyResumed => "already-resumed"
  | .contUsed cont => s!"cont-used\t{cont}"
  | .contDropped cont => s!"cont-dropped\t{cont}"
  | .trapEntered => "trap"
  | .trapCaught exn => s!"caught\t{exn.value}"

/-- Host agreement is a decidable fact of the transcribed rows. -/
def Witness.hostsAgree {ν : Type u} (w : Witness ν) : Bool := w.nativeRows == w.jsooRows

end OCaml5
