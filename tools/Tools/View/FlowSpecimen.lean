import Tools.View.Flow
import Effect4.Store.Domain.ProgramWire

/-!
# The program graph's specimen: each case of a flow, one program a page

A tool control of the program graph (`Tools.View.Flow`; slices D2 and D3 of
`docs/research/2026-10-09-program-graph-design.md`). Each page draws one small program's lines and
its flow, so each case of the layout is seen at work:

- fork and join: a fiber awaited by its parent's next step stands before the join, and the await
  after it;
- a wait inside a region: the await is not in the parent's series, so the wait is a cross edge,
  from the fiber's exit to the await, in a lane at the right, and the await stands below the exit;
- a fiber that awaits another fiber: a cross edge between two branches;
- `awaitAll` over two fibers: one node with two waits;
- a race: branches that all start, joined;
- a handler around a scope: a choice below a region;
- a loop: its head, its body, and the return.

The programs need not type-check: the flow reads their structure and their binders alone.
-/

namespace Tools.View.FlowSpecimen

open Effect4 Effect4.Program Effect4.Program.Wire.Corpus Tools.View

/-- A small fiber: a yield, then a value. -/
def work (n : Nat) : NativeEff := .bind (.yieldNow 0) (.succeed (.lit (.nat n)))

/-- A fork of `e`, as the program writes it. -/
def forkOf (e : NativeEff) : NativeEff := .withFiber (.fork e forkOptions)

/-- The specimen's programs, each with its name and what it shows. -/
def programs : List (String × String × NativeEff) :=
  [ ("fork and join", "the await of the fiber stands after the join",
      .bind (forkOf (work 7)) (.awaitFiber (.var 0) .awaitValue)),
    ("a wait inside a region", "a cross edge from the fiber's exit down to the await in the scope",
      .bind (forkOf (work 7)) (.scoped (.bind (.yieldNow 0) (.awaitFiber (.var 0) .awaitValue)))),
    ("a fiber awaits a fiber", "a cross edge between two branches; the parent joins the second fiber",
      .bind (forkOf (work 1)) (.bind (forkOf (.awaitFiber (.var 0) .awaitValue)) (.awaitFiber (.var 1) .awaitValue))),
    ("await all", "one node waits for two fibers",
      .bind (forkOf (work 1)) (.bind (forkOf (work 2))
        (.withFiber (.awaitAll (.app "list" (.cons (.var 0) (.cons (.var 1) .nil))))))),
    ("a race", "every branch starts; the race ends when one does",
      .withFiber (.raceAll (.cons (work 1) (.cons (work 2) (.cons (.yieldNow 0) .nil))))),
    ("a handler around a scope", "a region, then a choice: the handler, or nothing",
      .catchCause (.scoped (.bind (.yieldNow 0) (.fail (.lit (.nat 1))))) (.succeed (.lit (.nat 0)))),
    ("a loop", "its head, its body, and the return",
      .iterate none (.lit (.nat 0)) (.app "isZero" (.cons (.var 0) .nil)) (.app "succ" (.cons (.var 0) .nil))
        (.lit .unit) (.yieldNow 0)) ]

/-- One page: the program's lines, and its flow below them. -/
def page (i : Nat) (name what : String) (program : NativeEff) : Page :=
  let session := EditSession.open {} { program }
  let g := Program.sessionPage session none ("flow · " ++ name) what s!"{i + 1} / {programs.length}" ""
  { g with graph := some { title := "program", laid := Flow.ofPage program g } }

/-- The specimen's pages. -/
def frames : List Page := programs.zipIdx.map fun ((name, what, p), i) => page i name what p

end Tools.View.FlowSpecimen
