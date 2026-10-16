import Effect4.Run.Basic
import Effect4.Schema.Modeled

/-!
# Run.Method — a typed host: each row answered by a function over Lean types

A host is a function (`Run.Reactor`): a row, its request as a value, and the host's state in; a
completion and the next state out, or `none` for a request it does not answer. A **method**
answers one row by a function over Lean types. The request is read by its type's exact embedding
(`Modeled.image`), and the answer written by the answer type's. A request that does not read is
declined, as any reactor declines a request it does not answer, so the session sees a declined
call, never a guessed value. A host is its methods, the first that answers winning
(`Reactor.first`).

So a host written against rows is a record of Lean functions, and its values cross the boundary
only through derived codecs. Lowered by the LCNF route, the record is a native OCaml record of
functions over native OCaml types, and the codecs are the staged images
(`ocaml/engine/test/todo/`, decisions row 405).

What it does not do yet: answer a row's error column. A method answers a success; a failing
method is the next slice.
-/

namespace Effect4.Run

open Effect4.Schema

/-- **A method**: the row spelled `spelling`, answered by `f`. The request is read by
`Modeled.image Req`, and the answer written by `Modeled.image Ans` as a success. Any other row,
and a request that does not read, is declined. -/
def Reactor.method {σ Req Ans : Type} [Modeled Req] [Modeled Ans] (spelling : String)
    (f : Req → σ → Ans × σ) : Reactor σ := fun row sent state =>
  if row.spelling == spelling then
    ((Modeled.image Req).ofVal sent).map fun request =>
      let (answer, next) := f request state
      (.ofExit (.success ((Modeled.image Ans).toVal answer)), next)
  else none

/-- **A host of several reactors**: the first that answers a request answers it. -/
def Reactor.first {σ : Type} : List (Reactor σ) → Reactor σ
  | [] => fun _ _ _ => none
  | r :: rest => fun row sent state =>
    (r row sent state).orElse fun _ => Reactor.first rest row sent state

end Effect4.Run
