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

A row's error column is answered by a **fallible method** (`Reactor.fallible`): its function
answers `Except E Ans`, and a failure crosses as the typed failure of `E`'s value
(`Program.errOf`), as an untyped host writes one. A tagged failure `prod (lit tag) string`
(`eff_failure Name message`) is a derived one-constructor enum paired with a string.
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

/-- **A fallible method**: the row spelled `spelling`, answered by `f`, whose failure is the row's
error column. The request is read by `Modeled.image Req`; a success is written by
`Modeled.image Ans`, and a failure is the typed failure of `Modeled.image E`'s value
(`Program.errOf`). Any other row, and a request that does not read, is declined. -/
def Reactor.fallible {σ Req Ans E : Type} [Modeled Req] [Modeled Ans] [Modeled E]
    (spelling : String) (f : Req → σ → Except E Ans × σ) : Reactor σ :=
  fun row sent state =>
    if row.spelling == spelling then
      ((Modeled.image Req).ofVal sent).map fun request =>
        let (answer, next) := f request state
        match answer with
        | .ok value => (.ofExit (.success ((Modeled.image Ans).toVal value)), next)
        | .error e =>
          (.ofExit (.failure (Cause.fail (Program.errOf ((Modeled.image E).toVal e)))), next)
    else none

/-- **A host of several reactors**: the first that answers a request answers it. -/
def Reactor.first {σ : Type} : List (Reactor σ) → Reactor σ
  | [] => fun _ _ _ => none
  | r :: rest => fun row sent state =>
    (r row sent state).orElse fun _ => Reactor.first rest row sent state

end Effect4.Run
