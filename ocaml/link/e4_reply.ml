(* e4_reply.ml — a one-shot reply cell across domains.

   What it is: the answer channel of a control request (`Inspect`): the asker creates the
   cell and blocks in `await`; the owning worker fills it once with plain data (ints,
   strings, records of them — never a Lean value). `Mutex` + `Condition`.
   Depends on: nothing in the library.

   Properties:
     P1  At most one value: a second `fill` raises `Invalid_argument` and leaves the first
         value in place. [by construction; tested: reply-once]
     P2  `await` returns the filled value, to every waiter, exactly as filled; it blocks
         until then. [by construction; tested: reply-once] *)

type 'a t = { mu : Mutex.t; cv : Condition.t; mutable value : 'a option }

let create () = { mu = Mutex.create (); cv = Condition.create (); value = None }

let fill t v =
  Mutex.protect t.mu (fun () ->
      match t.value with
      | Some _ -> invalid_arg "E4_reply.fill: already filled"
      | None ->
          t.value <- Some v;
          Condition.broadcast t.cv)

let await t =
  Mutex.protect t.mu (fun () ->
      while t.value = None do
        Condition.wait t.cv t.mu
      done;
      Option.get t.value)

let peek t = Mutex.protect t.mu (fun () -> t.value)
