(* todo_core.ml -- the to-do repository written natively in OCaml, as a pure module.

   What it is: the four rows of `TodoRepo` (Test/Dogfood/Scenario/Todo/Data.lean) answered over
   this module's own types, with the host's state threaded as a value: the next id and the
   stored to-dos. It states what `Typed.model` states (Test/Dogfood/Scenario/Todo/Typed.lean),
   written by hand in OCaml, not lowered. `native_todo.ml` adapts it to the lowered `host` record,
   and the Rocq worked example (docs/research/2026-10-16-ocaml-interop/rocq/) reads this file.
   Depends on: nothing. It uses no library function, so that rocq-of-ocaml reads it alone.

   Properties:
   C1  Every function is total: each recursion is structural on a list.     by construction
   C2  `insert` answers the id `next`, and the next state's `next` is one more.
                                                   tested (test_todo T14); proved (Rocq, insert_id)
   C3  Each function keeps the ids of `items` strictly ascending and below `next`; so an id is
       stored at most once, and ordering the to-dos by id is their stored order.
                                                   proved (Rocq, step_keeps_ordered)
   C4  `set_done` and `delete` at an absent id change nothing, and answer `None` and `false`.
                                                   proved (Rocq, absent_set_done, absent_delete)
   C5  No function fails: the error type is the rows' error, which a host built over this core
       answers only through `native_todo.ml`'s fault hooks.               by construction *)

type todo =
  { id : int
  ; title : string
  ; done_ : bool
  }

(* The rows' error: the tag `SqlError`, written as this one constructor, and its message. *)
type error = Sql_error of string

(* The repository: the next id and the stored to-dos, in insertion order. *)
type t =
  { next : int
  ; items : todo list
  }

let rec snoc (items : todo list) (item : todo) : todo list =
  match items with
  | [] -> [ item ]
  | x :: rest -> x :: snoc rest item
;;

let rec find (id : int) (items : todo list) : todo option =
  match items with
  | [] -> None
  | x :: rest -> if x.id = id then Some x else find id rest
;;

let rec mark (id : int) (d : bool) (items : todo list) : todo list =
  match items with
  | [] -> []
  | x :: rest -> (if x.id = id then { x with done_ = d } else x) :: mark id d rest
;;

let rec mem (id : int) (items : todo list) : bool =
  match items with
  | [] -> false
  | x :: rest -> x.id = id || mem id rest
;;

let rec remove (id : int) (items : todo list) : todo list =
  match items with
  | [] -> []
  | x :: rest -> if x.id = id then remove id rest else x :: remove id rest
;;

let insert (title : string) (s : t) : (todo, error) result * t =
  let item = { id = s.next; title; done_ = false } in
  Ok item, { next = s.next + 1; items = snoc s.items item }
;;

let all (_ : unit) (s : t) : (todo list, error) result * t = Ok s.items, s

let set_done (request : int * bool) (s : t) : (todo option, error) result * t =
  let id, d = request in
  match find id s.items with
  | None -> Ok None, s
  | Some x -> Ok (Some { x with done_ = d }), { next = s.next; items = mark id d s.items }
;;

let delete (id : int) (s : t) : (bool, error) result * t =
  Ok (mem id s.items), { next = s.next; items = remove id s.items }
;;
