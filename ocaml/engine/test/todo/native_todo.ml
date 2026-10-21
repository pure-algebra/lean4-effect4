(* native_todo.ml -- the to-do rows answered by hosts written in OCaml.

   What it is: every host of the to-do lane that is not lowered from Lean. The rows' interface is
   the OCaml module type `REPO`, the lowered `host` record (Todo_gen.host) read as a signature
   whose state is abstract; `host` turns a module of that type into a value of the record. The
   lowered `Typed.Host.reactor` then reads each request and writes each answer through the
   derived codecs, and a failure crosses as the rows' typed failure (decisions row 405). REPO and
   `host` are the shape a generator would emit from `Typed.Host`; they are written here by hand
   to try that shape first (docs/research/2026-10-16-ocaml-interop/README.md).
   The hosts:
     Untyped  the repository over the wire's values, building each frame by hand (T9);
     record   the repository as a value of the record over the lane's state (T11), and
              `broken`, whose insert fails with the rows' error (T13);
     Core     todo_core.ml, a pure module with its own types, behind REPO (T14);
     Table    an imperative repository over a hash table, as a native service holds its data,
              with a fault hook that may raise before each method (T14 to T16).
   `catching` maps chosen OCaml exceptions to the rows' typed failure; any other exception is no
   answer at all (E4_host's H5).
   Depends on: Todo_gen (GENERATED), Todo_core, Eff_types.

   Properties:
   N1  A module of type REPO is a host: `host` builds the lowered record from it, and the compiler
       refuses a module that lacks a method or answers another type.        by construction
   N2  Core answers as Typed.model: a run over it is Lean's, byte for byte.  tested (T14)
   N3  Table answers as Typed.model on a state whose ids ascend (todo_core's C3): its `all` and
       its snapshot order the to-dos by id.                                  tested (T14)
   N4  `catching f h`: a method that raises e with `f e = Some err` answers `Error err` at the
       state it received; any other exception is raised again, unchanged.  tested (T15, T16)
   N5  A host's state is abstract to the driver: REPO's `t` is the only state the record threads,
       and no host here reads another's.                                    by construction *)

open Eff_types

(* The rows' error, as the lowered code carries it: the tag and the message. *)
type sql_error = Todo_gen.sql_tag * string

(* The lane's repository state (`Repo`): the next id, then each to-do's id, title and flag. An
   id is a Lean natural, Zarith's `Z.t` (M4). *)
type lane_state = Z.t * (Z.t * (string * bool)) list

(* The lane's own operations on ids: Lean's `==` and order on naturals. *)
let find_id (id : Z.t) items =
  List.find_map (fun (i, e) -> if Z.equal i id then Some e else None) items
;;

let has_id (id : Z.t) items = List.exists (fun (i, _) -> Z.equal i id) items
let drop_id (id : Z.t) items = List.filter (fun (i, _) -> not (Z.equal i id)) items

let set_id (id : Z.t) d items =
  List.map (fun (i, (t, e)) -> if Z.equal i id then i, (t, d) else i, (t, e)) items
;;

(* ---------------------------------------------------------------- the interface *)

(* The rows of `TodoRepo` as an OCaml signature: one function per row, over the lowered types,
   threading the host's state `t`. *)
module type REPO = sig
  type t

  val insert : string -> t -> (Todo_gen.todo, sql_error) result * t
  val all : unit -> t -> (Todo_gen.todo list, sql_error) result * t
  val set_done : Z.t * bool -> t -> (Todo_gen.todo option, sql_error) result * t
  val delete : Z.t -> t -> (bool, sql_error) result * t
end

(* A module of type REPO as a value of the lowered record. *)
let host (type s) (module R : REPO with type t = s) : s Todo_gen.host =
  { Todo_gen.insert = R.insert; all = R.all; set_done = R.set_done; delete = R.delete }
;;

(* The host as the engine driver's provider: the lowered reactor over its record. *)
let provider (h : 's Todo_gen.host)
  : Row.t -> Val.t -> 's -> ((Val.t, Err.t, Defect.t, Z.t, unit) Completion.t * 's) option
  =
  Todo_gen.test_dogfood_scenario_todo_typed_host_reactor h
;;

(* Each method of `h`, with the exceptions `f` names answered as the rows' failure. *)
let catching (f : exn -> sql_error option) (h : 's Todo_gen.host) : 's Todo_gen.host =
  let guard m q s =
    try m q s with
    | e ->
      (match f e with
       | Some err -> Error err, s
       | None -> raise e)
  in
  { Todo_gen.insert = guard h.insert
  ; all = guard h.all
  ; set_done = guard h.set_done
  ; delete = guard h.delete
  }
;;

let todo id title d : Todo_gen.todo = { id; title; done_ = d }

(* --------------------------------------------------------------------- Untyped *)

(* The repository over the wire's values: a native host, not lowered from Lean. It answers the
   four rows as `repository` states them (Test/Dogfood/Scenario/Todo/Data.lean), over the lane's
   state, so the lowered `resultVal` packages its runs too. A to-do is the record frame with its
   fields in canonical order: done, id, title. *)
module Untyped = struct
  let todo id title is_done =
    Val.Ctor
      ( Z.zero
      , [ Val.List [ Val.Str "done"; Val.Str "id"; Val.Str "title" ]
        ; Val.List [ Val.Bool is_done; Val.Nat id; Val.Str title ]
        ] )
  ;;

  let ok v = Completion.OfExit (Exit.Success v)

  let provider (r : Row.t) (sent : Val.t) ((next, items) : lane_state) =
    match r.Row.spelling, sent with
    | "TodoRepo.insert", Val.Str title ->
      Some (ok (todo next title false), (Z.succ next, items @ [ next, (title, false) ]))
    | "TodoRepo.all", _ ->
      Some
        ( ok (Val.List (List.map (fun (id, (title, d)) -> todo id title d) items))
        , (next, items) )
    | "TodoRepo.setDone", Val.List [ Val.Nat id; Val.Bool d ] ->
      (match find_id id items with
       | Some (title, _) ->
         Some (ok (Val.Some (todo id title d)), (next, set_id id d items))
       | None -> Some (ok Val.None, (next, items)))
    | "TodoRepo.delete", Val.Nat id ->
      Some (ok (Val.Bool (has_id id items)), (next, drop_id id items))
    | _ -> None
  ;;
end

(* ---------------------------------------------------------------------- record *)

(* A typed host written in OCaml as a value of the lowered record: the repository as four
   functions over native `todo` records and the lane's state. It builds no value of the wire. *)
let record : lane_state Todo_gen.host =
  { Todo_gen.insert =
      (fun title (next, items) ->
        Ok (todo next title false), (Z.succ next, items @ [ next, (title, false) ]))
  ; all =
      (fun () (next, items) ->
        Ok (List.map (fun (id, (title, d)) -> todo id title d) items), (next, items))
  ; set_done =
      (fun (id, d) (next, items) ->
        match find_id id items with
        | Some (title, _) -> Ok (Some (todo id title d)), (next, set_id id d items)
        | None -> Ok None, (next, items))
  ; delete = (fun id (next, items) -> Ok (has_id id items), (next, drop_id id items))
  }
;;

(* The same host, whose insert fails with the rows' error. *)
let broken : lane_state Todo_gen.host =
  { record with
    Todo_gen.insert =
      (fun _ state -> Error (Todo_gen.SqlTag_SqlError, "disk full"), state)
  }
;;

(* ------------------------------------------------------------------------ Core *)

(* todo_core.ml behind REPO: its own types, converted at the boundary. Its ids are the host's
   ints (rocq-of-ocaml reads the file alone, with no library); each is the lane's natural
   exactly, and the lane's ids are small. *)
module Core : REPO with type t = Todo_core.t = struct
  type t = Todo_core.t

  let todo (x : Todo_core.todo) : Todo_gen.todo = todo (Z.of_int x.id) x.title x.done_
  let error (Todo_core.Sql_error message) : sql_error = Todo_gen.SqlTag_SqlError, message
  let answer f (r, s) = Result.map_error error (Result.map f r), s
  let insert title s = answer todo (Todo_core.insert title s)
  let all () s = answer (List.map todo) (Todo_core.all () s)

  let set_done (id, d) s =
    answer (Option.map todo) (Todo_core.set_done (Z.to_int id, d) s)
  ;;

  let delete id s = answer Fun.id (Todo_core.delete (Z.to_int id) s)
end

let core_of_lane ((next, items) : lane_state) : Todo_core.t =
  { next = Z.to_int next
  ; items =
      List.map
        (fun (id, (title, done_)) -> { Todo_core.id = Z.to_int id; title; done_ })
        items
  }
;;

let lane_of_core (s : Todo_core.t) : lane_state =
  ( Z.of_int s.next
  , List.map (fun (x : Todo_core.todo) -> Z.of_int x.id, (x.title, x.done_)) s.items )
;;

(* ----------------------------------------------------------------------- Table *)

(* An imperative repository: a hash table from id to title and flag, and the next id. `fault` is
   called with the method's name before the method reads or writes anything; it may raise, as a
   disk or a network does. The state the record threads is the handle itself. *)
module Table : sig
  include REPO

  val create : ?fault:(string -> unit) -> lane_state -> t
  val snapshot : t -> lane_state
end = struct
  (* The ids are naturals, so the table hashes and compares them as Zarith does (rule 7). *)
  module Ids = Hashtbl.Make (struct
      type t = Z.t

      let equal = Z.equal
      let hash = Z.hash
    end)

  type t =
    { mutable next : Z.t
    ; rows : (string * bool) Ids.t
    ; fault : string -> unit
    }

  let create ?(fault = fun _ -> ()) ((next, items) : lane_state) : t =
    let rows = Ids.create 16 in
    List.iter (fun (id, entry) -> Ids.replace rows id entry) items;
    { next; rows; fault }
  ;;

  let sorted (h : t) : (Z.t * (string * bool)) list =
    List.sort
      (fun (a, _) (b, _) -> Z.compare a b)
      (Ids.fold (fun k v acc -> (k, v) :: acc) h.rows [])
  ;;

  let snapshot (h : t) : lane_state = h.next, sorted h

  let insert title h =
    h.fault "insert";
    let id = h.next in
    Ids.replace h.rows id (title, false);
    h.next <- Z.succ id;
    Ok (todo id title false), h
  ;;

  let all () h =
    h.fault "all";
    Ok (List.map (fun (id, (title, d)) -> todo id title d) (sorted h)), h
  ;;

  let set_done (id, d) h =
    h.fault "set_done";
    match Ids.find_opt h.rows id with
    | None -> Ok None, h
    | Some (title, _) ->
      Ids.replace h.rows id (title, d);
      Ok (Some (todo id title d)), h
  ;;

  let delete id h =
    h.fault "delete";
    let present = Ids.mem h.rows id in
    Ids.remove h.rows id;
    Ok present, h
  ;;
end
