(* todo_fixture.ml -- the reader of the to-do lane's fixture, todo-host.txt.

   What it is: the blocks Lean writes for each request of one script
   (Test/Dogfood/Scenario/Todo/HostLane.lean, written by write.lean beside this file): the built
   program, its rows, its type, its row names and the repository state before it, as canonical
   bytes, then Lean's results. The test and the bench read the fixture through it.
   Depends on: Todo_gen (GENERATED), Eff_wire, Eff_val, E4_hex.

   Properties:
   F1  Each input crosses as its canonical bytes and is read exactly: Eff_wire's program, row
       and type readers, and Eff_val for values. A block that does not read, and a line this
       reader does not know, raise Failure, never a skip.                  by construction *)

open Eff_types

(* One request's block of the fixture. *)
type request = {
  entry : string;
  program : string;
  rows : string list;
  typed : string;
  names : string;
  state : string;
  result : string;
  forgetful : string;
  broken : string;
  admits : string;
  answer : string;
}

let empty entry =
  { entry; program = ""; rows = []; typed = ""; names = ""; state = ""; result = ""; forgetful = "";
    broken = ""; admits = ""; answer = "" }

(* The fixture's blocks, in order. A line this reader does not know is a failure. *)
let read_fixture (path : string) : request list =
  let ic = open_in path in
  let rec go acc cur =
    match input_line ic with
    | exception End_of_file -> List.rev (match cur with Some r -> r :: acc | None -> acc)
    | line when line = "" || line.[0] = '#' -> go acc cur
    | line ->
      (match String.index_opt line ' ', cur with
       | None, _ -> failwith ("fixture: a line with no value: " ^ line)
       | Some i, _ ->
         let key = String.sub line 0 i and value = String.sub line (i + 1) (String.length line - i - 1) in
         (match key, cur with
          | "request", _ -> go (match cur with Some r -> r :: acc | None -> acc) (Some (empty value))
          | "program", Some r -> go acc (Some { r with program = value })
          | "row", Some r -> go acc (Some { r with rows = r.rows @ [ value ] })
          | "typed", Some r -> go acc (Some { r with typed = value })
          | "names", Some r -> go acc (Some { r with names = value })
          | "state", Some r -> go acc (Some { r with state = value })
          | "result", Some r -> go acc (Some { r with result = value })
          | "forgetful", Some r -> go acc (Some { r with forgetful = value })
          | "broken", Some r -> go acc (Some { r with broken = value })
          | "admits", Some r -> go acc (Some { r with admits = value })
          | "answer", Some r -> go acc (Some { r with answer = value })
          | _ -> failwith ("fixture: an unknown line: " ^ key)))
  in
  let requests = go [] None in
  close_in ic;
  requests

let bytes_of_hex (what : string) (hex : string) : string =
  match E4_hex.to_bytes hex with
  | Some b -> b
  | None -> failwith (Printf.sprintf "fixture: %s is not hexadecimal" what)

let exactly (what : string) (decode : string -> 'a option) (hex : string) : 'a =
  match decode (bytes_of_hex what hex) with
  | Some x -> x
  | None -> failwith (Printf.sprintf "fixture: %s does not read exactly" what)

(* The repository state: the next id, then each to-do's id, title and flag (`repoVal`). *)
let repo_of (v : val_) : int * (int * (string * bool)) list =
  match v with
  | Val_list [ Val_nat next; Val_list items ] ->
    ( next,
      List.map
        (function
          | Val_list [ Val_nat id; Val_str title; Val_bool isDone ] -> (id, (title, isDone))
          | _ -> failwith "fixture: a stored to-do is not an id, a title and a flag")
        items )
  | _ -> failwith "fixture: the state is not a next id and a list"

(* The row names: each spelling and its position (`namesVal`). *)
let names_of (v : val_) : (string * int) list =
  match v with
  | Val_list xs ->
    List.map
      (function
        | Val_list [ Val_str name; Val_nat i ] -> (name, i)
        | _ -> failwith "fixture: a row name is not a spelling and a position")
      xs
  | _ -> failwith "fixture: the row names are not a list"

let built_of (r : request) : Todo_gen.built =
  { Todo_gen.app =
      { Todo_gen.rows = List.map (exactly "a row" Eff_wire.decode_row_exact) r.rows;
        services = [];
        types = [] };
    program = exactly "the program" Eff_wire.decode_program_exact r.program;
    admitted = exactly "the type" Eff_wire.decode_eff_ty_exact r.typed;
    row_names = names_of (exactly "the row names" Eff_val.decode_exact r.names) }

let hex_of (v : val_) : string = E4_hex.of_bytes (Eff_val.to_bytes v)
