(* e4_snapshot.ml — the snapshot text, parsed.

   What it is: a parser for `Bridge.snapshot` (the human-readable dump of a session), used
   as the oracle for `E4_bridge`'s structured projections (B5) and as the fallback a host
   without the structured exports would read. Pure string work.
   Depends on: E4_bridge (the `fiber` record only).

   Properties:
     S1  `parse` reads exactly the fields `Bridge.snapshot` writes: name, fiber count,
         armed list (in order), finished, stuck, trace length, one fiber per `fiber` line
         and one event per `·` line. [tested: bridge-snapshot-agrees]
     S2  `parse` is total on the snapshot grammar and raises `Invalid_argument` naming the
         line on anything else. [by construction] *)

type t = {
  name : string;
  fiber_count : int;
  armed : int list;
  finished : bool;
  stuck : bool;
  trace_len : int;
  fibers : E4_bridge.fiber list;
  events : string list;
}

(* Index of [sub] in [s] at or after [from]. *)
let find_sub s sub from =
  let n = String.length s and m = String.length sub in
  let rec go i =
    if i + m > n then None else if String.sub s i m = sub then Some i else go (i + 1)
  in
  go from

(* The value of `key=` in [line], up to the next space or the end. *)
let field line key =
  match find_sub line (key ^ "=") 0 with
  | None -> invalid_arg (Printf.sprintf "E4_snapshot: no %s in %S" key line)
  | Some i ->
      let start = i + String.length key + 1 in
      let stop = match String.index_from_opt line start ' ' with Some j -> j | None -> String.length line in
      String.sub line start (stop - start)

let bool_field line key =
  match field line key with
  | "true" -> true
  | "false" -> false
  | v -> invalid_arg (Printf.sprintf "E4_snapshot: %s=%s in %S" key v line)

let parse_header line =
  let name =
    match find_sub line "machine " 0, String.index_opt line ':' with
    | Some 0, Some colon -> String.sub line 8 (colon - 8)
    | _ -> invalid_arg ("E4_snapshot: header " ^ line)
  in
  let armed =
    match find_sub line "armed=[" 0 with
    | None -> invalid_arg ("E4_snapshot: no armed in " ^ line)
    | Some i -> (
        let start = i + 7 in
        match String.index_from_opt line start ']' with
        | None -> invalid_arg ("E4_snapshot: unterminated armed in " ^ line)
        | Some j ->
            let inner = String.trim (String.sub line start (j - start)) in
            if inner = "" then []
            else List.map (fun s -> int_of_string (String.trim s)) (String.split_on_char ',' inner))
  in
  ( name,
    int_of_string (field line "fibers"),
    armed,
    bool_field line "finished",
    bool_field line "stuck",
    int_of_string (field line "trace") )

(* `  fiber <id>: live|exit=success(<tag>)|exit=failure running=… parked=-|token=<n> …` *)
let parse_fiber line : E4_bridge.fiber =
  let rest =
    match E4_bridge.after_prefix ~prefix:"  fiber " line with
    | Some r -> r
    | None -> invalid_arg ("E4_snapshot: fiber line " ^ line)
  in
  let colon = String.index rest ':' in
  let id = int_of_string (String.sub rest 0 colon) in
  let body = String.sub rest (colon + 2) (String.length rest - colon - 2) in
  let exit : E4_bridge.exit option =
    match E4_bridge.after_prefix ~prefix:"exit=success(" body with
    | Some r -> Some (E4_bridge.Success (String.sub r 0 (String.index r ')')))
    | None ->
        if E4_bridge.after_prefix ~prefix:"exit=failure" body <> None then Some E4_bridge.Failure
        else if E4_bridge.after_prefix ~prefix:"live" body <> None then None
        else invalid_arg ("E4_snapshot: fiber exit in " ^ line)
  in
  let parked_token =
    match field body "parked" with
    | "-" -> None
    | p -> (
        match E4_bridge.after_prefix ~prefix:"token=" p with
        | Some n -> Some (int_of_string n)
        | None -> invalid_arg ("E4_snapshot: parked in " ^ line))
  in
  { E4_bridge.id; live = (exit = None); parked_token; exit }

let event_prefix = "  \xc2\xb7 " (* "  · " *)

let parse text =
  match String.split_on_char '\n' text with
  | [] -> invalid_arg "E4_snapshot: empty"
  | header :: rest ->
      let name, fiber_count, armed, finished, stuck, trace_len = parse_header header in
      let fibers, events =
        List.fold_left
          (fun (fibers, events) line ->
            if E4_bridge.after_prefix ~prefix:"  fiber " line <> None then
              (parse_fiber line :: fibers, events)
            else
              match E4_bridge.after_prefix ~prefix:event_prefix line with
              | Some row -> (fibers, row :: events)
              | None -> (fibers, events))
          ([], []) rest
      in
      { name; fiber_count; armed; finished; stuck; trace_len; fibers = List.rev fibers; events = List.rev events }
