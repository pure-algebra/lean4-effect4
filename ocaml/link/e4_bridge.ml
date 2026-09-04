(* e4_bridge.ml — the typed OCaml face of the Lean ABI.

   What it is: `Bridge.lean` (a program table and a `RunMachine` held as an opaque
   `Session`) seen through `e4_stubs.c`. A session is an abstract value, every step is a
   new value, and the projections are read off the value as strings and parsed here.
   Depends on: e4_stubs.c only. Nothing here knows how the machine works.

   Properties:
     B1  A session is an abstract, domain-local value: nothing in this interface copies or
         compares it, and the only way to observe it is a projection to strings and ints.
         [by construction]
     B2  Values, not state. `step` and `drive` return a new session and leave their
         argument usable and unchanged until it is released. [by construction (Lean values
         are immutable); tested: bridge-values]
     B3  The wire grammar is total on `decision`: `of_wire (to_wire d) = Some d`, and every
         string `to_wire` produces is one `Bridge.parseDecision` accepts, so a step never
         silently applies the identity. [tested: bridge-wire, bridge-answer]
     B4  A released session raises `Invalid_argument` on use and never touches freed
         memory; `release` is idempotent. [tested: bridge-release]
     B5  The projections agree with the snapshot text (`E4_snapshot` is the oracle):
         armed, finished, trace_len, fibers, events. [tested: bridge-snapshot-agrees]
     B6  `events ~cursor` returns exactly the trace rows at index >= cursor, in order, and
         `trace_len` is the cursor after them. [tested: bridge-events-cursor]
     B7  The bytes path answers a refusal, not a machine. Lean's `e4_load_hex` is total: it
         answers a session for every string, named `bytes` when the bytes decoded exactly
         and typed, and `!refused:decode` / `!refused:ill-typed` otherwise — and a refused
         session carries p42's machine, so handing it out would run something other than
         the bytes asked for. `load_hex` therefore has a `result` type: it reads the name,
         and on a refusal releases the session and answers `Error refusal`, so bytes the
         decoder refuses can never be stepped. `program_hex` answers `None` for a name the
         table lacks (Lean's ""); `name` is the loaded program's name and is preserved by
         `step` / `drive`. [tested: bridge-name, bridge-hex-roundtrip, bridge-hex-refuses,
         bridge-hex-ill-typed, bridge-hex-tamper] *)

type t

type decision =
  | Evaluate
  | Flush
  | Fire of int
  | Evaluate_fiber of int
  | Answer of { fiber : int; token : int; value : int }

type exit = Success of string | Failure

type fiber = { id : int; live : bool; parked_token : int option; exit : exit option }

(* Why `e4_load_hex` would not run a byte string (B7): the reason of its `!refused:<reason>`
   session name. `Other` is the total case — a reason a later Bridge.lean may add. *)
type refusal = Decode | Ill_typed | Other of string

(* ---- the externals (e4_stubs.c) ---- *)

external init : unit -> unit = "caml_e4_init"
external thread_init : unit -> unit = "caml_e4_thread_init"
external thread_finalize : unit -> unit = "caml_e4_thread_finalize"
external program_names_raw : unit -> string = "caml_e4_program_names"
external load_raw : string -> int -> t = "caml_e4_load"
external step_raw : t -> string -> int -> t = "caml_e4_step"
external drive_raw : t -> int -> t = "caml_e4_drive"
external snapshot : t -> string = "caml_e4_snapshot"
external armed_raw : t -> string = "caml_e4_armed"
external finished : t -> bool = "caml_e4_finished"
external fibers_raw : t -> string = "caml_e4_fibers"
external trace_len : t -> int = "caml_e4_trace_len"
external events_raw : t -> int -> string = "caml_e4_events"
external name : t -> string = "caml_e4_name"
external load_hex_raw : string -> int -> t = "caml_e4_load_hex"
external program_hex_raw : string -> string = "caml_e4_program_hex"
external release : t -> unit = "caml_e4_release"
external is_released : t -> bool = "caml_e4_is_released"

(* ---- the wire grammar (B3) ---- *)

let to_wire = function
  | Evaluate -> "evaluate"
  | Flush -> "flush"
  | Fire owner -> "fire:" ^ string_of_int owner
  | Evaluate_fiber fiber -> "evaluate:" ^ string_of_int fiber
  | Answer { fiber; token; value } -> Printf.sprintf "answer:%d:%d:%d" fiber token value

(* Digits only, as Lean's `String.toNat?`: no sign, no radix prefix, no underscore. *)
let nat_of_string s =
  if s <> "" && String.for_all (fun c -> c >= '0' && c <= '9') s then int_of_string_opt s
  else None

let after_prefix ~prefix s =
  let n = String.length prefix in
  if String.length s >= n && String.sub s 0 n = prefix then
    Some (String.sub s n (String.length s - n))
  else None

let of_wire s =
  match s with
  | "evaluate" -> Some Evaluate
  | "flush" -> Some Flush
  | _ -> (
      match after_prefix ~prefix:"fire:" s with
      | Some rest -> Option.map (fun owner -> Fire owner) (nat_of_string rest)
      | None -> (
          match after_prefix ~prefix:"evaluate:" s with
          | Some rest -> Option.map (fun fiber -> Evaluate_fiber fiber) (nat_of_string rest)
          | None -> (
              match after_prefix ~prefix:"answer:" s with
              | Some rest -> (
                  match List.map nat_of_string (String.split_on_char ':' rest) with
                  | [ Some fiber; Some token; Some value ] -> Some (Answer { fiber; token; value })
                  | _ -> None)
              | None -> None)))

(* ---- the calls ---- *)

let program_names () =
  List.filter (fun s -> s <> "") (String.split_on_char '\n' (program_names_raw ()))

let load ~program ~fuel = load_raw program fuel
let step t ~fuel decision = step_raw t (to_wire decision) fuel
let drive t ~fuel = drive_raw t fuel

(* ---- the bytes path (B7): hex out, hex in, refusals by name ---- *)

(* The names `Bridge.loadHex` writes: the program it decoded, or why it would not. *)
let bytes_session_name = "bytes"
let refused_prefix = "!refused:"

let refusal_of_reason = function
  | "decode" -> Decode
  | "ill-typed" -> Ill_typed
  | reason -> Other reason

let pp_refusal = function
  | Decode -> "decode"
  | Ill_typed -> "ill-typed"
  | Other reason -> reason

(* The canonical bytes of a table program as hex; `None` when the table has no such name
   (the Lean side answers ""). Lowercase hex, two digits per byte, no separator. *)
let program_hex program = match program_hex_raw program with "" -> None | hex -> Some hex

(* A machine from a program's canonical bytes. `Error` for bytes the Lean decoder refuses
   or the typing check rejects: the refused session (p42's machine under a `!refused:` name)
   is released here and never handed out, so a caller cannot step a repaired program (B7). *)
let load_hex ~hex ~fuel =
  let s = load_hex_raw hex fuel in
  match after_prefix ~prefix:refused_prefix (name s) with
  | Some reason ->
      release s;
      Error (refusal_of_reason reason)
  | None -> Ok s

let armed t =
  match armed_raw t with
  | "" -> []
  | s -> List.map int_of_string (String.split_on_char ',' s)

let events t ~cursor =
  match events_raw t cursor with "" -> [] | s -> String.split_on_char '\n' s

(* ---- the fiber lines: `id<TAB>live|exited<TAB>token|-<TAB>success:<tag>|failure|-` ---- *)

let exit_of_field = function
  | "-" -> None
  | "failure" -> Some Failure
  | s -> (
      match after_prefix ~prefix:"success:" s with
      | Some tag -> Some (Success tag)
      | None -> invalid_arg ("E4_bridge: exit field " ^ s))

let parse_fiber_line line =
  match String.split_on_char '\t' line with
  | [ id; state; token; exit ] ->
      {
        id = int_of_string id;
        live = state = "live";
        parked_token = (if token = "-" then None else Some (int_of_string token));
        exit = exit_of_field exit;
      }
  | _ -> invalid_arg ("E4_bridge: fiber line " ^ line)

let parse_fibers s =
  if s = "" then [] else List.map parse_fiber_line (String.split_on_char '\n' s)

let fibers t = parse_fibers (fibers_raw t)

(* The natural number in a `nat <n>` value tag. *)
let nat_of_tag tag =
  match String.split_on_char ' ' tag with [ "nat"; n ] -> nat_of_string n | _ -> None

let pp_exit = function
  | None -> "-"
  | Some Failure -> "failure"
  | Some (Success tag) -> "success:" ^ tag

let pp_fiber f =
  Printf.sprintf "fiber %d %s parked=%s exit=%s" f.id
    (if f.live then "live" else "exited")
    (match f.parked_token with None -> "-" | Some t -> "token=" ^ string_of_int t)
    (pp_exit f.exit)
