(* test_scenarios.ml -- the machine clause of the dogfood scenarios, on the generated engine.

   What it is: decisions row 254.  A scenario of Test/Dogfood/Scenario/ compares one named
   observation.  The generated engine holds no session, so the observation lands as two
   clauses: the session clause, checked in Lean, and the machine clause, checked here.  The
   machine clause is `Effect4.Run.machineView`: the root's exit, the cells, the calls
   the machine waits on, the armed owners, the runnable fibers and the timers.

   The fixtures are the *.txt files beside this one, written by Lean from the programs
   `Api.Author.build` admits (Test/Dogfood/Scenario/Lowered.lean; the writer is write.lean,
   beside this file).  A run of a fixture holds the program's canonical bytes, each row's
   canonical bytes, the budgets, and the machine tape: each decision that moved Lean's session
   machine, with the view after it.

   The adapter lives here and changes no production interface.  `E4_engine.INSTANCE` takes no
   row table: api_engine_inst.ml and api_engine_ref.ml fix it to the empty list.  This test
   calls the generated `api_replay` itself, with the program, the command fuel, the tape, no
   preloaded answers, the row table and the compile fuel.

   Properties:
   S1  The row table is read from its wire bytes (`Eff_wire.decode_row_exact`) and converted
       into the instance's row type by `of_row`.  The conversion is behind `E4_program.pin`,
       has no catch-all arm, and each sum it maps is checked against the source's own ordinal
       (`Eff_types.ctor_index_*`) by an independently written engine-side table.
                                                                 by construction; tested
   S2  At every position of every run, on BOTH instances (Fast and Ref), the view of
       `api_replay` on the tape's prefix is the view Lean wrote for its session machine.
                                                                 tested (finite runs)
   S3  A value crosses as its canonical bytes: `decode_val` reads Lean's `Val.encode`, and
       `emit_val` writes the engine's value back in the same frames.  For every value a
       fixture's tape carries, `emit_val (decode_val bytes) = bytes`.       tested
   S4  The table, and the red controls.  A fixture's line `table differs` or `table same`
       is one observed difference, in one projection: whether Lean's raw replay with the
       empty table (what the production wrappers supply) shows another machine view
       (`machineViewOf`) at some position than its replay with the built table.  The engine
       must show the same answer, in both directions.  `table same` does NOT say that the
       replay reads no row: `prepareExternalAnswer` (src/Effect4/Program/Compile.lean)
       consults a nonempty table for each successful reply, and an answer with no handle can
       come out the same.  A tape cut before its last decision that moves the view ends at
       another view than the full tape's.  The cut is Lean's: the last position at which two
       neighbouring view lines of the fixture differ.  The engine's own views choose nothing.
       A run of two or more decisions in which no decision moves the view fails: it is not
       skipped.  The decisions after the cut move nothing, and S2 compares each of their
       positions, so they get no second comparison.  A row whose bytes are cut is refused,
       never repaired.                                                     tested
   S5  A run whose fixture ends at a frontier is compared up to that position only, and its
       unread rows are reported: a frontier is never read as a reply application.
                                                                 by construction

   What it does not establish: the session clause on the engine (the engine has no stored
   reply, no retired call, no consumed call), any schedule but the fixtures', or the host run.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine *)

open Effect4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ================================================================ the fixture's text *)

type run = {
  name : string;
  fuel : int;
  compile : int;
  program : string;  (* canonical bytes *)
  rows : string list;  (* canonical bytes, in table order *)
  observed_table_difference : bool;
      (* whether Lean's raw replay with the empty table shows another machine view on this run *)
  first : string;  (* the view line of the loaded machine *)
  steps : (string list * string) list;  (* a decision's words, and the view line after it *)
  ending : string list;  (* ["tape"], or ["frontier"; rows left] *)
}

let words (line : string) : string list =
  List.filter (fun w -> w <> "") (String.split_on_char ' ' line)

let bytes_of_hex (what : string) (hex : string) : string =
  match E4_hex.to_bytes hex with
  | Some b -> b
  | None -> failwith (Printf.sprintf "fixture: %s is not hexadecimal" what)

(* One fixture file into its runs.  Any line this reader does not know is a failure: a fixture
   is never read loosely. *)
let read_fixture (path : string) : run list =
  let ic = open_in path in
  let rec lines acc =
    match input_line ic with
    | line -> lines (line :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  let rec runs acc = function
    | [] -> List.rev acc
    | line :: rest when line = "" || line.[0] = '#' -> runs acc rest
    | line :: rest ->
      (match words line with
       | [ "run"; name ] ->
         let run, rest =
           body
             { name; fuel = 0; compile = 0; program = ""; rows = [];
               observed_table_difference = false; first = ""; steps = []; ending = [] }
             rest
         in
         runs (run :: acc) rest
       | _ -> failwith (Printf.sprintf "fixture %s: expected `run`, read %S" path line))
  and body r = function
    | [] -> failwith (Printf.sprintf "fixture %s: run %s has no `end`" path r.name)
    | line :: rest ->
      (match words line with
       | [ "fuel"; n ] -> body { r with fuel = int_of_string n } rest
       | [ "compile"; n ] -> body { r with compile = int_of_string n } rest
       | [ "program"; hex ] -> body { r with program = bytes_of_hex "the program" hex } rest
       | [ "row"; hex ] -> body { r with rows = r.rows @ [ bytes_of_hex "a row" hex ] } rest
       | [ "table"; "differs" ] -> body { r with observed_table_difference = true } rest
       | [ "table"; "same" ] -> body { r with observed_table_difference = false } rest
       | "view" :: _ when r.first = "" -> body { r with first = line } rest
       | "step" :: decision ->
         (match rest with
          | view :: rest' when (match words view with "view" :: _ -> true | _ -> false) ->
            body { r with steps = r.steps @ [ (decision, view) ] } rest'
          | _ -> failwith (Printf.sprintf "fixture %s: a step of %s has no view" path r.name))
       | "end" :: ending -> ({ r with ending }, rest)
       | _ -> failwith (Printf.sprintf "fixture %s: run %s, unknown line %S" path r.name line))
  in
  runs [] (lines [])

(* ================================================================ the generated engine *)

(* What the adapter reads of a generated instance beyond `E4_engine.INSTANCE`: the replay with
   its table, and three declarations of the generated type group.  `ocamlopt` checks each
   against both instances, so a field or a constructor that moves in api_engine.ml is a build
   error here. *)
module type GEN = sig
  include E4_engine.INSTANCE

  type await = { fiber : fiber_id; token : int; op : native_op; request : val_ }
  type key = { fiber : fiber_id; token : int }

  type frontier_reason =
    | FrontierReason_commandFuel
    | FrontierReason_compileFuel of fiber_id
    | FrontierReason_awaitHost of key
    | FrontierReason_awaitTimer of fiber_id * E4_clock.t
    | FrontierReason_awaitDecision

  type inspection = { outcome : outcome; machine : machine; reasons : frontier_reason list }

  val api_replay :
    program ->
    int ->
    api_decision list ->
    (val_, err, defect, fiber_id, unit) completion list ->
    row list ->
    int ->
    inspection

  val reify_exit_val : (val_, err, defect, fiber_id, unit) exit_ -> val_
  val program_awaits : machine -> await list
end

(* The one reading that must name a carrier: the timer store's waiters. *)
module type TIMERS = sig
  type machine

  val timers : machine -> (int * E4_clock.t) list
end

module Adapter (A : GEN) (T : TIMERS with type machine = A.machine) = struct
  module P = E4_program.Make (A)

  (* ------------------------------------------------------------ S1: the row table *)

  let rec of_ty : Eff_types.ty -> A.ty = function
    | Eff_types.Ty_never -> A.Ty_never
    | Eff_types.Ty_unit -> A.Ty_unit
    | Eff_types.Ty_nat -> A.Ty_nat
    | Eff_types.Ty_int -> A.Ty_int
    | Eff_types.Ty_string -> A.Ty_string
    | Eff_types.Ty_bool -> A.Ty_bool
    | Eff_types.Ty_handle h -> A.Ty_handle h
    | Eff_types.Ty_option a -> A.Ty_option (of_ty a)
    | Eff_types.Ty_list a -> A.Ty_list (of_ty a)
    | Eff_types.Ty_prod (a, b) -> A.Ty_prod (of_ty a, of_ty b)
    | Eff_types.Ty_except (a, b) -> A.Ty_except (of_ty a, of_ty b)
    | Eff_types.Ty_exitOf (a, b) -> A.Ty_exitOf (of_ty a, of_ty b)
    | Eff_types.Ty_causeOf a -> A.Ty_causeOf (of_ty a)
    | Eff_types.Ty_fiberOf (a, b) -> A.Ty_fiberOf (of_ty a, of_ty b)
    | Eff_types.Ty_union (a, b) -> A.Ty_union (of_ty a, of_ty b)
    | Eff_types.Ty_lit s -> A.Ty_lit s
    | Eff_types.Ty_refOf a -> A.Ty_refOf (of_ty a)
    | Eff_types.Ty_deferredOf (a, b) -> A.Ty_deferredOf (of_ty a, of_ty b)
    | Eff_types.Ty_var i -> A.Ty_var i
    | Eff_types.Ty_unknown -> A.Ty_unknown
    | Eff_types.Ty_record fs -> A.Ty_record (List.map (fun (n, (o, t)) -> (n, (o, of_ty t))) fs)
    | Eff_types.Ty_map (k, v) -> A.Ty_map (of_ty k, of_ty v)
    | Eff_types.Ty_tuple ts -> A.Ty_tuple (List.map of_ty ts)
    | Eff_types.Ty_app (n, ts) -> A.Ty_app (n, List.map of_ty ts)
    | Eff_types.Ty_null -> A.Ty_null
    | Eff_types.Ty_undefined -> A.Ty_undefined
    | Eff_types.Ty_number -> A.Ty_number
    | Eff_types.Ty_bytes -> A.Ty_bytes

  (* The engine side of the ordinal check, written apart from `of_ty`: the position of each
     constructor in api_engine.ml's declaration (e4_program_layout.ml mirrors it). *)
  let index_ty : A.ty -> int = function
    | A.Ty_never -> 0
    | A.Ty_unit -> 1
    | A.Ty_nat -> 2
    | A.Ty_int -> 3
    | A.Ty_string -> 4
    | A.Ty_bool -> 5
    | A.Ty_handle _ -> 6
    | A.Ty_option _ -> 7
    | A.Ty_list _ -> 8
    | A.Ty_prod _ -> 9
    | A.Ty_except _ -> 10
    | A.Ty_exitOf _ -> 11
    | A.Ty_causeOf _ -> 12
    | A.Ty_fiberOf _ -> 13
    | A.Ty_union _ -> 14
    | A.Ty_lit _ -> 15
    | A.Ty_refOf _ -> 16
    | A.Ty_deferredOf _ -> 17
    | A.Ty_var _ -> 18
    | A.Ty_unknown -> 19
    | A.Ty_record _ -> 20
    | A.Ty_map _ -> 21
    | A.Ty_tuple _ -> 22
    | A.Ty_app _ -> 23
    | A.Ty_null -> 24
    | A.Ty_undefined -> 25
    | A.Ty_number -> 26
    | A.Ty_bytes -> 27

  let of_row_shape : Eff_types.row_shape -> A.row_shape = function
    | Eff_types.Row_shape_call -> A.RowShape_call
    | Eff_types.Row_shape_value -> A.RowShape_value
    | Eff_types.Row_shape_tupleCall -> A.RowShape_tupleCall
    | Eff_types.Row_shape_method -> A.RowShape_method

  let index_row_shape : A.row_shape -> int = function
    | A.RowShape_call -> 0
    | A.RowShape_value -> 1
    | A.RowShape_tupleCall -> 2
    | A.RowShape_method -> 3

  let of_row_kind : Eff_types.row_kind -> A.row_kind = function
    | Eff_types.Row_kind_sync -> A.RowKind_sync
    | Eff_types.Row_kind_async -> A.RowKind_async
    | Eff_types.Row_kind_program -> A.RowKind_program

  let index_row_kind : A.row_kind -> int = function
    | A.RowKind_sync -> 0
    | A.RowKind_async -> 1
    | A.RowKind_program -> 2

  let of_registration : Eff_types.registration -> A.registration = function
    | Eff_types.Registration_deferred -> A.Registration_deferred
    | Eff_types.Registration_external -> A.Registration_external

  let index_registration : A.registration -> int = function
    | A.Registration_deferred -> 0
    | A.Registration_external -> 1

  let of_service_key (k : Eff_types.service_key) : A.service_key =
    { A.name = k.Eff_types.service_key_name.Eff_types.service_name_value;
      service = k.Eff_types.service_key_service.Eff_types.service_type_code_value }

  (* The checked conversion of one row.  `Error` names the column whose ordinal the engine
     side disagrees on; the pin refuses the whole table when the two alphabets disagree. *)
  let of_row (r : Eff_types.row) : (A.row, string) result =
    let request = of_ty r.Eff_types.row_request in
    let answer = of_ty r.Eff_types.row_answer in
    let error = of_ty r.Eff_types.row_error in
    let shape = of_row_shape r.Eff_types.row_shape in
    let kind = of_row_kind r.Eff_types.row_kind in
    let registration = of_registration r.Eff_types.row_registration in
    let same what a b = if a = b then Ok () else Error (r.Eff_types.row_spelling ^ ": " ^ what) in
    let ( let* ) = Result.bind in
    let* () = Result.map_error (fun m -> "the ordinal pin: " ^ m) (E4_program.pin ()) in
    let* () = same "request" (Eff_types.ctor_index_ty r.Eff_types.row_request) (index_ty request) in
    let* () = same "answer" (Eff_types.ctor_index_ty r.Eff_types.row_answer) (index_ty answer) in
    let* () = same "error" (Eff_types.ctor_index_ty r.Eff_types.row_error) (index_ty error) in
    let* () =
      same "shape" (Eff_types.ctor_index_row_shape r.Eff_types.row_shape) (index_row_shape shape)
    in
    let* () =
      same "kind" (Eff_types.ctor_index_row_kind r.Eff_types.row_kind) (index_row_kind kind)
    in
    let* () =
      same "registration"
        (Eff_types.ctor_index_registration r.Eff_types.row_registration)
        (index_registration registration)
    in
    Ok
      { A.name = r.Eff_types.row_name;
        spelling = r.Eff_types.row_spelling;
        shape;
        trailing = r.Eff_types.row_trailing;
        kind;
        request;
        answer;
        error;
        requires = List.map of_service_key r.Eff_types.row_requires;
        cite = r.Eff_types.row_cite;
        type_args = r.Eff_types.row_typeArgs;
        registration }

  (* The table from its wire bytes.  A row that is not exactly one row is refused. *)
  let table_of (rows : string list) : (A.row list, string) result =
    let rec go acc = function
      | [] -> Ok (List.rev acc)
      | bytes :: rest ->
        (match Eff_wire.decode_row_exact bytes with
         | None -> Error "a row's bytes are not exactly one row"
         | Some r -> (match of_row r with Ok row -> go (row :: acc) rest | Error m -> Error m))
    in
    go [] rows

  (* ------------------------------------------------------------ S3: values as bytes *)

  let string_of_codes (codes : int list) : string =
    String.init (List.length codes) (fun i -> Char.chr (List.nth codes i))

  let be64 (n : int) : string =
    let b = Buffer.create 8 in
    Eff_frame.emit_be64 b n;
    Buffer.contents b

  (* The frames of src/Effect4/Store/Carrier/Val.lean, `Val.encode`. *)
  let rec emit_val (b : Buffer.t) (v : A.val_) : unit =
    match v with
    | A.Val_unit -> Eff_frame.emit_unit b ()
    | A.Val_bool x -> Eff_frame.emit_bool b x
    | A.Val_nat n -> Eff_frame.emit_nat b n
    | A.Val_str s -> Eff_frame.emit_string b s
    | A.Val_bytes codes -> Eff_frame.emit_frame b Eff_frame.tag_bytes (string_of_codes codes)
    | A.Val_list xs -> Eff_frame.emit_list b emit_val xs
    | A.Val_pair (x, y) -> Eff_frame.emit_pair b emit_val emit_val (x, y)
    | A.Val_none -> Eff_frame.emit_option b emit_val None
    | A.Val_some x -> Eff_frame.emit_option b emit_val (Some x)
    | A.Val_ctor (index, args) -> Eff_frame.emit_ctor b index (fun p -> List.iter (emit_val p) args)
    | A.Val_ref (kind, digest) -> Eff_frame.emit_ref b (kind, string_of_codes digest)
    | A.Val_handle (kind, key) -> Eff_frame.emit_handle b (kind, key)
    | A.Val_negInt n -> Eff_frame.emit_frame b Eff_frame.tag_int (Eff_frame.nat_digits n)
    | A.Val_float bits -> Eff_frame.emit_frame b Eff_frame.tag_float (be64 bits)

  let hex_of_val (v : A.val_) : string = E4_hex.of_bytes (Eff_frame.to_string emit_val v)

  (* The reader of the same frames.  The tape's values are scalars, lists, options, pairs and
     constructor applications; a frame outside those is refused, never guessed. *)
  let rec decode_val : A.val_ Eff_frame.decoder =
   fun s pos limit ->
    match Eff_frame.read_frame s pos limit with
    | None -> None
    | Some (tag, p, e, next) ->
      if tag = Eff_frame.tag_unit then if p = e then Some (A.Val_unit, next) else None
      else if tag = Eff_frame.tag_bool then
        Option.map (fun (x, n) -> (A.Val_bool x, n)) (Eff_frame.decode_bool s pos limit)
      else if tag = Eff_frame.tag_nat then
        Option.map (fun (x, n) -> (A.Val_nat x, n)) (Eff_frame.decode_nat s pos limit)
      else if tag = Eff_frame.tag_string then
        Option.map (fun (x, n) -> (A.Val_str x, n)) (Eff_frame.decode_string s pos limit)
      else if tag = Eff_frame.tag_list then
        Option.map (fun (xs, n) -> (A.Val_list xs, n)) (Eff_frame.decode_list decode_val s pos limit)
      else if tag = Eff_frame.tag_pair then
        Option.map
          (fun ((x, y), n) -> (A.Val_pair (x, y), n))
          (Eff_frame.decode_pair decode_val decode_val s pos limit)
      else if tag = Eff_frame.tag_none || tag = Eff_frame.tag_some then
        Option.map
          (fun (o, n) -> ((match o with None -> A.Val_none | Some x -> A.Val_some x), n))
          (Eff_frame.decode_option decode_val s pos limit)
      else if tag = Eff_frame.tag_ctor then
        match Eff_frame.read_ctor s pos limit with
        | None -> None
        | Some (index, p', e', next') ->
          let rec args p acc =
            if p = e' then Some (List.rev acc)
            else match decode_val s p e' with None -> None | Some (x, p'') -> args p'' (x :: acc)
          in
          Option.map (fun xs -> (A.Val_ctor (index, xs), next')) (args p' [])
      else None

  let val_of_hex (hex : string) : A.val_ =
    match Eff_frame.exact decode_val (bytes_of_hex "a value" hex) with
    | Some v -> v
    | None -> failwith "fixture: a value's bytes are not exactly one value"

  let text_of_word (word : string) : string =
    if String.length word > 0 && word.[0] = 's' then
      bytes_of_hex "a text" (String.sub word 1 (String.length word - 1))
    else failwith "fixture: a text does not start with `s`"

  (* ------------------------------------------------------------ the tape's decisions *)

  let decision_of (ws : string list) : A.api_decision =
    match ws with
    | [ "fire"; f ] -> A.RunDecision_fire (int_of_string f)
    | [ "flush" ] -> A.RunDecision_flush
    | [ "evaluate"; f ] -> A.RunDecision_evaluate (int_of_string f)
    | [ "yield"; f; verdict ] -> A.RunDecision_yieldVerdict (int_of_string f, verdict = "1")
    | [ "answer"; f; token; "ok"; hex ] ->
      A.RunDecision_answerAsync
        (int_of_string f, int_of_string token,
         A.Completion_ofExit (A.Exit_success (val_of_hex hex)))
    | [ "answer"; f; token; "failed"; tag; message ] ->
      A.RunDecision_answerAsync
        (int_of_string f, int_of_string token,
         A.Completion_ofExit
           (A.Exit_failure
              [ A.Reason_fail (A.Err_tagged (text_of_word tag, text_of_word message), []) ]))
    | [ "interrupt"; who; target ] ->
      A.RunDecision_interruptFrom
        ((if who = "-" then None else Some (int_of_string who)), [], int_of_string target)
    | [ "middleware" ] -> A.RunDecision_installMiddleware
    | [ "advance"; millis ] ->
      (match E4_clock.of_decimal millis with
       | Some t -> A.RunDecision_advance t
       | None -> failwith "fixture: a clock step is not a canonical decimal")
    | _ -> failwith ("fixture: unknown decision " ^ String.concat " " ws)

  (* ------------------------------------------------------------ S2: the view *)

  let items (texts : string list) : string = if texts = [] then "-" else String.concat "," texts

  let outcome_word : A.outcome -> string = function
    | A.Outcome_finished -> "finished"
    | A.Outcome_frontier -> "frontier"
    | A.Outcome_stuck _ -> "stuck"

  (* The view line of an inspection: the same seven readings, in the same spelling, as
     `Test.Dogfood.Scenario.Lowered.viewText`. *)
  let view_of (r : A.inspection) : string =
    let m = r.A.machine in
    let fibers = A.fibers m in
    let root =
      match List.assoc_opt 0 fibers with
      | None -> "-"
      | Some f -> (match A.f_exit f with None -> "-" | Some e -> hex_of_val (A.reify_exit_val e))
    in
    let cells = items (List.map hex_of_val (A.refs m)) in
    let awaiting =
      items
        (List.map
           (fun (a : A.await) ->
             Printf.sprintf "%d.%d.%s.%s" a.A.fiber a.A.token
               (match a.A.op with A.NativeOp_external i -> string_of_int i | _ -> "x")
               (hex_of_val a.A.request))
           (A.program_awaits m))
    in
    let queued = items (List.map string_of_int (A.armed_of m)) in
    let runnable =
      items
        (List.filter_map
           (fun (id, f) ->
             if A.f_exit f = None && A.f_parked f = A.Parked_notParked then Some (string_of_int id)
             else None)
           fibers)
    in
    let timers =
      items (List.map (fun (f, at) -> Printf.sprintf "%d@%s" f (E4_clock.to_decimal at)) (T.timers m))
    in
    String.concat " " [ "view"; outcome_word r.A.outcome; root; cells; awaiting; queued; runnable; timers ]

  (* ------------------------------------------------------------ one run *)

  let rec take n = function [] -> [] | x :: xs -> if n = 0 then [] else x :: take (n - 1) xs

  (* The views of `api_replay` on every prefix of a tape, the loaded machine first. *)
  let views (program : A.program) (r : run) (table : A.row list) (tape : A.api_decision list)
    : string list =
    List.init (List.length tape + 1) (fun count ->
        view_of (A.api_replay program r.fuel (take count tape) [] table r.compile))

  (* The positions at which the engine's view is not the fixture's; `-1` for another length. *)
  let differs (expected : string list) (got : string list) : int list =
    if List.length expected <> List.length got then [ -1 ]
    else
      List.filter
        (fun i -> List.nth expected i <> List.nth got i)
        (List.init (List.length got) Fun.id)

  let run_one (r : run) : unit =
    let label what = Printf.sprintf "%s %s: %s" A.name r.name what in
    match P.of_bytes r.program with
    | None -> check (label "the program's bytes are exactly one program") false
    | Some program ->
      (match table_of r.rows with
       | Error m -> check (label ("the row table converts: " ^ m)) false
       | Ok table ->
         let tape = List.map (fun (ws, _) -> decision_of ws) r.steps in
         let expected = r.first :: List.map snd r.steps in
         let got = views program r table tape in
         let bad = differs expected got in
         check
           (label
              (Printf.sprintf "the engine's view is Lean's at each of %d positions"
                 (List.length expected)))
           (bad = []);
         List.iter
           (fun i ->
             if i >= 0 then
               Printf.printf "  position %d\n    Lean   %s\n    engine %s\n" i (List.nth expected i)
                 (List.nth got i))
           bad;
         (* S5: a fixture that ends at a frontier names the rows it left unread. *)
         (match r.ending with
          | [ "tape" ] -> ()
          | [ "frontier"; left ] ->
            Printf.printf "  %s stops at a frontier: %s rows of the journal are not replayed\n"
              r.name left
          | _ -> check (label "the run's last line is `end tape` or `end frontier n`") false);
         (* S3: every value of the tape re-encodes to its own bytes. *)
         let values =
           List.filter_map
             (fun (ws, _) -> match ws with [ "answer"; _; _; "ok"; hex ] -> Some hex | _ -> None)
             r.steps
         in
         check
           (label (Printf.sprintf "%d answer values re-encode to their own bytes" (List.length values)))
           (List.for_all (fun hex -> hex_of_val (val_of_hex hex) = hex) values);
         (* S4: the red control of every run with two decisions or more.  The cut is Lean's: the
            last position at which two neighbouring view lines of the fixture differ.  The
            engine's replay of the tape before that decision must end at another view than the
            fixture's last.  A run in which no decision moves the view has no cut, and it
            fails. *)
         if List.length tape >= 2 then begin
           let moving =
             List.filter
               (fun i -> List.nth expected i <> List.nth expected (i + 1))
               (List.init (List.length tape) Fun.id)
           in
           check
             (label
                "the tape cut before its last decision that moves the view ends at another view (red control)")
             (match List.rev moving with
              | [] -> false
              | cut :: _ ->
                view_of (A.api_replay program r.fuel (take cut tape) [] table r.compile)
                <> List.nth expected (List.length tape))
         end;
         (* S4: the table and its red control, on a run with a host row. *)
         if r.rows <> [] then begin
           check
             (label
                (if r.observed_table_difference then
                   "with the empty table some machine view differs, as in Lean"
                 else "with the empty table every machine view is the same, as in Lean"))
             (differs expected (views program r [] tape) <> [] = r.observed_table_difference);
           check
             (label "a row whose bytes are cut is refused (red control)")
             (match table_of (List.map (fun b -> String.sub b 0 (String.length b - 1)) r.rows) with
              | Error _ -> true
              | Ok _ -> false)
         end)
end

module Fast = Adapter (Api_engine_inst) (struct
  type machine = Api_engine_inst.machine

  let timers (m : machine) : (int * E4_clock.t) list =
    List.map
      (fun (w : E4_clock.t Api_engine_inst.waiter) -> (w.Api_engine_inst.fiber, w.Api_engine_inst.payload))
      (Api_engine_inst.stores_of m).Api_engine_inst.timers.Api_engine_inst.wake.Api_engine_inst.waiters
end)

module Ref = Adapter (Api_engine_ref) (struct
  type machine = Api_engine_ref.machine

  let timers (m : machine) : (int * E4_clock.t) list =
    List.map
      (fun (w : E4_clock.t Api_engine_ref.waiter) -> (w.Api_engine_ref.fiber, w.Api_engine_ref.payload))
      (Api_engine_ref.stores_of m).Api_engine_ref.timers.Api_engine_ref.wake.Api_engine_ref.waiters
end)

(* ================================================================ main *)

let () =
  let dir = "." in
  let files =
    Sys.readdir dir |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".txt")
    |> List.sort compare
  in
  check "the scenario fixtures are present" (files <> []);
  let positions = ref 0 in
  List.iter
    (fun file ->
      let runs = read_fixture (Filename.concat dir file) in
      Printf.printf "== %s: %d runs ==\n" file (List.length runs);
      check (Printf.sprintf "%s holds at least one run" file) (runs <> []);
      List.iter
        (fun r ->
          positions := !positions + List.length r.steps + 1;
          Fast.run_one r;
          Ref.run_one r)
        runs)
    files;
  Printf.printf "%d positions compared on each of the two instances\n" !positions;
  Printf.printf "%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
