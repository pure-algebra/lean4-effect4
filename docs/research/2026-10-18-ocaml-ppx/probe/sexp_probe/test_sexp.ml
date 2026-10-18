(* test_sexp.ml -- probe: the tool's request and reply envelopes through Lean's sexp face.

   What it checks, on the kit's fixture lines (read through Kit_json, the JSON twin):
   S1 Lean's printer is Sexplib0's: `print_mach` (lowered) equals `Sexp.to_string_mach`.
   S2 Lean's canonical bytes are csexp's: `canonical` equals `Csexp.to_string`.
   S3 The round trip through text: Sexplib's parser reads the machine text back, and Lean's
      reader gives the same carrier (`*_equal`), with no fragment.
   S4 The typed face equals the value-tree face (`request_to_sexp r = request_val_to_sexp v`).
   S5 Exactness controls: a reordered field, a padded natural and a dropped field are refused.
   S6 The agent face in sexp: each request served by `serve_sexp` answers the sexp of the reply
      the JSON driver (Kit_tool) answers, in one session each.
   M  Sizes and times, printed, not checked. *)

module G = Effect4_gen.Api_gen
open Effect4_kit
module S = Sexplib0.Sexp
module C = Csexp.Make (Sexplib0.Sexp)

let failures = ref 0
let check name ok = if not ok then (incr failures; Printf.printf "FAIL %s\n%!" name)

let lines f = In_channel.with_open_text f In_channel.input_all |> String.split_on_char '\n' |> List.filter (( <> ) "")

let val_opt shape line =
  match Kit.Json.parse line with
  | Error _ -> None
  | Ok j -> Kit_json.read shape j

let val_of shape line = match val_opt shape line with Some v -> v | None -> failwith ("unreadable: " ^ line)

let codes s = List.init (String.length s) (fun i -> Char.code s.[i])

let readable shape = List.filter (fun l -> val_opt shape l <> None)
let request_lines = List.concat_map lines [ "../kit/tool-requests.jsonl"; "../kit/tool-numbers.jsonl" ]
let reply_lines = List.concat_map lines [ "../kit/tool-replies.jsonl"; "../kit/tool-numbers-replies.jsonl" ]
let requests = readable G.tool_native_envelope_shape request_lines
let replies = readable G.tool_native_reply_envelope_shape reply_lines

let rec mutate_first_struct = function
  (* swap the first two fields of the first structure met *)
  | S.List (S.List [ S.Atom a; x ] :: S.List [ S.Atom b; y ] :: rest) ->
    Some (S.List (S.List [ S.Atom b; y ] :: S.List [ S.Atom a; x ] :: rest))
  | S.List xs ->
    let rec go acc = function
      | [] -> None
      | x :: rest -> (match mutate_first_struct x with Some x' -> Some (S.List (List.rev_append acc (x' :: rest))) | None -> go (x :: acc) rest)
    in go [] xs
  | S.Atom _ -> None

let rec pad_first_nat = function
  | S.Atom a when a <> "" && String.for_all (fun c -> c >= '0' && c <= '9') a -> Some (S.Atom ("0" ^ a))
  | S.Atom _ -> None
  | S.List xs ->
    let rec go acc = function
      | [] -> None
      | x :: rest -> (match pad_first_nat x with Some x' -> Some (S.List (List.rev_append acc (x' :: rest))) | None -> go (x :: acc) rest)
    in go [] xs

let () =
  let json_bytes = ref 0 and mach_bytes = ref 0 and hum_bytes = ref 0 and csexp_bytes = ref 0 in
  List.iteri (fun i line ->
    let name k = Printf.sprintf "request %d %s" i k in
    let v = val_of G.tool_native_envelope_shape line in
    match G.test_probe_sexp_lane_request_of_val v with
    | None -> check (name "of_val") false
    | Some r ->
      let sx = G.test_probe_sexp_lane_request_to_sexp r in
      let mach = S.to_string_mach sx in
      json_bytes := !json_bytes + String.length line;
      mach_bytes := !mach_bytes + String.length mach;
      hum_bytes := !hum_bytes + String.length (S.to_string_hum sx);
      csexp_bytes := !csexp_bytes + String.length (C.to_string sx);
      check (name "S1 printer") (String.equal (G.test_probe_sexp_lane_print_mach sx) mach);
      check (name "S2 canonical") (G.test_probe_sexp_lane_canonical sx = codes (C.to_string sx));
      let back = Parsexp.Single.parse_string_exn mach in
      check (name "S3 round trip")
        (match G.test_probe_sexp_lane_request_of_sexp back with
         | Some r' -> G.test_probe_sexp_lane_request_equal r r'
         | None -> false);
      check (name "S4 typed = tree") (S.equal sx (G.test_probe_sexp_lane_request_val_to_sexp v));
      (match mutate_first_struct sx with
       | Some m -> check (name "S5 reorder refused") (G.test_probe_sexp_lane_request_of_sexp m = None)
       | None -> ());
      (match pad_first_nat sx with
       | Some m -> check (name "S5 padded natural refused") (G.test_probe_sexp_lane_request_of_sexp m = None)
       | None -> ());
      (match sx with
       | S.List (_ :: rest) -> check (name "S5 dropped field refused") (G.test_probe_sexp_lane_request_of_sexp (S.List rest) = None)
       | _ -> ()))
    requests;
  List.iteri (fun i line ->
    let v = val_of G.tool_native_reply_envelope_shape line in
    match G.test_probe_sexp_lane_reply_of_val v with
    | None -> check (Printf.sprintf "reply %d of_val" i) false
    | Some r ->
      let sx = G.test_probe_sexp_lane_reply_to_sexp r in
      let mach = S.to_string_mach sx in
      json_bytes := !json_bytes + String.length line;
      mach_bytes := !mach_bytes + String.length mach;
      hum_bytes := !hum_bytes + String.length (S.to_string_hum sx);
      csexp_bytes := !csexp_bytes + String.length (C.to_string sx);
      check (Printf.sprintf "reply %d S1" i) (String.equal (G.test_probe_sexp_lane_print_mach sx) mach);
      check (Printf.sprintf "reply %d S3" i)
        (match G.test_probe_sexp_lane_reply_of_sexp (Parsexp.Single.parse_string_exn mach) with
         | Some r' -> G.test_probe_sexp_lane_reply_equal r r'
         | None -> false))
    replies;
  (* S6: the sexp face served against the JSON face, one session each *)
  let json_session = Kit_tool.create () in
  let sexp_session = ref G.tool_native_start in
  List.iteri (fun i line ->
    let reply_json = Kit_tool.serve_line json_session line in
    match val_opt G.tool_native_envelope_shape line with
    | None -> check (Printf.sprintf "S6 %d JSON refuses an unreadable line" i) (String.length reply_json > 10 && String.sub reply_json 0 10 = "{\"refused\"")
    | Some v ->
    let text = S.to_string_mach (G.test_probe_sexp_lane_request_val_to_sexp v) in
    match G.test_probe_sexp_lane_serve_sexp !sexp_session (Parsexp.Single.parse_string_exn text) with
    | Error _ -> check (Printf.sprintf "S6 %d refused where JSON answered %s" i (String.sub reply_json 0 (min 60 (String.length reply_json)))) (String.length reply_json > 10 && String.sub reply_json 0 10 = "{\"refused\"")
    | Ok (reply, s') ->
      sexp_session := s';
      let from_json = G.test_probe_sexp_lane_reply_val_to_sexp (val_of G.tool_native_reply_envelope_shape reply_json) in
      check (Printf.sprintf "S6 %d same reply" i) (S.equal reply from_json))
    (lines "../kit/tool-requests.jsonl");
  Printf.printf "M fixture lines: %d requests (%d readable), %d replies (%d readable)\n"
    (List.length request_lines) (List.length requests) (List.length reply_lines) (List.length replies);
  Printf.printf "M sizes over %d requests and %d replies: JSON %d bytes, sexp mach %d, sexp hum %d, csexp %d\n"
    (List.length requests) (List.length replies) !json_bytes !mach_bytes !hum_bytes !csexp_bytes;
  (* M times: one request line through each face, read and written, N times *)
  let n = 2000 in
  let time f = let t0 = Unix.gettimeofday () in for _ = 1 to n do f () done; (Unix.gettimeofday () -. t0) *. 1e6 /. float n in
  let line = List.hd requests in
  let shape = G.tool_native_envelope_shape in
  let json_us = time (fun () ->
    match Kit.Json.parse line with
    | Ok j -> (match Kit_json.read shape j with Some v -> ignore (Kit_json.render (Kit_json.print shape v)) | None -> ())
    | Error _ -> ()) in
  let mach = S.to_string_mach (G.test_probe_sexp_lane_request_val_to_sexp (val_of shape line)) in
  let sexp_us = time (fun () ->
    match G.test_probe_sexp_lane_request_val_of_sexp (Parsexp.Single.parse_string_exn mach) with
    | Some v -> ignore (S.to_string_mach (G.test_probe_sexp_lane_request_val_to_sexp v))
    | None -> ()) in
  Printf.printf "M one request (%d JSON bytes) read and written: JSON (Kit_json, hand) %.1f us, sexp (Parsexp + Lean lowered) %.1f us\n"
    (String.length line) json_us sexp_us;
  if !failures > 0 then (Printf.printf "%d failure(s)\n" !failures; exit 1) else print_endline "all sexp checks pass"
