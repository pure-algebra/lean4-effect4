(* test_tool.ml -- the authoring tool's native shell against Lean's driver (seams S6).

   What it is: the session fixture (tool-requests.jsonl, a copy of
   Test/fixtures/session/requests.jsonl) served by Kit_tool, the native shell over the generated
   Tool.serve, and compared with tool-replies.jsonl: the replies tools/Drivers/Session.lean printed
   for the same lines (Lean's own driver; regenerate with
   `lake env lean --run tools/Drivers/Session.lean < tool-requests.jsonl > tool-replies.jsonl`).
   Depends on: Effect4_kit (Kit, Kit_json, Kit_tool), Effect4_gen.Api_gen, Eff_json_text.

   Properties:
   N1  Every reply equals Lean's, as JSON values (object keys in any order).        tested
   N2  The cached and the uncached transcripts are equal: each envelope served through the memo
       and through the uncached oracle answers the same value tree (`serve_transparent`). tested
   N3  Hostile lines refuse and change nothing: text that is not JSON, an unknown tag, an
       unselected version, and a method that disagrees with its request; the next line is
       served as if they had not come.                                          tested

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/kit *)

open Effect4_kit
module G = Effect4_gen.Api_gen
module J = Eff_json_text

let failures = ref 0
let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let lines path =
  In_channel.with_open_bin path In_channel.input_all
  |> String.split_on_char '\n'
  |> List.filter (fun l -> String.trim l <> "")

(* JSON values compared with each object's keys sorted. *)
let rec norm (j : J.t) : J.t =
  match j with
  | J.Object es -> J.Object (List.sort (fun (a, _) (b, _) -> compare a b) (List.map (fun (k, v) -> (k, norm v)) es))
  | J.Array xs -> J.Array (List.map norm xs)
  | other -> other

let parse s = match Kit.Json.parse s with Ok j -> Some (norm j) | Error _ -> None

let requests = lines "tool-requests.jsonl"
let lean = lines "tool-replies.jsonl"

(* N1 *)
let () =
  let t = Kit_tool.create () in
  let native = List.map (Kit_tool.serve_line t) requests in
  check (Printf.sprintf "N1 the fixture has %d requests and Lean %d replies" (List.length requests) (List.length lean))
    (List.length requests = List.length lean && requests <> []);
  List.iteri
    (fun i (n, l) ->
      let same = parse n = parse l && parse n <> None in
      check (Printf.sprintf "N1 reply %d equals Lean's" i) same;
      if not same then Printf.printf "  native: %s\n  lean:   %s\n" n l)
    (List.combine native lean)

(* N2: every fixture envelope served cached and uncached, side by side. *)
let () =
  let envelopes =
    List.filter_map
      (fun line -> match Kit.Json.parse line with
        | Ok json -> Kit_json.read G.tool_native_envelope_shape json
        | Error _ -> None)
      requests
  in
  check "N2 every fixture line reads as an envelope" (List.length envelopes = List.length requests);
  let cached = ref G.tool_native_start and uncached = ref G.tool_native_start in
  List.iteri
    (fun i v ->
      match G.tool_native_serve !cached v, G.tool_native_serve_uncached !uncached v with
      | Ok (reply1, s1), Ok (reply2, s2) ->
        cached := s1;
        uncached := s2;
        check (Printf.sprintf "N2 request %d: cached and uncached replies are equal" i) (reply1 = reply2)
      | _ -> check (Printf.sprintf "N2 request %d is served" i) false)
    envelopes

(* N3: hostile lines before the first request leave the session where it was. *)
let () =
  match requests with
  | [] -> check "N3 the fixture has a first request" false
  | first :: _ ->
    let replace sub by s =
      let n = String.length sub in
      let rec go i = if i + n > String.length s then s
        else if String.sub s i n = sub then String.sub s 0 i ^ by ^ String.sub s (i + n) (String.length s - i - n)
        else go (i + 1) in
      go 0
    in
    let hostile =
      [ ("not JSON", "{\"method\": ");
        ("an unknown tag", replace "\"_tag\":\"open_\"" "\"_tag\":\"opened\"" first);
        ("an unselected version", replace "\"version\":1" "\"version\":2" first);
        ("a method that disagrees with its request", replace "\"method\":\"open\"" "\"method\":\"edit\"" first) ]
    in
    let t = Kit_tool.create () in
    List.iter
      (fun (name, line) ->
        let reply = Kit_tool.serve_line t line in
        let refused = match parse reply with Some (J.Object [ ("refused", _) ]) -> true | _ -> false in
        check ("N3 " ^ name ^ " refuses") (refused && line <> first))
      hostile;
    let fresh = Kit_tool.create () in
    check "N3 after them, the first request answers as on a fresh session"
      (parse (Kit_tool.serve_line t first) = parse (Kit_tool.serve_line fresh first))

let () =
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
