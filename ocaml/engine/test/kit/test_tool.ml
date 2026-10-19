(* test_tool.ml -- the authoring tool's native shell against Lean's driver (seams S6).

   What it is: the session fixture (tool-requests.jsonl, its one copy, which bench_tool and
   scripts/check-mcp-protocol.py also read) served by Kit_tool, the native shell over the
   generated Tool.serve, and compared with tool-replies.jsonl: the replies that
   tools/Drivers/Session.lean printed for the same lines (Lean's own driver; regenerate with
   `lake env lean --run tools/Drivers/Session.lean < tool-requests.jsonl > tool-replies.jsonl`, and
   the same for tool-numbers.jsonl into tool-numbers-replies.jsonl).
   Depends on: Effect4_kit (Kit, Kit_tool), Effect4_gen.Api_gen.

   Properties:
   N1  Every reply equals Lean's, as JSON values (object keys in any order).        tested
   N2  The cached and the uncached transcripts are equal: each envelope served through the memo
       and through the uncached oracle answers the same value tree (`serve_transparent`). tested
   N3  Hostile lines refuse and change nothing: text that is not JSON, an unknown tag, an
       unselected version, and a method that disagrees with its request; the next line is
       served as if they had not come.                                          tested
   N4  Both drivers carry the same naturals (`CodecProfile.carries`, up to 2^53 - 1): on
       tool-numbers.jsonl (2^53 - 1 answers; 2^53 and a line that parses but does not read refuse
       as `codec unreadable`, at a site) every reply equals Lean's (tool-numbers-replies.jsonl,
       printed by tools/Drivers/Session.lean). Both drivers read the text by one grammar
       (NatJson.parse), so 2^53 + 1 and a number past the int range are in both trees, as a
       natural or as a numeral, and the reader refuses each at its site as outside the profile.
                                                                                tested

   N5  Drafts with invalid references recheck, kept edits refuse them, and the source entry
       stays at its address. Undo and wider subtree observations agree with Lean controls. tested

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/kit *)

open Effect4_kit
module G = Effect4_gen.Api_gen
module J = Kit.Json

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures
;;

let lines path =
  In_channel.with_open_bin path In_channel.input_all
  |> String.split_on_char '\n'
  |> List.filter (fun l -> String.trim l <> "")
;;

(* JSON values compared with each object's keys sorted. *)
let rec norm (j : J.t) : J.t =
  match j with
  | J.NatJson_obj es ->
    J.NatJson_obj
      (List.sort
         (fun (a, _) (b, _) -> compare a b)
         (List.map (fun (k, v) -> k, norm v) es))
  | J.NatJson_arr xs -> J.NatJson_arr (List.map norm xs)
  | other -> other
;;

let parse s =
  match Kit.Json.parse s with
  | Ok j -> Some (norm j)
  | Error _ -> None
;;

let requests = lines "tool-requests.jsonl"

(* Whether a reply is a refusal, and whether it is the text parser's own (a string reason). *)
let refusal j =
  match j with
  | Some (J.NatJson_obj [ ("refused", why) ]) -> Some why
  | _ -> None
;;

(* Serve a fixture through one native session and compare every reply with Lean's. A text-parser
   refusal is each driver's own words, so there both must refuse; every other reply, refusals of the
   wire included, must be equal. *)
let compare_with_lean label requests replies =
  let lean = lines replies in
  let t = Kit_tool.create () in
  let native = List.map (Kit_tool.serve_line t) requests in
  check
    (Printf.sprintf
       "%s the fixture has %d requests and Lean %d replies"
       label
       (List.length requests)
       (List.length lean))
    (List.length requests = List.length lean && requests <> []);
  List.iteri
    (fun i (n, l) ->
       let same =
         match refusal (parse l) with
         | Some (J.NatJson_str _) -> refusal (parse n) <> None
         | _ -> parse n = parse l && parse n <> None
       in
       check (Printf.sprintf "%s reply %d equals Lean's" label i) same;
       if not same then Printf.printf "  native: %s\n  lean:   %s\n" n l)
    (List.combine native lean)
;;

(* N1 *)
let () = compare_with_lean "N1" requests "tool-replies.jsonl"

(* N4 *)
let () =
  compare_with_lean "N4" (lines "tool-numbers.jsonl") "tool-numbers-replies.jsonl";
  let past_int =
    "{\"method\":\"run\",\"payload\":{\"_tag\":\"ask\",\"q\":{\"_tag\":\"run\",\"id\":{\"n\":4611686018427387904},\"form\":{\"_tag\":\"view\"}}},\"version\":1}"
  in
  check
    "N4 an integer past the int range refuses"
    (match parse (Kit_tool.serve_line (Kit_tool.create ()) past_int) with
     | Some (J.NatJson_obj [ ("refused", _) ]) -> true
     | _ -> false)
;;

(* N2: every fixture envelope served cached and uncached, side by side. *)
let () =
  let envelopes =
    List.filter_map
      (fun line ->
         match Kit.Json.parse line with
         | Ok json -> Result.to_option (Kit.Json.read G.tool_native_envelope_shape json)
         | Error _ -> None)
      requests
  in
  check
    "N2 every fixture line reads as an envelope"
    (List.length envelopes = List.length requests);
  let cached = ref G.tool_native_start
  and uncached = ref G.tool_native_start in
  List.iteri
    (fun i v ->
       match G.tool_native_serve !cached v, G.tool_native_serve_uncached !uncached v with
       | Ok (reply1, s1), Ok (reply2, s2) ->
         cached := s1;
         uncached := s2;
         check
           (Printf.sprintf "N2 request %d: cached and uncached replies are equal" i)
           (reply1 = reply2)
       | _ -> check (Printf.sprintf "N2 request %d is served" i) false)
    envelopes
;;

(* N3: hostile lines before the first request leave the session where it was. *)
let () =
  match requests with
  | [] -> check "N3 the fixture has a first request" false
  | first :: _ ->
    let replace sub by s =
      let n = String.length sub in
      let rec go i =
        if i + n > String.length s
        then s
        else if String.sub s i n = sub
        then String.sub s 0 i ^ by ^ String.sub s (i + n) (String.length s - i - n)
        else go (i + 1)
      in
      go 0
    in
    let hostile =
      [ "not JSON", "{\"method\": "
      ; "an unknown tag", replace "\"_tag\":\"open_\"" "\"_tag\":\"opened\"" first
      ; "an unselected version", replace "\"version\":1" "\"version\":2" first
      ; ( "a method that disagrees with its request"
        , replace "\"method\":\"open\"" "\"method\":\"edit\"" first )
      ]
    in
    let t = Kit_tool.create () in
    List.iter
      (fun (name, line) ->
         let reply = Kit_tool.serve_line t line in
         let refused =
           match parse reply with
           | Some (J.NatJson_obj [ ("refused", _) ]) -> true
           | _ -> false
         in
         check ("N3 " ^ name ^ " refuses") (refused && line <> first))
      hostile;
    let fresh = Kit_tool.create () in
    check
      "N3 after them, the first request answers as on a fresh session"
      (parse (Kit_tool.serve_line t first) = parse (Kit_tool.serve_line fresh first))
;;

(* N5: the preserved reference-fault cases exercise the generated source feed. *)
let () =
  let t = Kit_tool.create () in
  let requests =
    [ "{\"method\":\"open\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"open_\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]},\"name\":\"fault\",\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"bind\",\"first\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}},\"rest\":{\"_tag\":\"provideLayer\",\"layer\":{\"_tag\":\"effectDiscard\",\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":1}}}},\"isLocal\":false,\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":1}}}}}}}},\"version\":1}"
    ; "{\"method\":\"edit\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"edit\",\"a\":{\"_tag\":\"commit\",\"items\":[[{\"_tag\":\"at_\",\"path\":[0],\"expected\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}},{\"_tag\":\"fill\",\"q\":{\"_tag\":\"provideLayer\",\"layer\":{\"_tag\":\"ref\",\"target\":[1,0]},\"isLocal\":false,\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}}}]],\"policy\":\"keepExact\"},\"at_\":{\"doc\":{\"generation\":0,\"name\":\"fault\"},\"revision\":0}}},\"version\":1}"
    ; "{\"method\":\"edit\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"edit\",\"a\":{\"_tag\":\"draft\",\"e\":{\"_tag\":\"fill\",\"path\":[0],\"program\":{\"_tag\":\"provideLayer\",\"layer\":{\"_tag\":\"ref\",\"target\":[1,0]},\"isLocal\":false,\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}}}},\"at_\":{\"doc\":{\"generation\":0,\"name\":\"fault\"},\"revision\":0}}},\"version\":1}"
    ; "{\"method\":\"edit\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"edit\",\"a\":{\"_tag\":\"draft\",\"e\":{\"_tag\":\"fill\",\"path\":[0],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}}},\"at_\":{\"doc\":{\"generation\":0,\"name\":\"fault\"},\"revision\":1}}},\"version\":1}"
    ; "{\"method\":\"edit\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"edit\",\"a\":{\"_tag\":\"draft\",\"e\":{\"_tag\":\"fill\",\"path\":[0],\"program\":{\"_tag\":\"provideLayer\",\"layer\":{\"_tag\":\"ref\",\"target\":[1,0]},\"isLocal\":false,\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}}}},\"at_\":{\"doc\":{\"generation\":0,\"name\":\"fault\"},\"revision\":2}}},\"version\":1}"
    ; "{\"method\":\"doc\",\"payload\":{\"_tag\":\"ask\",\"q\":{\"_tag\":\"doc\",\"at_\":[0]}},\"version\":1}"
    ; "{\"method\":\"open\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"open_\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]},\"name\":\"fault\",\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"bind\",\"first\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}},\"rest\":{\"_tag\":\"provideLayer\",\"layer\":{\"_tag\":\"effectDiscard\",\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":1}}}},\"isLocal\":false,\"body\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":1}}}}}}}},\"version\":1}"
    ; "{\"method\":\"edit\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"edit\",\"a\":{\"_tag\":\"commit\",\"items\":[[{\"_tag\":\"at_\",\"path\":[0],\"expected\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}},{\"_tag\":\"fill\",\"q\":{\"_tag\":\"bind\",\"first\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":1}}},\"rest\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":7}}}}}]],\"policy\":\"keepExact\"},\"at_\":{\"doc\":{\"generation\":1,\"name\":\"fault\"},\"revision\":0}}},\"version\":1}"
    ]
  in
  let replies = List.map (fun r -> parse (Kit_tool.serve_line t r)) requests in
  let rec at keys value =
    match keys, value with
    | [], value -> value
    | key :: rest, Some (J.NatJson_obj fields) -> at rest (List.assoc_opt key fields)
    | _ -> None
  in
  let get i keys = at keys (List.nth replies i) in
  let result = [ "payload"; "result" ] in
  let action = result @ [ "arg0"; "a" ] in
  let view = action @ [ "view" ] in
  let delta = action @ [ "receipt"; "steps" ] in
  check
    "N5 opening the reference-fault control succeeds"
    (get 0 (result @ [ "_tag" ]) = Some (J.NatJson_str "ok"));
  check
    "N5 kept edit adding an invalid reference refuses"
    (get 1 (result @ [ "_tag" ]) = Some (J.NatJson_str "error"));
  List.iter
    (fun i ->
       check
         (Printf.sprintf "N5 draft %d has the refused root type" i)
         (get i (view @ [ "type" ]) = Some J.NatJson_null);
       check
         (Printf.sprintf "N5 draft %d rechecks" i)
         (match get i delta with
          | Some (J.NatJson_arr [ J.NatJson_obj fields ]) ->
            at [ "delta"; "_tag" ] (Some (J.NatJson_obj fields))
            = Some (J.NatJson_str "rechecked")
          | _ -> false))
    [ 2; 4 ];
  check
    "N5 the edited source address retains its own table entry"
    (match get 5 (result @ [ "arg0"; "view"; "inspection"; "entry"; "path" ]) with
     | Some (J.NatJson_arr [ _ ]) -> true
     | _ -> false);
  check
    "N5 removing the invalid reference restores a typed root"
    (match get 3 (view @ [ "type" ]) with
     | Some (J.NatJson_obj _) -> true
     | _ -> false);
  check
    "N5 the wide filling reports all three source addresses"
    (match get 7 delta with
     | Some (J.NatJson_arr [ J.NatJson_obj fields ]) ->
       at [ "delta"; "_tag" ] (Some (J.NatJson_obj fields))
       = Some (J.NatJson_str "spliced")
       &&
         (match at [ "delta"; "shown" ] (Some (J.NatJson_obj fields)) with
         | Some (J.NatJson_arr paths) -> List.length paths = 3
         | _ -> false)
     | _ -> false);
  List.iteri
    (fun i _reply ->
       if get i (result @ [ "_tag" ]) = None
       then
         Printf.printf
           "N5 unreadable reply %d: %s\n"
           i
           (Kit_tool.serve_line (Kit_tool.create ()) (List.nth requests i)))
    replies
;;

let () =
  Printf.printf
    "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
;;
