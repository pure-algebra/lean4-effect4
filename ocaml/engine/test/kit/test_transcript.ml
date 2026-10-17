(* test_transcript.ml -- the production tool's answers, pinned (R3-C-7's net).

   What it is: the replay of transcript.txt beside this file, the tool's required requests with
   their exact answers, through both of Kit_serve's transports: `serve_line` (`eff serve`) and
   `mcp_line` (`eff mcp`). Seat GEN's phase 1 moves the kit onto generated names and adapters,
   and slice 1.7 replaces Kit_serve's request execution; both must keep every answer, and this
   test fails at the line of any answer that moves.
   Depends on: Effect4_kit (Kit, Kit_serve), Eff_json_text.

   The transcript, one request a line and its answer on the next:
     both> REQUEST   a command request: through serve_line, and through mcp_line as the
                     tools/call of its op with its other fields as arguments
     serve> LINE     a line no tool call can carry (not JSON, not an object, no op)
     mcp> MESSAGE    a JSON-RPC message, through mcp_line only
     < ANSWER        the answer; "< (no reply)" for a message that gets none
   Lines starting with "#" are comments; blank lines separate nothing.

   Properties:
   X1  Through serve_line, every both> and serve> request answers its pinned line, byte for
       byte.                                                                tested
   X2  Through mcp_line, every both> request's tools/call answers the JSON-RPC result whose text
       is the same pinned answer and whose isError is whether its status is "error"; every mcp>
       message answers its pinned line, or no line.                         tested
   X3  Every answer is the same when asked twice, so no answer holds an unstable field the
       transcript would have to hide.                                      tested
   X4  Answers are compared after one named rule, `normalize`, and the transcript is never
       edited to absorb an unstable field. Today no answer holds a timing or another unstable
       field, so the rule is the identity.                                 by construction
   X5  Red control: a pinned answer with one byte changed is reported at its line.  tested
   X6  A deliberate change of answer is one reviewed diff: with E4_KIT_TRANSCRIPT_REWRITE set to
       the transcript's path, the test writes every answer afresh there, requests and comments
       unchanged, and passes.                                               by construction

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/kit
   Rewrite: E4_KIT_TRANSCRIPT_REWRITE=$PWD/engine/test/kit/transcript.txt, then the same. *)

open Effect4_kit
module J = Eff_json_text

(* X4: the one rule that would hide an unstable field of an answer. None exists today. *)
let normalize (answer : string) : string = answer

type transport = Both | Serve | Mcp

type entry = {
  line : int;  (** the request's line in the transcript *)
  transport : transport;
  request : string;
  answer : string option;  (** [None]: no reply *)
}

type item = Text of string | Entry of entry

let no_reply = "(no reply)"

(* "both>", "serve>" or "mcp>", then one space, then the request (a request may be empty). *)
let request_of (s : string) : (transport * string) option =
  let after prefix =
    let k = String.length prefix in
    if String.length s >= k && String.sub s 0 k = prefix then
      let rest = String.sub s k (String.length s - k) in
      Some (if String.length rest > 0 && rest.[0] = ' ' then String.sub rest 1 (String.length rest - 1) else rest)
    else None
  in
  match after "both>", after "serve>", after "mcp>" with
  | Some r, _, _ -> Some (Both, r)
  | _, Some r, _ -> Some (Serve, r)
  | _, _, Some r -> Some (Mcp, r)
  | None, None, None -> None

let parse (lines : string list) : item list =
  let rec go n acc = function
    | [] -> List.rev acc
    | l :: rest -> (
      match request_of l with
      | None -> go (n + 1) (Text l :: acc) rest
      | Some (transport, request) -> (
        match rest with
        | a :: rest' when String.length a >= 2 && String.sub a 0 2 = "< " ->
          let a = String.sub a 2 (String.length a - 2) in
          let answer = if String.equal a no_reply then None else Some a in
          go (n + 2) (Entry { line = n; transport; request; answer } :: acc) rest'
        | _ -> failwith (Printf.sprintf "transcript.txt:%d: a request with no answer line after it" n)))
  in
  go 1 [] lines

let read_lines path = In_channel.with_open_bin path In_channel.input_all |> String.split_on_char '\n'

(* The JSON-RPC wrapping of a both> request, and the reply it must get. *)
let tools_call (id : int) (request : string) : string option =
  match Kit.Json.parse request with
  | Ok (J.Object fields) -> (
    match List.assoc_opt "op" fields with
    | Some (J.String op) ->
      let args = List.filter (fun (k, _) -> not (String.equal k "op")) fields in
      Some
        (Kit.Json.render
           (J.Object
              [ ("jsonrpc", J.String "2.0");
                ("id", J.Int id);
                ("method", J.String "tools/call");
                ("params", J.Object [ ("name", J.String op); ("arguments", J.Object args) ]) ]))
    | _ -> None)
  | _ -> None

let status_of (answer : string) : string =
  match Kit.Json.parse answer with
  | Ok (J.Object fields) -> (match List.assoc_opt "status" fields with Some (J.String s) -> s | _ -> "?")
  | _ -> "?"

let tool_reply (id : int) (answer : string) : string =
  Kit.Json.render
    (J.Object
       [ ("jsonrpc", J.String "2.0");
         ("id", J.Int id);
         ("result",
           J.Object
             [ ("content", J.Array [ J.Object [ ("type", J.String "text"); ("text", J.String answer) ] ]);
               ("isError", J.Bool (String.equal (status_of answer) "error")) ]) ])

(* The answer a transport gives a request now, after the rule. *)
let serve (request : string) : string option = Some (normalize (Kit_serve.serve_line request))
let mcp (request : string) : string option = Option.map normalize (Kit_serve.mcp_line request)
let current (e : entry) : string option = match e.transport with Both | Serve -> serve e.request | Mcp -> mcp e.request

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "FAIL %s\n%!" name
  end

let show = function None -> no_reply | Some a -> a
let is_both e = match e.transport with Both -> true | Serve | Mcp -> false
let is_serve e = match e.transport with Serve -> true | Both | Mcp -> false
let is_mcp e = match e.transport with Mcp -> true | Both | Serve -> false

(* X1, X2 and X3 for one entry against an answer pinned for it: the failures, each named at its
   line. *)
let mismatches (e : entry) (pinned : string option) : string list =
  let now = current e in
  let pinned_failure =
    if Option.equal String.equal now pinned then []
    else [ Printf.sprintf "transcript.txt:%d: the answer moved\n  pinned: %s\n  now:    %s" (e.line + 1) (show pinned) (show now) ]
  in
  let twice_failure =
    if Option.equal String.equal now (current e) then []
    else [ Printf.sprintf "transcript.txt:%d: the answer differs when asked twice" (e.line + 1) ]
  in
  let mcp_failure =
    match e.transport, pinned with
    | Both, Some answer -> (
      match tools_call e.line e.request with
      | None -> [ Printf.sprintf "transcript.txt:%d: a both> request names its op" e.line ]
      | Some message ->
        let expected = tool_reply e.line answer and got = mcp message in
        if Option.equal String.equal got (Some expected) then []
        else [ Printf.sprintf "transcript.txt:%d: tools/call answers another text\n  expected: %s\n  got:      %s" e.line expected (show got) ])
    | Both, None -> [ Printf.sprintf "transcript.txt:%d: a both> request has an answer" e.line ]
    | (Serve | Mcp), _ -> []
  in
  pinned_failure @ twice_failure @ mcp_failure

let () =
  let items = parse (read_lines "transcript.txt") in
  let entries = List.filter_map (function Entry e -> Some e | Text _ -> None) items in
  match Sys.getenv_opt "E4_KIT_TRANSCRIPT_REWRITE" with
  | Some path ->
    (* X6: the same requests and comments, every answer afresh. *)
    let changed = ref 0 in
    let out =
      List.concat_map
        (function
          | Text t -> [ t ]
          | Entry e ->
            let now = current e in
            if not (Option.equal String.equal now e.answer) then incr changed;
            let prefix = match e.transport with Both -> "both>" | Serve -> "serve>" | Mcp -> "mcp>" in
            [ (if String.equal e.request "" then prefix else prefix ^ " " ^ e.request); "< " ^ show now ])
        items
    in
    Out_channel.with_open_bin path (fun oc -> output_string oc (String.concat "\n" out));
    Printf.printf "rewrote %s: %d entries, %d answers changed\n" path (List.length entries) !changed
  | None ->
    List.iter
      (fun e ->
        let replays = match e.transport with Both -> 2 | Serve | Mcp -> 1 in
        let failed = mismatches e e.answer in
        checks := !checks + replays + 1;
        failures := !failures + List.length failed;
        List.iter (fun f -> Printf.printf "FAIL %s\n%!" f) failed)
      entries;
    (* X5: the comparison sees one changed byte, at its line. *)
    (match List.find_opt is_both entries with
     | Some e ->
       let caught = mismatches e (Option.map (fun a -> a ^ " ") e.answer) in
       check "X5 red control: a pinned answer with one byte changed is reported at its line"
         (List.exists (fun f -> String.length f > 0 && String.starts_with ~prefix:(Printf.sprintf "transcript.txt:%d:" (e.line + 1)) f) caught)
     | None -> check "X5 red control: the transcript holds a both> request" false);
    (* The counts the receipt cites. *)
    let count p = List.length (List.filter p entries) in
    let command_status e = match e.transport, e.answer with (Both | Serve), Some a -> Some (status_of a) | _ -> None in
    let statuses = List.sort_uniq String.compare (List.filter_map command_status entries) in
    Printf.printf "transcript: %d requests: %d both> (each replayed through serve_line and mcp_line), %d serve>, %d mcp> (%d with no reply)\n"
      (List.length entries) (count is_both) (count is_serve) (count is_mcp)
      (count (fun e -> is_mcp e && Option.is_none e.answer));
    Printf.printf "statuses of both> and serve> answers: %s\n"
      (String.concat ", "
         (List.map (fun s -> Printf.sprintf "%s %d" s (count (fun e -> Option.equal String.equal (command_status e) (Some s)))) statuses));
    Printf.printf "test_transcript: %d checks, %d failures\n" !checks !failures;
    if !failures > 0 then exit 1
