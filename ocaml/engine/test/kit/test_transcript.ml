(* test_transcript.ml -- the production tool's answers, pinned (R3-C-7's net).

   What it is: the replay of serve.transcript beside this file, the kit's required requests with
   their exact answers, through Kit_serve's transport `serve_line` (`eff serve`). Seat GEN's
   phase 1 moves the kit onto generated names and adapters, and slice 1.7 replaces Kit_serve's
   request execution; both must keep every answer, and this test fails at the line of any answer
   that moves. (`eff mcp` serves the authoring tool, Kit_mcp, tested by test_mcp.ml.)
   Depends on: Effect4_kit (Kit, Kit_serve).

   The transcript, one request a line and its answer on the next:
     serve> REQUEST  a request line, through serve_line
     < ANSWER        the answer
   Lines starting with "#" are comments; blank lines separate nothing.

   Properties:
   X1  Through serve_line, every request answers its pinned line, byte for byte.  tested
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
   Rewrite: E4_KIT_TRANSCRIPT_REWRITE=$PWD/engine/test/kit/serve.transcript, then the same. *)

open Effect4_kit
module J = Kit.Json

(* X4: the one rule that would hide an unstable field of an answer. None exists today. *)
let normalize (answer : string) : string = answer

type entry =
  { line : int (** the request's line in the transcript *)
  ; request : string
  ; answer : string option (** [None]: no reply *)
  }

type item =
  | Text of string
  | Entry of entry

let no_reply = "(no reply)"

(* "serve>", then one space, then the request (a request may be empty). *)
let request_of (s : string) : string option =
  let after prefix =
    let k = String.length prefix in
    if String.length s >= k && String.sub s 0 k = prefix
    then (
      let rest = String.sub s k (String.length s - k) in
      Some
        (if String.length rest > 0 && rest.[0] = ' '
         then String.sub rest 1 (String.length rest - 1)
         else rest))
    else None
  in
  after "serve>"
;;

let parse (lines : string list) : item list =
  let rec go n acc = function
    | [] -> List.rev acc
    | l :: rest ->
      (match request_of l with
       | None -> go (n + 1) (Text l :: acc) rest
       | Some request ->
         (match rest with
          | a :: rest' when String.length a >= 2 && String.sub a 0 2 = "< " ->
            let a = String.sub a 2 (String.length a - 2) in
            let answer = if String.equal a no_reply then None else Some a in
            go (n + 2) (Entry { line = n; request; answer } :: acc) rest'
          | _ ->
            failwith
              (Printf.sprintf
                 "serve.transcript:%d: a request with no answer line after it"
                 n)))
  in
  go 1 [] lines
;;

let read_lines path =
  In_channel.with_open_bin path In_channel.input_all |> String.split_on_char '\n'
;;

let status_of (answer : string) : string =
  match Kit.Json.parse answer with
  | Ok (J.NatJson_obj fields) ->
    (match List.assoc_opt "status" fields with
     | Some (J.NatJson_str s) -> s
     | _ -> "?")
  | _ -> "?"
;;

(* The answer serve_line gives a request now, after the rule. *)
let current (e : entry) : string option =
  Some (normalize (Kit_serve.serve_line e.request))
;;

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if not ok
  then (
    incr failures;
    Printf.printf "FAIL %s\n%!" name)
;;

let show = function
  | None -> no_reply
  | Some a -> a
;;

(* X1 and X3 for one entry against an answer pinned for it: the failures, each named at its
   line. *)
let mismatches (e : entry) (pinned : string option) : string list =
  let now = current e in
  let pinned_failure =
    if Option.equal String.equal now pinned
    then []
    else
      [ Printf.sprintf
          "serve.transcript:%d: the answer moved\n  pinned: %s\n  now:    %s"
          (e.line + 1)
          (show pinned)
          (show now)
      ]
  in
  let twice_failure =
    if Option.equal String.equal now (current e)
    then []
    else
      [ Printf.sprintf
          "serve.transcript:%d: the answer differs when asked twice"
          (e.line + 1)
      ]
  in
  pinned_failure @ twice_failure
;;

let () =
  let items = parse (read_lines "serve.transcript") in
  let entries =
    List.filter_map
      (function
        | Entry e -> Some e
        | Text _ -> None)
      items
  in
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
            [ (if String.equal e.request "" then "serve>" else "serve> " ^ e.request)
            ; "< " ^ show now
            ])
        items
    in
    Out_channel.with_open_bin path (fun oc -> output_string oc (String.concat "\n" out));
    Printf.printf
      "rewrote %s: %d entries, %d answers changed\n"
      path
      (List.length entries)
      !changed
  | None ->
    List.iter
      (fun e ->
         let failed = mismatches e e.answer in
         checks := !checks + 2;
         failures := !failures + List.length failed;
         List.iter (fun f -> Printf.printf "FAIL %s\n%!" f) failed)
      entries;
    (* X5: the comparison sees one changed byte, at its line. *)
    (match entries with
     | e :: _ ->
       let caught = mismatches e (Option.map (fun a -> a ^ " ") e.answer) in
       check
         "X5 red control: a pinned answer with one byte changed is reported at its line"
         (List.exists
            (fun f ->
               String.length f > 0
               && String.starts_with
                    ~prefix:(Printf.sprintf "serve.transcript:%d:" (e.line + 1))
                    f)
            caught)
     | [] -> check "X5 red control: the transcript holds a request" false);
    (* The counts the receipt cites. *)
    let count p = List.length (List.filter p entries) in
    let command_status e = Option.map status_of e.answer in
    let statuses =
      List.sort_uniq String.compare (List.filter_map command_status entries)
    in
    Printf.printf
      "transcript: %d requests, each replayed through serve_line\n"
      (List.length entries);
    Printf.printf
      "statuses of the answers: %s\n"
      (String.concat
         ", "
         (List.map
            (fun s ->
               Printf.sprintf
                 "%s %d"
                 s
                 (count (fun e -> Option.equal String.equal (command_status e) (Some s))))
            statuses));
    Printf.printf "test_transcript: %d checks, %d failures\n" !checks !failures;
    if !failures > 0 then exit 1
;;
