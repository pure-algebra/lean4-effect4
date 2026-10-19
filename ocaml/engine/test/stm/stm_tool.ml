(* stm_tool -- the native tool session (Kit_tool over the generated Tool.Native.serve) against Lean's
   uncached oracle under qcheck-stm (plan E2).

   What it is: a session is the function of the requests it served. The model holds, per session,
   the requests served so far, and answers each line with Lean's uncached oracle
   (`Api_gen.tool_native_serve_uncached`, lowered from src/Effect4/Tool/Native.lean) from the
   session those requests reach; a line that does not parse, does not read, or is refused at the
   wire answers "refused" and changes nothing. The system is Kit_tool: the shell's mutable cell
   over the cached `serve`. So each run checks Kit_tool's T1-T3 (a refused line changes nothing,
   a served line moves the session) and T4 (the checker memo changes cost, never a reply) on
   random request lists, beyond the pinned fixture of test_tool.
     A0 the alphabet's control: the request lines still read under today's envelope (below). A
        respelled wire would make served lines refused on both sides, and the tests after it
        would hold while checking little; A0 fails instead.
     S1 sequential: two sessions, interleaved, agree with the model.
     S2 red control: a shell that serves every line on a fresh session disagrees: it forgets.
     P1 parallel (STM_domain): two sessions, each served by its own domain, as a native host
        serves many sessions: no state is shared between them, not even the generated start
        session they both begin from.
     P2 red control: one session served by two domains at once, against the one-owner rule
        (ocaml/STANDARDS.md rule 8): QCheck must find an outcome no interleaving explains.
   The requests are a finite alphabet over one document, "default": two programs to open, the
   document, its address [0], the history, drafts at [0] at a generation and revision, a revert,
   text that is not JSON, and an unknown tag. A draft is mostly drawn at the session's current
   generation and revision, so most drafts land.
   Depends on: Effect4_kit (Kit, Kit.Json, Kit_tool), Effect4_gen.Api_gen,
   qcheck-stm, Stm_support.
   The evidence is host-only: finite runs on this machine. The oracle is Lean's code lowered by
   LCNF, so a disagreement names a shell or lowering fault; no theorem reaches the runs. *)

open Effect4_kit
module G = Effect4_gen.Api_gen
module J = Kit.Json

type req =
  | Open of int (** 0: the session fixture's program; 1: succeed 1 *)
  | Doc
  | Doc0 (** the document at address [0] *)
  | History
  | Draft of int * int * int (** generation, revision, value: 0 is 6, 1 is 7, 2 is "x" *)
  | Revert of int * int (** generation, revision: revert history entry 1 *)
  | Garbage
  | Unreadable

let show_req = function
  | Open v -> "Open " ^ string_of_int v
  | Doc -> "Doc"
  | Doc0 -> "Doc0"
  | History -> "History"
  | Draft (g, r, v) -> Printf.sprintf "Draft g%d r%d v%d" g r v
  | Revert (g, r) -> Printf.sprintf "Revert g%d r%d" g r
  | Garbage -> "Garbage"
  | Unreadable -> "Unreadable"
;;

let fixture_program =
  {|{"_tag":"bind","first":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":5}}},"rest":{"_tag":"bind","first":{"_tag":"perform","op":{"_tag":"refMake"},"request":{"_tag":"var","index":0}},"rest":{"_tag":"bind","first":{"_tag":"perform","op":{"_tag":"refSet"},"request":{"_tag":"app","args":[{"_tag":"var","index":1},{"_tag":"lit","value":{"_tag":"nat","value":7}}],"atom":"pair"}},"rest":{"_tag":"perform","op":{"_tag":"refGet"},"request":{"_tag":"var","index":1}}}}}|}
;;

let succeed_one =
  {|{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":1}}}|}
;;

let at g r =
  Printf.sprintf {|{"doc":{"generation":%d,"name":"default"},"revision":%d}|} g r
;;

let value = function
  | 0 -> {|{"_tag":"nat","value":6}|}
  | 1 -> {|{"_tag":"nat","value":7}|}
  | _ -> {|{"_tag":"str","value":"x"}|}
;;

let line = function
  | Open v ->
    Printf.sprintf
      {|{"method":"open","payload":{"_tag":"act","a":{"_tag":"open_","app":{"rows":[],"services":[],"types":[]},"name":"default","sketch":{"holes":[],"program":%s}}},"version":1}|}
      (if v = 0 then fixture_program else succeed_one)
  | Doc ->
    {|{"method":"doc","payload":{"_tag":"ask","q":{"_tag":"doc","at_":null}},"version":1}|}
  | Doc0 ->
    {|{"method":"doc","payload":{"_tag":"ask","q":{"_tag":"doc","at_":[0]}},"version":1}|}
  | History ->
    {|{"method":"history","payload":{"_tag":"ask","q":{"_tag":"history"}},"version":1}|}
  | Draft (g, r, v) ->
    Printf.sprintf
      {|{"method":"edit","payload":{"_tag":"act","a":{"_tag":"edit","a":{"_tag":"draft","e":{"_tag":"fill","path":[0],"program":{"_tag":"succeed","value":{"_tag":"lit","value":%s}}}},"at_":%s}},"version":1}|}
      (value v)
      (at g r)
  | Revert (g, r) ->
    Printf.sprintf
      {|{"method":"edit","payload":{"_tag":"act","a":{"_tag":"edit","a":{"_tag":"revert","entry":1},"at_":%s}},"version":1}|}
      (at g r)
  | Garbage -> {|{"method": |}
  | Unreadable ->
    {|{"method":"doc","payload":{"_tag":"ask","q":{"_tag":"docx","at_":null}},"version":1}|}
;;

(* What a reply shows: "refused" for every refusal (its words are test_tool's to pin, against
   Lean's driver), or the served reply envelope's text. *)
let observe reply =
  if String.starts_with ~prefix:{|{"refused":|} reply then "refused" else reply
;;

let field k = function
  | J.NatJson_obj kvs -> List.assoc_opt k kvs
  | _ -> None
;;

(* The session's document after a served reply: its generation and revision (`now`). *)
let now_of reply =
  match Kit.Json.parse reply with
  | Error _ -> None
  | Ok j ->
    (match Option.bind (field "payload" j) (field "now") with
     | Some (J.NatJson_obj _ as now) ->
       (match
          Option.bind (field "doc" now) (field "generation"), field "revision" now
        with
        | Some (J.NatJson_nat g), Some (J.NatJson_nat r) -> Some (g, r)
        | _ -> None)
     | _ -> None)
;;

(* A reply as a counterexample prints it: the method, the result's tags, `now`, and the first
   twelve hexadecimal digits of the text's MD5, so two different texts print differently. The
   postcondition compares the whole text; this is the printer alone. *)
let summary reply =
  if String.equal reply "refused"
  then reply
  else (
    let tag j =
      match field "_tag" j with
      | Some (J.NatJson_str t) -> t
      | _ -> "-"
    in
    let digest = String.sub (Digest.to_hex (Digest.string reply)) 0 12 in
    match Kit.Json.parse reply with
    | Error _ -> "unparsed #" ^ digest
    | Ok j ->
      let meth =
        match field "method" j with
        | Some (J.NatJson_str m) -> m
        | _ -> "-"
      in
      let result = Option.bind (field "payload" j) (field "result") in
      let arg = Option.bind result (field "arg0") in
      let act = Option.bind arg (field "a") in
      let tags = List.filter_map (Option.map tag) [ result; arg; act ] in
      let now =
        match now_of reply with
        | Some (g, r) -> Printf.sprintf " now g%d r%d" g r
        | None -> ""
      in
      Printf.sprintf "%s %s%s #%s" meth (String.concat "/" tags) now digest)
;;

let reply_ty : string STM.ty_show = STM.String, summary

(* The oracle, memoised. A session state is named by its served requests, and the memo maps the
   name to Lean's session, so `next_state` and `postcond` stay pure functions of the model state
   while qcheck-stm's interleaving search asks them many times. Only the main domain asks: STM
   checks observations after the run's domains are joined. *)
type served =
  { name : string
  ; now : (int * int) option
  }

let sessions : (string, G.session) Hashtbl.t = Hashtbl.create 1024
let answers : (string, string * served option) Hashtbl.t = Hashtbl.create 4096
let start = { name = ""; now = None }
let () = Hashtbl.replace sessions start.name G.tool_native_start

let oracle (s : served) (r : req) =
  let key = s.name ^ "|" ^ show_req r in
  match Hashtbl.find_opt answers key with
  | Some a -> a
  | None ->
    let session = Hashtbl.find sessions s.name in
    let a =
      match Kit.Json.parse (line r) with
      | Error _ -> "refused", None
      | Ok json ->
        (match Kit.Json.read G.tool_native_envelope_shape json with
         | Error _ -> "refused", None
         | Ok v ->
           (match G.tool_native_serve_uncached session v with
            | Error _ -> "refused", None
            | Ok (reply, next) ->
              let text = J.render (J.print G.tool_native_reply_envelope_shape reply) in
              let name = s.name ^ ";" ^ show_req r in
              Hashtbl.replace sessions name next;
              text, Some { name; now = now_of text }))
    in
    Hashtbl.replace answers key a;
    a
;;

(* [shared]: both command tags address one session, as two domains sharing a Kit_tool.t would.
   [forgetful]: the shell serves each line on a fresh session. *)
module Spec (P : sig
    val shared : bool
    val forgetful : bool
  end) =
struct
  type cmd =
    { at : int
    ; req : req
    }

  let show_cmd c = Printf.sprintf "s%d %s" c.at (show_req c.req)
  let slot at = if P.shared then 0 else at

  type state = served list
  type sut = Kit_tool.t array

  let init_state = List.init (if P.shared then 1 else 2) (fun _ -> start)
  let arb_of g = QCheck.make ~print:show_cmd g

  let gen_req (s : served) =
    let g, r = Option.value s.now ~default:(0, 0) in
    QCheck.Gen.(
      oneof_weighted
        [ (if Option.is_none s.now then 6 else 1), map (fun v -> Open v) (int_bound 1)
        ; ( (if Option.is_some s.now then 6 else 1)
          , map (fun v -> Draft (g, r, v)) (int_bound 2) )
        ; 1, map3 (fun g r v -> Draft (g, r, v)) (int_bound 1) (int_bound 3) (int_bound 2)
        ; 1, return (Revert (g, r))
        ; 1, return Doc
        ; 1, return Doc0
        ; 1, return History
        ; 1, return Garbage
        ; 1, return Unreadable
        ])
  ;;

  let gen_at st at =
    QCheck.Gen.map (fun req -> { at; req }) (gen_req (List.nth st (slot at)))
  ;;

  let arb_cmd st = arb_of QCheck.Gen.(int_bound 1 >>= gen_at st)
  let arb_at at st = arb_of (gen_at st at)

  let next_state c st =
    match snd (oracle (List.nth st (slot c.at)) c.req) with
    | None -> st
    | Some next -> List.mapi (fun i x -> if i = slot c.at then next else x) st
  ;;

  let init_sut () = Array.init (if P.shared then 1 else 2) (fun _ -> Kit_tool.create ())
  let cleanup _ = ()
  let precond _ _ = true

  let serve sut c =
    let session = if P.forgetful then Kit_tool.create () else sut.(slot c.at) in
    observe (Kit_tool.serve_line session (line c.req))
  ;;

  let run c sut = STM.Res (STM.result reply_ty STM.exn, STM.protect (serve sut) c)

  let postcond c st (r : STM.res) =
    match r with
    | STM.Res ((STM.Result (STM.String, STM.Exn), _), (r : (string, exn) result)) ->
      (match r with
       | Ok a -> String.equal a (fst (oracle (List.nth st (slot c.at)) c.req))
       | Error _ -> false)
    | _ -> false
  ;;
end

module Two = Spec (struct
    let shared = false
    let forgetful = false
  end)

module Forgetful = Spec (struct
    let shared = false
    let forgetful = true
  end)

module Shared = Spec (struct
    let shared = true
    let forgetful = false
  end)

module Seq_two = STM_sequential.Make (Two)
module Seq_forgetful = STM_sequential.Make (Forgetful)
module Par_two = STM_domain.Make (Two)
module Par_shared = STM_domain.Make (Shared)

(* A0: from the start session, Open 0 is served; after it, a draft at generation 0 and revision
   0 moves the document to revision 1, and Open 1, Doc, Doc0, History and a revert are served;
   Garbage and Unreadable are refused. *)
let () =
  let served s r = snd (oracle s r) in
  let fail why =
    Printf.printf "FAIL A0 the request alphabet: %s\n%!" why;
    exit 1
  in
  match served start (Open 0) with
  | None -> fail "Open 0 is refused from the start session"
  | Some opened ->
    (match served opened (Draft (0, 0, 0)) with
     | Some { now = Some (0, 1); _ } -> ()
     | _ ->
       fail
         "a draft at generation 0 and revision 0 does not move the document to revision 1");
    List.iter
      (fun r ->
         if Option.is_none (served opened r)
         then fail (show_req r ^ " is refused after Open 0"))
      [ Open 1; Doc; Doc0; History; Revert (0, 0) ];
    List.iter
      (fun r -> if Option.is_some (served start r) then fail (show_req r ^ " is served"))
      [ Garbage; Unreadable ];
    print_endline
      "PASS A0 the request alphabet reads: seven requests served, Garbage and Unreadable \
       refused"
;;

let () =
  let open Stm_support in
  let own_domains = Par_two.arb_triple 10 8 Two.arb_cmd (Two.arb_at 0) (Two.arb_at 1) in
  let one_session =
    Par_shared.arb_triple 6 4 Shared.arb_cmd (Shared.arb_at 0) (Shared.arb_at 1)
  in
  run
    [ Seq_two.agree_test ~count:300 ~name:"S1 Kit_tool, two sessions, sequential"
    ; Seq_forgetful.neg_agree_test
        ~count:300
        ~name:"S2 red: a shell that serves each line on a fresh session"
    ; par_test
        ~neg:false
        ~name:"P1 Kit_tool, two sessions, each served by its own domain"
        ~count:60
        ~repeats:10
        ~ok:Par_two.all_interleavings_ok
        own_domains
        Par_two.agree_prop_par
    ; par_test
        ~retries:2
        ~neg:true
        ~name:"P2 red: one session served by two domains at once"
        ~count:100
        ~repeats:10
        ~ok:Par_shared.all_interleavings_ok
        one_session
        Par_shared.agree_prop_par
    ]
;;
