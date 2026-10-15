(* Effect's RPC protocol, served by OCaml, in four layers over two channels.

   Exploration probe (2026-10-15). Dependencies: eio_main, yojson. OCaml 5.1.1, Eio 1.2.
   The client is Effect's own `RpcClient` (effect 4.0.0-rc.112); the wire alphabet is
   effect/unstable/rpc/RpcMessage.

   The layers, bottom up. Only the first is native; the other three are data and functions of
   data, written once for every channel and every table.
   1. Channel: a duplex byte flow (a TCP connection) or one HTTP exchange.
   2. Framing: bytes to messages. NDJSON on the socket (one message per line); one JSON value
      per HTTP body, answered by a JSON array. Effect calls the difference `includesFraming`.
   3. Messages: the alphabet. From the client: Request, Ack, Interrupt, Ping, Eof. From the
      server: Exit (Success, or Failure with a cause of Fail, Die or Interrupt), Pong, Defect.
   4. Correlation: each Request runs in its own fiber, keyed by its id; answers carry the id, so
      calls on one connection finish in any order. An id in flight twice is refused, and an
      Interrupt cancels the fiber of its id.
   5. The host: rows, answered from state. *)

type json = Yojson.Safe.t

(* ----------------------------------------------------------------- 3. the message alphabet *)

type from_client =
  | Request of { id : json; tag : string; payload : json }
  | Ack of json
  | Interrupt of json
  | Ping
  | Eof
  | Unknown of string

type cause = Fail of json | Die of string | Interrupted

type from_server =
  | Exit_success of { request_id : json; value : json }
  | Exit_failure of { request_id : json; cause : cause }
  | Pong
  | Defect of string

let field k = function `Assoc kvs -> List.assoc_opt k kvs | _ -> None

let decode_client (v : json) : from_client =
  match field "_tag" v with
  | Some (`String "Request") ->
    (match field "id" v, field "tag" v with
     | Some id, Some (`String tag) ->
       Request { id; tag; payload = Option.value ~default:`Null (field "payload" v) }
     | _ -> Unknown "a Request without its id or tag")
  | Some (`String "Ack") -> Ack (Option.value ~default:`Null (field "requestId" v))
  | Some (`String "Interrupt") -> Interrupt (Option.value ~default:`Null (field "requestId" v))
  | Some (`String "Ping") -> Ping
  | Some (`String "Eof") -> Eof
  | _ -> Unknown (Yojson.Safe.to_string v)

let encode_server : from_server -> json = function
  | Exit_success { request_id; value } ->
    `Assoc [ "_tag", `String "Exit"; "requestId", request_id;
             "exit", `Assoc [ "_tag", `String "Success"; "value", value ] ]
  | Exit_failure { request_id; cause } ->
    let c = match cause with
      | Fail e -> `Assoc [ "_tag", `String "Fail"; "error", e ]
      | Die d -> `Assoc [ "_tag", `String "Die"; "defect", `String d ]
      | Interrupted -> `Assoc [ "_tag", `String "Interrupt"; "fiberId", `Null ] in
    `Assoc [ "_tag", `String "Exit"; "requestId", request_id;
             "exit", `Assoc [ "_tag", `String "Failure"; "cause", `List [ c ] ] ]
  | Pong -> `Assoc [ "_tag", `String "Pong" ]
  | Defect d -> `Assoc [ "_tag", `String "Defect"; "defect", `String d ]

(* ------------------------------------------------------------------------- 5. the host *)

(* A host answers a row: the tag and the payload in; a success, a failure, or no such row. *)
type answer = Ok of json | Failed of json | No_row

let todo_v (id, title, d) = `Assoc [ "id", `Int id; "title", `String title; "done", `Bool d ]
let sql_error m = `Assoc [ "_tag", `String "SqlError"; "message", `String m ]

let make_host ~clock =
  let next = ref 1 and items = ref [] in
  fun tag (payload : json) ->
    match tag, payload with
    | "insert", `String "boom" -> Failed (sql_error "disk full")
    | "insert", `String title ->
      let t = (!next, title, false) in incr next; items := !items @ [ t ]; Ok (todo_v t)
    | "all", _ -> Ok (`List (List.map todo_v !items))
    | "setDone", `List [ `Int id; `Bool d ] ->
      (match List.find_opt (fun (i, _, _) -> i = id) !items with
       | None -> Ok `Null
       | Some (_, title, _) ->
         items := List.map (fun ((i, _, _) as e) -> if i = id then (i, title, d) else e) !items;
         Ok (todo_v (id, title, d)))
    | "delete", `Int id ->
      let had = List.exists (fun (i, _, _) -> i = id) !items in
      items := List.filter (fun (i, _, _) -> i <> id) !items; Ok (`Bool had)
    | "echoAfter", `List [ `Int ms; `String text ] ->
      Eio.Time.sleep clock (float_of_int ms /. 1000.); Ok (`String text)
    | _ -> No_row

(* --------------------------------------------------------------------- 4. correlation *)

(* One connection's calls in flight, by id. `run` answers one Request through `reply`. *)
type session = { in_flight : (string, Eio.Cancel.t) Hashtbl.t; log : string -> unit }

let key (id : json) = Yojson.Safe.to_string id

let run_request ~sw session host reply id tag payload =
  if Hashtbl.mem session.in_flight (key id) then
    reply (Defect (Printf.sprintf "request id %s is already in flight" (key id)))
  else
    Eio.Fiber.fork ~sw (fun () ->
        let outcome =
          try
            Eio.Cancel.sub (fun ctx ->
                Hashtbl.replace session.in_flight (key id) ctx;
                Fun.protect ~finally:(fun () -> Hashtbl.remove session.in_flight (key id))
                  (fun () -> `Answer (host tag payload)))
          with Eio.Cancel.Cancelled _ -> `Interrupted in
        match outcome with
        | `Answer (Ok value) -> reply (Exit_success { request_id = id; value })
        | `Answer (Failed e) -> reply (Exit_failure { request_id = id; cause = Fail e })
        | `Answer No_row -> reply (Exit_failure { request_id = id; cause = Die ("no row " ^ tag) })
        | `Interrupted ->
          session.log (Printf.sprintf "  interrupt: id %s cancelled" (key id));
          reply (Exit_failure { request_id = id; cause = Interrupted }))

let handle ~sw session host reply = function
  | Request { id; tag; payload } ->
    session.log (Printf.sprintf "  request id %s %s %s" (key id) tag (Yojson.Safe.to_string payload));
    run_request ~sw session host reply id tag payload
  | Interrupt id ->
    (match Hashtbl.find_opt session.in_flight (key id) with
     | Some ctx -> Eio.Cancel.cancel ctx (Failure "interrupted by the client")
     | None -> ())
  | Ping -> reply Pong
  | Ack _ | Eof -> ()
  | Unknown what -> reply (Defect ("not a client message: " ^ what))

(* --------------------------------------------------------------- 2. framing, 1. channels *)

(* The socket edge: NDJSON over one long-lived connection, replies serialized by a mutex. *)
let serve_socket ~clock host flow addr =
  Eio.Switch.run @@ fun sw ->
  let peer = Format.asprintf "%a" Eio.Net.Sockaddr.pp addr in
  let session = { in_flight = Hashtbl.create 8; log = (fun s -> Printf.printf "[socket %s]%s\n%!" peer s) } in
  ignore clock;
  let lock = Eio.Mutex.create () in
  let reply m =
    let line = Yojson.Safe.to_string (encode_server m) ^ "\n" in
    session.log ("  reply " ^ String.trim line);
    Eio.Mutex.use_rw ~protect:true lock (fun () -> Eio.Flow.copy_string line flow) in
  let r = Eio.Buf_read.of_flow flow ~max_size:(1 lsl 20) in
  let rec loop () =
    match Eio.Buf_read.line r with
    | exception End_of_file -> session.log "  closed"
    | "" -> loop ()
    | line ->
      (match Yojson.Safe.from_string line with
       | v -> handle ~sw session host reply (decode_client v)
       | exception Yojson.Json_error e -> reply (Defect ("not JSON: " ^ e)));
      loop () in
  loop ()

(* The HTTP edge: one POST, one JSON value (or array) in, a JSON array of replies out. Every
   request is answered before the response is written, so correlation is per exchange. *)
let serve_http host flow _addr =
  Eio.Switch.run @@ fun sw ->
  let session = { in_flight = Hashtbl.create 8; log = (fun s -> Printf.printf "[http]%s\n%!" s) } in
  let r = Eio.Buf_read.of_flow flow ~max_size:(1 lsl 20) in
  let rec loop () =
    match Eio.Buf_read.line r with
    | exception End_of_file -> ()
    | _start ->
      let rec headers n = match Eio.Buf_read.line r with
        | "" -> n
        | h -> (match String.index_opt h ':' with
            | Some i when String.lowercase_ascii (String.sub h 0 i) = "content-length" ->
              headers (int_of_string (String.trim (String.sub h (i + 1) (String.length h - i - 1))))
            | _ -> headers n) in
      let n = headers 0 in
      let body = if n > 0 then Eio.Buf_read.take n r else "" in
      let replies = ref [] in
      let reply m = replies := encode_server m :: !replies in
      Eio.Switch.run (fun inner ->
          match Yojson.Safe.from_string body with
          | `List vs -> List.iter (fun v -> handle ~sw:inner session host reply (decode_client v)) vs
          | v -> handle ~sw:inner session host reply (decode_client v)
          | exception Yojson.Json_error e -> reply (Defect ("not JSON: " ^ e)));
      let out = Yojson.Safe.to_string (`List (List.rev !replies)) in
      session.log ("  reply " ^ out);
      Eio.Flow.copy_string (Printf.sprintf
        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: %d\r\n\r\n%s"
        (String.length out) out) flow;
      ignore sw;
      loop () in
  loop ()

let () =
  let socket_port = try int_of_string Sys.argv.(1) with _ -> 8475 in
  let http_port = try int_of_string Sys.argv.(2) with _ -> 8476 in
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let net = Eio.Stdenv.net env and clock = Eio.Stdenv.clock env in
  let listen port = Eio.Net.listen ~sw ~reuse_addr:true ~backlog:16 net (`Tcp (Eio.Net.Ipaddr.V4.loopback, port)) in
  let on_error e = Printf.printf "connection error: %s\n%!" (Printexc.to_string e) in
  (* Each channel gets its own host state, so the two runs start alike. *)
  let socket_host = make_host ~clock and http_host = make_host ~clock in
  Printf.printf "effect_rpc: NDJSON socket on 127.0.0.1:%d, HTTP on 127.0.0.1:%d\n%!" socket_port http_port;
  Eio.Fiber.both
    (fun () -> Eio.Net.run_server (listen socket_port) (serve_socket ~clock socket_host) ~on_error)
    (fun () -> Eio.Net.run_server (listen http_port) (serve_http http_host) ~on_error)
