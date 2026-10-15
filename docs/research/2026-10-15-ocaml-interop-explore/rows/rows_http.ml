(* The to-do's four rows behind the generic transport (transport.ml): a self-test of the law
   `remote table url` against `serve table host` answers as `host` does, and a server mode.

   Exploration probe (2026-10-15). Dependencies: eio_main, yojson. OCaml 5.1.1, Eio 1.2. *)

open Transport

(* ------------------------------------------------------- one table: the to-do's four rows *)

let todo = Record [ "id", Nat; "title", Str; "done", Bool ]
let sql_error = Record [ "_tag", Str; "message", Str ]

let todo_rows = [
  { spelling = "TodoRepo.insert"; request = Str; answer = todo; error = sql_error };
  { spelling = "TodoRepo.all"; request = Unit; answer = List todo; error = sql_error };
  { spelling = "TodoRepo.setDone"; request = Prod (Nat, Bool); answer = Option todo; error = sql_error };
  { spelling = "TodoRepo.delete"; request = Nat; answer = Bool; error = sql_error };
]

(* The reference repository, as Test/Dogfood/Scenario/Todo.lean's `repository` answers. *)
let memory_repository () : host =
  let next = ref 1 and items = ref [] in
  let todo_v (id, title, d) = `Assoc [ "id", `Int id; "title", `String title; "done", `Bool d ] in
  fun spelling request ->
    match spelling, request with
    | "TodoRepo.insert", `String title ->
      let t = (!next, title, false) in incr next; items := !items @ [ t ]; Some (Success (todo_v t))
    | "TodoRepo.all", `Null -> Some (Success (`List (List.map todo_v !items)))
    | "TodoRepo.setDone", `List [ `Int id; `Bool d ] ->
      (match List.find_opt (fun (i, _, _) -> i = id) !items with
       | None -> Some (Success `Null)
       | Some (_, title, _) ->
         items := List.map (fun ((i, _, _) as e) -> if i = id then (i, title, d) else e) !items;
         Some (Success (todo_v (id, title, d))))
    | "TodoRepo.delete", `Int id ->
      let had = List.exists (fun (i, _, _) -> i = id) !items in
      items := List.filter (fun (i, _, _) -> i <> id) !items; Some (Success (`Bool had))
    | _ -> None

(* A host that breaks its row: `delete` answers a string. The guard must refuse it. *)
let lying_repository () : host =
  let honest = memory_repository () in
  fun spelling request ->
    if spelling = "TodoRepo.delete" then Some (Success (`String "yes")) else honest spelling request

let script = [
  "TodoRepo.insert", `String "milk"; "TodoRepo.insert", `String "tea";
  "TodoRepo.setDone", `List [ `Int 1; `Bool true ]; "TodoRepo.setDone", `List [ `Int 9; `Bool true ];
  "TodoRepo.delete", `Int 2; "TodoRepo.all", `Null;
]

let show = function
  | None -> "no answer"
  | Some c -> Yojson.Safe.to_string (completion_json c)

let check name ok = if not ok then failwith ("FAILED: " ^ name); Printf.printf "PASS %s\n%!" name

let raw_post ~sw net port spelling body =
  let flow = Eio.Net.connect ~sw net (`Tcp (Eio.Net.Ipaddr.V4.loopback, port)) in
  Eio.Flow.copy_string (Printf.sprintf
    "POST /rows/%s HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Length: %d\r\n\r\n%s"
    spelling (String.length body) body) flow;
  let start, out = read_message (Eio.Buf_read.of_flow flow ~max_size:(1 lsl 20)) in
  Eio.Flow.close flow; (start, out)

let listen ~sw net port =
  Eio.Net.listen ~sw ~reuse_addr:true ~backlog:16 net (`Tcp (Eio.Net.Ipaddr.V4.loopback, port))

let on_error e = Printf.printf "connection error: %s\n%!" (Printexc.to_string e)

let () =
  let mode = try Sys.argv.(1) with _ -> "selftest" in
  let port = try int_of_string Sys.argv.(2) with _ -> 8473 in
  Eio_main.run @@ fun env ->
  let net = Eio.Stdenv.net env in
  Eio.Switch.run @@ fun sw ->
  match mode with
  | "serve" ->
    Printf.printf "rows_http: serving %d rows on 127.0.0.1:%d\n%!" (List.length todo_rows) port;
    Eio.Net.run_server (listen ~sw net port) (serve todo_rows (memory_repository ())) ~on_error
  | _ ->
    (* The server half runs in a fiber of this process; the client half calls it. *)
    let honest_port = port and lying_port = port + 1 in
    Eio.Fiber.fork_daemon ~sw (fun () ->
        Eio.Net.run_server (listen ~sw net honest_port) (serve todo_rows (memory_repository ())) ~on_error);
    Eio.Fiber.fork_daemon ~sw (fun () ->
        Eio.Net.run_server (listen ~sw net lying_port) (serve todo_rows (lying_repository ())) ~on_error);
    let local = guard todo_rows (memory_repository ()) in
    let over_http = remote ~sw net honest_port in
    List.iter (fun (spelling, request) ->
        let a = local spelling request and b = over_http spelling request in
        Printf.printf "%-17s %-22s local %s\n%-40s http  %s\n%!" spelling (Yojson.Safe.to_string request)
          (show a) "" (show b);
        check ("the host behind HTTP answers " ^ spelling ^ " as the host does") (a = b)) script;
    let start, out = raw_post ~sw net honest_port "TodoRepo.insert" "42" in
    Printf.printf "insert 42           -> %s %s\n%!" start out;
    check "a request outside the row's type is refused, with its path" (String.length start > 12
      && String.sub start 9 3 = "422");
    let start, out = raw_post ~sw net honest_port "TodoRepo.setDone" "[-1, true]" in
    Printf.printf "setDone [-1, true]  -> %s %s\n%!" start out;
    check "a negative natural inside a pair is refused at its position" (String.sub start 9 3 = "422");
    let start, out = raw_post ~sw net lying_port "TodoRepo.delete" "2" in
    Printf.printf "lying delete 2      -> %s %s\n%!" start out;
    check "the guard refuses a host answer outside the row's answer type (red control)"
      (String.sub start 9 3 = "502");
    print_endline "ALL ROW TRANSPORT PROBES PASSED"
