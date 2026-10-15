(* The to-do application over HTTP, served by OCaml on Eio, for an Effect HttpApi client.

   Exploration probe (2026-10-15). Dependencies: eio_main, yojson. OCaml 5.1.1, Eio 1.2.

   Three layers, each one a stand-in for what the generator would supply:
   1. The host: the repository's four rows (Test/Dogfood/Scenario/Todo.lean, `eff_rows TodoRepo`),
      answered from memory as the reference `repository` reactor answers them.
   2. The program: the four entries (`add`, `list`, `complete`, `remove`), transcribed from their
      Eff programs. In P1 these are the lowered machine's `serve`, not hand OCaml.
   3. The edge: a route table, as data, from HTTP to entries; failures are tagged records with the
      status that Effect's `httpApiStatus` annotation names.

   The HTTP/1.1 reader is the smallest one that serves fetch: request line, headers,
   Content-Length bodies, keep-alive. A real deployment uses an HTTP library over Eio. *)

(* ---------------------------------------------------------------- 1. the host: four rows *)

type todo = { id : int; title : string; done_ : bool }

let todo_json t = `Assoc [ "id", `Int t.id; "title", `String t.title; "done", `Bool t.done_ ]

module Repo = struct
  type t = { mutable next : int; mutable items : todo list; mutable calls : string list }
  let create () = { next = 1; items = []; calls = [] }
  let log r row = r.calls <- row :: r.calls
  (* TodoRepo.insert(.string) : Todo.ty *)
  let insert r title =
    log r "TodoRepo.insert";
    let t = { id = r.next; title; done_ = false } in
    r.next <- r.next + 1; r.items <- r.items @ [ t ]; t
  (* TodoRepo.all(.unit) : .list Todo.ty *)
  let all r = log r "TodoRepo.all"; r.items
  (* TodoRepo.setDone(.prod .nat .bool) : .option Todo.ty *)
  let set_done r id d =
    log r "TodoRepo.setDone";
    match List.find_opt (fun t -> t.id = id) r.items with
    | None -> None
    | Some t ->
      let t' = { t with done_ = d } in
      r.items <- List.map (fun x -> if x.id = id then t' else x) r.items; Some t'
  (* TodoRepo.delete(.nat) : .bool *)
  let delete r id =
    log r "TodoRepo.delete";
    let had = List.exists (fun t -> t.id = id) r.items in
    r.items <- List.filter (fun t -> t.id <> id) r.items; had
end

(* ------------------------------------------------------------ 2. the program: four entries *)

(* A failure is a tagged record, as `eff_failure` declares it, with its HTTP status. *)
type failure = { tag : string; fields : (string * Yojson.Safe.t) list; status : int }

type outcome = Success of Yojson.Safe.t option | Failure of failure

let empty_title = { tag = "EmptyTitle"; fields = [ "message", `String "a title is required" ]; status = 400 }
let not_found id = { tag = "NotFound"; fields = [ "id", `Int id ]; status = 404 }

(* add(title): an empty title fails and asks the repository nothing. *)
let add repo title =
  if title = "" then Failure empty_title else Success (Some (todo_json (Repo.insert repo title)))

(* list(): every to-do. *)
let list repo = Success (Some (`List (List.map todo_json (Repo.all repo))))

(* complete(id): the to-do, marked done; a missing one fails with its id. *)
let complete repo id =
  match Repo.set_done repo id true with
  | Some t -> Success (Some (todo_json t))
  | None -> Failure (not_found id)

(* remove(id): a missing to-do fails with its id. Unit is HttpApi's NoContent. *)
let remove repo id = if Repo.delete repo id then Success None else Failure (not_found id)

(* -------------------------------------------------------------- 3. the edge: routes as data *)

type request = { meth : string; path : string list; content_type : string option; body : string }

(* One route: a method, a path pattern (":id" binds a natural), and the entry it runs. *)
type route = { r_meth : string; r_path : string list; entry : Repo.t -> (string * int) list -> request -> outcome }

(* Effect's HttpApi encodes a payload given as a field list as a form (`title=milk`), and a
   payload given as a schema as JSON: the description, not the server, picks the encoding. *)
let percent_decode s =
  let b = Buffer.create (String.length s) in
  let rec go i =
    if i < String.length s then
      match s.[i] with
      | '+' -> Buffer.add_char b ' '; go (i + 1)
      | '%' when i + 2 < String.length s ->
        (match int_of_string_opt ("0x" ^ String.sub s (i + 1) 2) with
         | Some c -> Buffer.add_char b (Char.chr c); go (i + 3)
         | None -> Buffer.add_char b '%'; go (i + 1))
      | c -> Buffer.add_char b c; go (i + 1) in
  go 0; Buffer.contents b

let form_fields body =
  List.filter_map (fun kv -> match String.index_opt kv '=' with
      | Some i -> Some (percent_decode (String.sub kv 0 i),
                        percent_decode (String.sub kv (i + 1) (String.length kv - i - 1)))
      | None -> None) (String.split_on_char '&' body)

let payload_title ~content_type body =
  if content_type = Some "application/x-www-form-urlencoded" then List.assoc_opt "title" (form_fields body)
  else match Yojson.Safe.from_string body with
    | `Assoc fields -> (match List.assoc_opt "title" fields with Some (`String s) -> Some s | _ -> None)
    | _ -> None
    | exception Yojson.Json_error _ -> None

let bad_request what = Failure { tag = "BadRequest"; fields = [ "message", `String what ]; status = 400 }

let routes = [
  { r_meth = "POST"; r_path = [ "todos" ];
    entry = (fun repo _ req -> match payload_title ~content_type:req.content_type req.body with
      | Some t -> add repo t | None -> bad_request "payload: { title: string }") };
  { r_meth = "GET"; r_path = [ "todos" ]; entry = (fun repo _ _ -> list repo) };
  { r_meth = "POST"; r_path = [ "todos"; ":id"; "complete" ];
    entry = (fun repo params _ -> complete repo (List.assoc "id" params)) };
  { r_meth = "DELETE"; r_path = [ "todos"; ":id" ];
    entry = (fun repo params _ -> remove repo (List.assoc "id" params)) };
]

(* Match a path against a pattern; a ":name" segment must be a natural in OCaml's int range. *)
let rec bind pattern path acc =
  match pattern, path with
  | [], [] -> Some (List.rev acc)
  | p :: ps, s :: ss when String.length p > 0 && p.[0] = ':' ->
    (match int_of_string_opt s with
     | Some n when n >= 0 -> bind ps ss ((String.sub p 1 (String.length p - 1), n) :: acc)
     | _ -> None)
  | p :: ps, s :: ss when p = s -> bind ps ss acc
  | _ -> None

let dispatch repo req =
  let found = List.find_map (fun r ->
      if r.r_meth <> req.meth then None
      else Option.map (fun params -> (r, params)) (bind r.r_path req.path [])) routes in
  match found with
  | None -> Failure { tag = "RouteNotFound"; fields = []; status = 404 }
  | Some (r, params) -> r.entry repo params req

(* ------------------------------------------------------------------------ HTTP/1.1 on Eio *)

let reason = function
  | 200 -> "OK" | 204 -> "No Content" | 400 -> "Bad Request" | 404 -> "Not Found" | _ -> "Error"

let respond flow status body =
  let head = Printf.sprintf "HTTP/1.1 %d %s\r\nContent-Length: %d\r\n%s\r\n" status (reason status)
      (String.length body) (if body = "" then "" else "Content-Type: application/json\r\n") in
  Eio.Flow.copy_string (head ^ body) flow

let split_path target =
  let path = match String.index_opt target '?' with Some i -> String.sub target 0 i | None -> target in
  List.filter (fun s -> s <> "") (String.split_on_char '/' path)

let read_request r =
  let line = Eio.Buf_read.line r in
  match String.split_on_char ' ' line with
  | [ meth; target; _version ] ->
    let rec headers acc =
      match Eio.Buf_read.line r with
      | "" -> acc
      | h -> (match String.index_opt h ':' with
          | Some i -> headers ((String.lowercase_ascii (String.sub h 0 i),
                                String.trim (String.sub h (i + 1) (String.length h - i - 1))) :: acc)
          | None -> headers acc) in
    let hs = headers [] in
    (* A chunked body: hexadecimal sizes, each chunk and its CRLF, closed by a zero chunk. *)
    let rec chunks acc =
      let size = int_of_string ("0x" ^ String.trim (Eio.Buf_read.line r)) in
      if size = 0 then (ignore (Eio.Buf_read.line r); String.concat "" (List.rev acc))
      else begin
        let chunk = Eio.Buf_read.take size r in
        ignore (Eio.Buf_read.line r);
        chunks (chunk :: acc)
      end in
    let body =
      if List.assoc_opt "transfer-encoding" hs = Some "chunked" then chunks []
      else match Option.bind (List.assoc_opt "content-length" hs) int_of_string_opt with
        | Some n when n > 0 -> Eio.Buf_read.take n r
        | _ -> "" in
    let content_type = Option.map (fun v -> String.trim (List.hd (String.split_on_char ';' v)))
        (List.assoc_opt "content-type" hs) in
    Some { meth; path = split_path target; content_type; body }
  | _ -> None

let handle repo flow _addr =
  let r = Eio.Buf_read.of_flow flow ~max_size:(1 lsl 20) in
  let rec loop () =
    match read_request r with
    | exception End_of_file -> ()
    | None -> respond flow 400 ""
    | Some req ->
      let status, body =
        match dispatch repo req with
        | Success None -> 204, ""
        | Success (Some json) -> 200, Yojson.Safe.to_string json
        | Failure f -> f.status, Yojson.Safe.to_string (`Assoc (("_tag", `String f.tag) :: f.fields)) in
      Printf.printf "%-6s /%s -> %d %s\n%!" req.meth (String.concat "/" req.path) status body;
      respond flow status body;
      loop () in
  loop ()

let () =
  let port = try int_of_string Sys.argv.(1) with _ -> 8471 in
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let repo = Repo.create () in
  let socket = Eio.Net.listen ~sw ~reuse_addr:true ~backlog:16 (Eio.Stdenv.net env)
      (`Tcp (Eio.Net.Ipaddr.V4.loopback, port)) in
  Printf.printf "todo_http: listening on 127.0.0.1:%d\n%!" port;
  Eio.Net.run_server socket (handle repo)
    ~on_error:(fun e -> Printf.printf "connection error: %s\n%!" (Printexc.to_string e))
