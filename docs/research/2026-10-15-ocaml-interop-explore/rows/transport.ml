(* Transport: the HTTP half of the row transport, over Rows_core. Exploration probe (2026-10-15).
   Dependencies: eio_main, yojson. *)

include Rows_core

(* -------------------------------------------------------- HTTP/1.1: reading and writing *)

let read_message r =
  let start = Eio.Buf_read.line r in
  let rec headers acc = match Eio.Buf_read.line r with
    | "" -> acc
    | h -> (match String.index_opt h ':' with
        | Some i -> headers ((String.lowercase_ascii (String.sub h 0 i),
                              String.trim (String.sub h (i + 1) (String.length h - i - 1))) :: acc)
        | None -> headers acc) in
  let hs = headers [] in
  let rec chunks acc =
    let size = int_of_string ("0x" ^ String.trim (Eio.Buf_read.line r)) in
    if size = 0 then (ignore (Eio.Buf_read.line r); String.concat "" (List.rev acc))
    else (let c = Eio.Buf_read.take size r in ignore (Eio.Buf_read.line r); chunks (c :: acc)) in
  let body =
    if List.assoc_opt "transfer-encoding" hs = Some "chunked" then chunks []
    else match Option.bind (List.assoc_opt "content-length" hs) int_of_string_opt with
      | Some n when n > 0 -> Eio.Buf_read.take n r | _ -> "" in
  (start, body)

let write_response flow status body =
  Eio.Flow.copy_string (Printf.sprintf
    "HTTP/1.1 %d X\r\nContent-Type: application/json\r\nAccess-Control-Allow-Origin: *\r\nContent-Length: %d\r\n\r\n%s"
    status (String.length body) body) flow

(* --------------------------------------------------------------- the server half: `serve` *)

let serve table (host : host) flow _addr =
  let r = Eio.Buf_read.of_flow flow ~max_size:(1 lsl 20) in
  let rec loop () =
    match read_message r with
    | exception End_of_file -> ()
    | (start, body) ->
      let status, out =
        match String.split_on_char ' ' start with
        | [ "GET"; "/rows"; _ ] -> 200, `List (List.map row_json table)
        | [ "POST"; target; _ ] when String.length target > 6 && String.sub target 0 6 = "/rows/" ->
          let spelling = String.sub target 6 (String.length target - 6) in
          (match List.find_opt (fun row -> row.spelling = spelling) table,
                 (try Some (Yojson.Safe.from_string body) with Yojson.Json_error _ -> None) with
           | None, _ -> 404, `Assoc [ "_tag", `String "NoSuchRow"; "row", `String spelling ]
           | _, None -> 400, `Assoc [ "_tag", `String "NotJson" ]
           | Some row, Some request ->
             match refusal "$" row.request request with
             | Some why -> 422, `Assoc [ "_tag", `String "RequestRefused"; "at", `String why ]
             | None ->
               match guard table host spelling request with
               | Some c -> 200, completion_json c
               | None -> 502, `Assoc [ "_tag", `String "NoAdmittedAnswer"; "row", `String spelling ])
        | _ -> 404, `Assoc [ "_tag", `String "NoRoute" ] in
      write_response flow status (Yojson.Safe.to_string out);
      loop () in
  loop ()

(* -------------------------------------------------------------- the client half: `remote` *)

let remote ~sw net port : host = fun spelling request ->
  let flow = Eio.Net.connect ~sw net (`Tcp (Eio.Net.Ipaddr.V4.loopback, port)) in
  let body = Yojson.Safe.to_string request in
  Eio.Flow.copy_string (Printf.sprintf
    "POST /rows/%s HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Type: application/json\r\nContent-Length: %d\r\n\r\n%s"
    spelling (String.length body) body) flow;
  let start, out = read_message (Eio.Buf_read.of_flow flow ~max_size:(1 lsl 20)) in
  Eio.Flow.close flow;
  match String.split_on_char ' ' start, Yojson.Safe.from_string out with
  | _ :: "200" :: _, `Assoc [ "_tag", `String "Success"; "value", v ] -> Some (Success v)
  | _ :: "200" :: _, `Assoc [ "_tag", `String "Failure"; "error", e ] -> Some (Failure e)
  | _ -> None

