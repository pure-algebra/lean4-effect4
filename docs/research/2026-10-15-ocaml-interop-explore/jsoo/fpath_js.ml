(* The generated Fpath host, compiled to JavaScript by js_of_ocaml: the same rows, answered
   in-process, with no HTTP. The guard is the same one the HTTP edge applies.

   Exploration probe (2026-10-15). Dependencies: js_of_ocaml, js_of_ocaml-ppx, yojson, fpath. *)
open Js_of_ocaml

let () =
  Js.export "fpathHost"
    (object%js
      (* The table, as the HTTP edge answers GET /rows. *)
      method table = Js.string (Yojson.Safe.to_string (`List (List.map Rows_core.row_json Fpath_host.table)))
      (* One call, as the HTTP edge answers POST /rows/<spelling>: a completion, or null. *)
      method call (spelling : Js.js_string Js.t) (request : Js.js_string Js.t) =
        let answer =
          match Yojson.Safe.from_string (Js.to_string request) with
          | exception Yojson.Json_error _ -> None
          | r ->
            (match List.find_opt (fun row -> row.Rows_core.spelling = Js.to_string spelling) Fpath_host.table with
             | Some row when Rows_core.refusal "$" row.request r = None ->
               Rows_core.guard Fpath_host.table Fpath_host.host (Js.to_string spelling) r
             | _ -> None) in
        match answer with
        | Some c -> Js.some (Js.string (Yojson.Safe.to_string (Rows_core.completion_json c)))
        | None -> Js.null
    end)
