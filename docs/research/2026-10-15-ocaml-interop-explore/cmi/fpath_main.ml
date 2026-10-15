(* Serve the generated Fpath host (fpath_host.ml, from cmi_rows) through the generic transport.
   Exploration probe (2026-10-15). Dependencies: eio_main, yojson, fpath. *)
let () =
  let port = try int_of_string Sys.argv.(1) with _ -> 8474 in
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let socket = Eio.Net.listen ~sw ~reuse_addr:true ~backlog:16 (Eio.Stdenv.net env)
      (`Tcp (Eio.Net.Ipaddr.V4.loopback, port)) in
  Printf.printf "fpath host: %d rows on 127.0.0.1:%d\n%!" (List.length Fpath_host.table) port;
  Eio.Net.run_server socket (Transport.serve Fpath_host.table Fpath_host.host)
    ~on_error:(fun e -> Printf.printf "connection error: %s\n%!" (Printexc.to_string e))
