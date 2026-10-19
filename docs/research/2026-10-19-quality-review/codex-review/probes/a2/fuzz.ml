open Effect4_engine_cas
open Effect4_kit
module G = Effect4_gen.Api_gen
let root = Filename.dirname Sys.argv.(0)
let save path s = let o = open_out_bin path in output_string o s; close_out o
let get path = let i = open_in_bin path in let s = really_input_string i (in_channel_length i) in close_in i; s
let mkdir p = if not (Sys.file_exists p) then Unix.mkdir p 0o755
let bytes s = List.init (String.length s) (fun i -> Char.code s.[i])
let frame tag s = String.make 1 (Char.chr tag) ^ E4_be.be64 (String.length s) ^ s
let zero = E4_addr.Addr.of_digest (String.make 32 '\000')
let disk = Filename.concat root "fuzz-data"
let packdir = Filename.concat disk "pack"
let indexpath = Filename.concat disk "index"
let walpath () = Filename.concat (E4_wal.job_dir ~dir:disk ~job:zero) (E4_wal.segment_name 0)
let setup () =
 mkdir disk; mkdir packdir;
 let w = E4_pack.open_ ~dir:disk ~seg_max:4096 in
 let b = "test node" in ignore (E4_pack.append w ~digest:(E4_sha256.digest b) ~node_bytes:b); E4_pack.commit w; E4_pack.close w;
 let w = E4_wal.open_ ~dir:disk ~job:zero ~seg_max:4096 in ignore (E4_wal.append w (E4_wal.Decision "test")); E4_wal.commit w; E4_wal.close w;
 E4_index.save ~path:indexpath (E4_index.create ~slots:16) ~covers:(0,0)
let diskread mode s =
 match mode with
 | "index" -> (if Sys.file_exists indexpath then Unix.unlink indexpath); save indexpath s; ignore(E4_index.load ~path:indexpath)
 | "pack" ->
   save (E4_pack.seg_path ~dir:disk 0) s;
   let r=E4_pack.open_reader ~dir:disk in Fun.protect ~finally:(fun () -> E4_pack.close_reader r) (fun () -> ignore(E4_pack.read r ~seg:0 ~off:E4_pack.head_length); ignore(E4_pack.scan r ~from:(0,E4_pack.head_length) ~f:(fun _ _ _ _ -> ())))
 | "wal" ->
   save (walpath ()) s;
   let r=E4_wal.open_reader ~dir:disk ~job:zero in Fun.protect ~finally:(fun () -> E4_wal.close_reader r) (fun () -> ignore(E4_wal.replay r ~from:0 ~f:(fun _ _ -> ())))
 | _ -> assert false
let run mode s = match mode with
 | "frame" -> ignore(Eff_frame.read_frame s 0 (String.length s)); ignore(Eff_frame.exact Eff_frame.decode_nat s); ignore(Eff_frame.exact Eff_frame.decode_string s); ignore(Eff_frame.exact (Eff_frame.decode_list Eff_frame.decode_nat) s)
 | "wire" -> ignore(Eff_wire.decode_ty_exact s); ignore(Eff_wire.decode_program_exact s)
 | "shape" -> List.iter (fun k -> ignore(E4_shape.cids_of_checked E4_shape.table k ~payload:s); ignore(E4_shape.refs_of_checked E4_shape.table k ~payload:s); ignore(E4_shape.stamps_of_checked E4_shape.table k ~payload:s)) E4_kind.all
 | "node" -> ignore(E4_node.decode s); ignore(E4_node.scan_payload s)
 | "control" -> ignore(E4_control.decode s)
 | "json" -> ignore(Kit.Json.parse s)
 | "nat_json" -> ignore(G.nat_json_parse (bytes s))
 | "mcp" -> ignore(Kit_mcp.line (Kit_mcp.create ()) s)
 | "pack" | "wal" | "index" -> diskread mode s
 | _ -> failwith mode
let program = Result.get_ok (Kit_author.build Kit_author.(succeed (nat 1)))
let program_wire = Eff_wire.encode_program program
let node_wire = E4_node.encode (E4_node.make ~version:0 ~kind:E4_kind.Program ~spec:E4_node.zero_digest ~payload:program_wire)
let seeds mode =
 match mode with
 | "shape" -> [program_wire]
 | "node" -> [node_wire]
 | "frame" -> [""; frame 9 ""; frame 2 "\001"; frame 4 (frame 9 ""); "\000\001" ^ String.make 32 '\000' ^ frame 9 "" ]
 | "wire" -> [""; Eff_wire.encode_ty Eff_types.Ty.Nat; Eff_wire.encode_ty (Eff_types.Ty.List Eff_types.Ty.Nat); program_wire]
 | "control" -> [""; E4_control.encode E4_control.initial]
 | "index" -> [get indexpath]
 | "pack" -> [get (E4_pack.seg_path ~dir:disk 0)]
 | "wal" -> [get (walpath ())]
 | _ -> [""; "0"; "null"; "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"ping\"}"; "[0,1,{\"a\":true}]"; "\"abc\""]
let () =
 Printexc.record_backtrace true;
 let mode = Sys.argv.(1) in
 if mode = "setup" then setup ()
 else if Array.length Sys.argv > 2 && Sys.argv.(2) = "file" then (try run mode (get Sys.argv.(3)); print_endline "returned" with e -> Printf.printf "EXCEPTION %s\n%s\n" (Printexc.to_string e) (Printexc.get_backtrace()); exit 2)
 else (
  let rng=Random.State.make [|3471;20261019|] in
  let count=ref 0 and failures=ref 0 in
  let test label s = incr count; try run mode s with e -> incr failures; let fn=Filename.concat root (Printf.sprintf "%s-failure-%d.bin" mode !failures) in save fn s; Printf.printf "%s %s EXCEPTION %s input=%s\n%!" mode label (Printexc.to_string e) fn in
  let starts=seeds mode in
  List.iter (fun s -> test "seed" s; for i=0 to String.length s do test "truncate" (String.sub s 0 i) done; for i=0 to String.length s - 1 do List.iter(fun bit -> let b=Bytes.of_string s in Bytes.set b i (Char.chr(Char.code(Bytes.get b i) lxor bit)); test "flip" (Bytes.to_string b)) [1;128;255] done) starts;
  for n=1 to 1000 do let s=List.nth starts (Random.State.int rng (List.length starts)) in let b=Bytes.of_string s in for _=1 to 1+Random.State.int rng 4 do if Bytes.length b>0 then Bytes.set b (Random.State.int rng (Bytes.length b)) (Char.chr(Random.State.int rng 256)) done; test "mutate" (Bytes.to_string b) done;
  for n=1 to 1000 do test "random" (String.init (Random.State.int rng 513) (fun _ -> Char.chr(Random.State.int rng 256))) done;
  Printf.printf "%s cases=%d exceptions=%d seed=3471,20261019\n" mode !count !failures)
