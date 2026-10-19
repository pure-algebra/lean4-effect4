open Effect4_engine_cas
let save p s=let o=open_out_bin p in Fun.protect ~finally:(fun()->close_out o) (fun()->output_string o s)
let get p=let i=open_in_bin p in Fun.protect ~finally:(fun()->close_in i) (fun()->really_input_string i (in_channel_length i))
let root=Filename.dirname Sys.argv.(0)
let dir=Filename.concat root "pack-boundary-data"
let ()=
 if not(Sys.file_exists dir) then Unix.mkdir dir 0o755;
 let w=E4_pack.open_ ~dir ~seg_max:4096 in
 ignore(E4_pack.append w ~digest:(E4_sha256.digest "abc") ~node_bytes:"abc");E4_pack.commit w;E4_pack.close w;
 let path=E4_pack.seg_path ~dir 0 in let valid=get path in
 let test label data=
  save path data;
  List.iter(fun verify ->let r=E4_pack.open_reader ~dir in
   Fun.protect ~finally:(fun()->E4_pack.close_reader r) (fun()->
    try
     if verify then Printf.printf "%s read=%s\n" label (match E4_pack.read r ~seg:0 ~off:E4_pack.head_length with Ok _->"Ok"|Error e->E4_pack.refusal_to_string e)
     else Printf.printf "%s scan=%s\n" label (E4_pack.scan_stop_to_string(E4_pack.scan r ~from:(0,E4_pack.head_length) ~f:(fun _ _ _ _->())))
    with e->Printf.printf "%s %s EXCEPTION=%s\n" label (if verify then "read" else "scan") (Printexc.to_string e))) [true;false]
 in
 test "valid" valid;
 List.iter(fun delta ->let b=Bytes.of_string valid in Bytes.blit_string (E4_be.be64 (max_int-delta)) 0 b (E4_pack.head_length+1) 8;test ("max_int-"^string_of_int delta) (Bytes.to_string b)) [0;4;16;64;100];
 test "restored" valid
