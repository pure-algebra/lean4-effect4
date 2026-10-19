open Effect4_engine_cas
let () =
 let p=Result.get_ok (Effect4_kit.Kit_author.build Effect4_kit.Kit_author.(succeed (nat 1))) in
 let bytes=Eff_wire.encode_program p in
 let node=E4_node.make ~version:0 ~kind:E4_kind.Program ~spec:E4_node.zero_digest ~payload:bytes in
 List.iter (fun (n,b) -> Printf.printf "%s=%b\n" n b; assert b)
 ["program",Option.is_some(Eff_wire.decode_program_exact bytes);
  "node",Result.is_ok(E4_node.decode(E4_node.encode node));
  "shape",Result.is_ok(E4_shape.cids_of_checked E4_shape.table E4_kind.Program ~payload:bytes);
  "control",Result.is_ok(E4_control.decode(E4_control.encode E4_control.initial));
  "json",Result.is_ok(Effect4_kit.Kit.Json.parse "[0,1,{\"a\":true}]")]
