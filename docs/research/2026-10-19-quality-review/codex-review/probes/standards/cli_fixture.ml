open Effect4_kit
open Eff_types
let () =
  let p = Eff.Succeed (Term.Lit (Lit.Nat 1)) in
  Out_channel.with_open_bin Sys.argv.(1) (fun o -> output_string o (Kit.Json.render(Kit.Json.program_json p)));
  List.iter (fun s -> Unix.putenv "E4_BATCH" s; let c=Effect4_engine.E4_sched.config_of_env() in
    Printf.printf "E4_BATCH=%S => batch=%d\n" s c.batch) ["8";"eight";"-1";"9999999999999999999999999"]
