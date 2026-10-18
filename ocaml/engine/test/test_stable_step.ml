(* Prepared-step control, against each generated adapter.
   Depends on E4_engine.INSTANCE. Tested: one package retains its own source
   across repeated decisions and remains separate from another package.
   This finite control does not relate the machine to the call tree. *)
open Eff_types
open Effect4_engine
module Check (I : E4_engine.INSTANCE) = struct
  let run () =
    let program = Eff.Suspend (Eff.Succeed (Term.Lit (Lit.Nat 7))) in
    let other = Eff.Suspend (Eff.Succeed (Term.Lit (Lit.Nat 99))) in
    let prepared = I.prepare [] program in
    let separate = I.prepare [] other in
    let machine = I.load program ~fuel:100 in
    let normal, settled = I.step prepared ~fuel:100 machine (I.RunDecision_evaluate 0) in
    let repeated, _ = I.step prepared ~fuel:100 machine (I.RunDecision_evaluate 0) in
    let alternate, _ = I.step separate ~fuel:100 (I.load other ~fuel:100) (I.RunDecision_evaluate 0) in
    let returns n m = match List.assoc_opt 0 (I.completed_exits m) with
      | Some (Exit.Success (Val.Nat value)) -> value = n | _ -> false in
    assert settled;
    assert (returns 7 normal && returns 7 repeated && returns 99 alternate);
    Printf.printf "PASS %s prepared step retains each source across repeated decisions\n" I.name;
    let measure prepare_each_step =
      Gc.full_major ();
      let before = Gc.allocated_bytes () in
      let started = Sys.time () in
      for _ = 1 to 10000 do
        let package = if prepare_each_step then I.prepare [] program else prepared in
        ignore (I.step package ~fuel:100 machine (I.RunDecision_evaluate 0))
      done;
      (Gc.allocated_bytes () -. before) /. 10000., (Sys.time () -. started) *. 100.
    in
    let reuse_bytes, reuse_us = measure false in
    let rebuild_bytes, rebuild_us = measure true in
    Printf.printf "%s prepare+step bytes=%.1f cpu_us=%.3f; reuse+step bytes=%.1f cpu_us=%.3f (10000 decisions)\n"
      I.name rebuild_bytes rebuild_us reuse_bytes reuse_us
end
module Fast = Check (Api_engine_inst)
module Ref = Check (Api_engine_ref)
module Gen = Check (Api_gen_inst)
let () = Fast.run (); Ref.run (); Gen.run ()
