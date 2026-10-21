(* Prepared-step control, against each generated adapter.
   Depends on E4_engine.INSTANCE. Tested: one package retains its own source
   across repeated decisions and remains separate from another package.
   This finite control does not relate the machine to the call tree. *)
open Eff_types
open Effect4_engine

module Check (I : E4_engine.INSTANCE) = struct
  let run () =
    let program = Eff.Suspend (Eff.Succeed (Term.Lit (Lit.Nat (Z.of_int 7)))) in
    let other = Eff.Suspend (Eff.Succeed (Term.Lit (Lit.Nat (Z.of_int 99)))) in
    let prepared = I.prepare [] program in
    let separate = I.prepare [] other in
    let machine = I.load program ~fuel:(Z.of_int 100) in
    let normal, settled =
      I.step prepared ~fuel:(Z.of_int 100) machine (I.RunDecision_evaluate Z.zero)
    in
    let repeated, _ =
      I.step prepared ~fuel:(Z.of_int 100) machine (I.RunDecision_evaluate Z.zero)
    in
    let alternate, _ =
      I.step
        separate
        ~fuel:(Z.of_int 100)
        (I.load other ~fuel:(Z.of_int 100))
        (I.RunDecision_evaluate Z.zero)
    in
    let returns n m =
      match List.assoc_opt Z.zero (I.completed_exits m) with
      | Some (Exit.Success (Val.Nat value)) -> Z.equal value (Z.of_int n)
      | _ -> false
    in
    assert settled;
    assert (returns 7 normal && returns 7 repeated && returns 99 alternate);
    Printf.printf
      "PASS %s prepared step retains each source across repeated decisions\n"
      I.name;
    let measure prepare_each_step =
      Gc.full_major ();
      let before = Gc.allocated_bytes () in
      let started = Sys.time () in
      for _ = 1 to 10000 do
        let package = if prepare_each_step then I.prepare [] program else prepared in
        ignore
          (I.step package ~fuel:(Z.of_int 100) machine (I.RunDecision_evaluate Z.zero))
      done;
      (Gc.allocated_bytes () -. before) /. 10000., (Sys.time () -. started) *. 100.
    in
    let reuse_bytes, reuse_us = measure false in
    let rebuild_bytes, rebuild_us = measure true in
    Printf.printf
      "%s prepare+step bytes=%.1f cpu_us=%.3f; reuse+step bytes=%.1f cpu_us=%.3f (10000 \
       decisions)\n"
      I.name
      rebuild_bytes
      rebuild_us
      reuse_bytes
      reuse_us
  ;;
end

module Fast = Check (Api_engine_inst)
module Gen = Check (Api_gen_inst)

let () =
  Fast.run ();
  Gen.run ()
;;
