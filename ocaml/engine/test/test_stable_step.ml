(* S0 stable-step control, against both generated adapters.
   Depends on E4_engine.INSTANCE. Tested: the closed program/table own evaluation,
   including when the obsolete interpreter argument comes from a different program.
   This is a finite compatibility observation, not arbitrary-interpreter equality. *)
open Eff_types
open Effect4_engine
module Check (I : E4_engine.INSTANCE) = struct
  let run () =
    let program = Eff.Suspend (Eff.Succeed (Term.Lit (Lit.Nat 7))) in
    let other = Eff.Suspend (Eff.Succeed (Term.Lit (Lit.Nat 99))) in
    let machine = I.load program ~fuel:100 in
    let normal, _ = I.step [] program (I.interp_of [] program) ~fuel:100 machine (I.RunDecision_evaluate 0) in
    let mismatched, _ = I.step [] program (I.interp_of [] other) ~fuel:100 machine (I.RunDecision_evaluate 0) in
    let returns_seven m = match List.assoc_opt 0 (I.completed_exits m) with
      | Some (Exit.Success (Val.Nat 7)) -> true | _ -> false in
    assert (returns_seven normal);
    assert (returns_seven mismatched);
    Printf.printf "PASS %s stable step uses its program with a mismatched obsolete interpreter\n" I.name
end
module Fast = Check (Api_engine_inst)
module Ref = Check (Api_engine_ref)
module Gen = Check (Api_gen_inst)
let () = Fast.run (); Ref.run (); Gen.run ()
