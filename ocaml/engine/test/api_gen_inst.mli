(* Api_gen_inst: the generated list-backed engine's adapter interface.
   Depends on the one engine instance signature.
   Properties: callers see the instance operations only, by construction.
   The differential and test_stable_step check the native instance. *)
include Effect4_engine.E4_engine.INSTANCE
