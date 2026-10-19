(* red_closure_module -- a value the closure's interface exports for the test lanes, and the
   installed Api_gen does not, named through the closure's module from an installed client; its
   build must fail on the module (D1). *)
let _ = Closure_gen.store_image_equiv
