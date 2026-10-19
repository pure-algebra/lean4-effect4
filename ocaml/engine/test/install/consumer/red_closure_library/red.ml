(* red_closure_library -- the closure linked by its private name; a value its interface exports
   is still unbound, since the module is; its build must fail (D1). *)
let _ = Closure_gen.store_image_equiv
