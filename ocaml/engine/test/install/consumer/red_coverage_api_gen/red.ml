(* red_coverage_api_gen -- a coverage root is not exported by the installed Api_gen; its build must fail (R6.2). *)
let _ = Effect4_gen.Api_gen.dispatcher_insert
