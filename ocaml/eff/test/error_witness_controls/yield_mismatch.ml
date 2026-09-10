(* Negative: a text witness cannot certify a Boolean generator-style failure. *)
open Eff_typed
let unsupported = Yield_error (Error_string, Bool_lit true)
