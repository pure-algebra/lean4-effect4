(* Negative: a text witness cannot certify a Boolean ordinary failure. *)
open Eff_typed
let unsupported = Fail (Error_string, Bool_lit true)
