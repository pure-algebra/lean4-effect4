(* Negative: a text witness cannot certify a Boolean cause leaf. *)
open Eff_typed
let unsupported = C_fail (Error_string, Bool_lit true)
