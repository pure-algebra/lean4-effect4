(* DI-62 positive controls. Their indices are checked by construction at compilation. *)
open Eff_typed

let fail_nat : (empty, never, nat) eff = Fail (Error_nat, Nat_lit 1)
let fail_text : (empty, never, string) eff = Fail (Error_string, Str_lit "lost")
let fail_pair : (empty, never, string * string) eff =
  Fail (Error_pair, Pair (Str_lit "A", Str_lit "message"))
let yield_text : (empty, never, string) eff = Yield_error (Error_string, Str_lit "lost")
let cause_text : (empty, string) cause = C_fail (Error_string, Str_lit "lost")
let fail_union (value : (empty, (nat, string) union) term) :
    (empty, never, (nat, string) union) eff =
  Fail (Error_union (Error_nat, Error_string), value)
let fail_never (value : (empty, never) term) : (empty, never, never) eff =
  Fail (Error_never, value)
