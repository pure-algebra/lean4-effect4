(* Finite interface fixture. The final ascription keeps the source package name.
   Tested by test_interface; this fixture represents no Effect4 program syntax. *)
type memo = (int * bool) list
type public_alias = memo
let empty = []
let helper (x : memo) = x
let empty : memo = empty
