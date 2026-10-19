(* Finite interface fixture. The final ascription keeps the source package name.
   Tested by test_interface; this fixture represents no Effect4 program syntax. *)
type memo = (int * bool) list
type public_alias = memo

(* A recursive group whose first member no root names: a facade keeps the second alone. *)
type dropped = Dropped of kept_after
and kept_after = Kept of int

let empty = []
let helper (x : memo) = x
let empty : memo = empty
let make_kept n = Kept n
