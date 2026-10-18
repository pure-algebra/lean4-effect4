(* Typed_lint's red control: each line marked "red" is a rule-7 finding the lint must report,
   and each line marked "green" must pass. Represents no Effect4 program. *)
type point = { x : int; y : int }
type seg = int

let same (a : point) b = a = b (* red: = on a record *)
let order (a : int * int) b = compare a b (* red: compare at a tuple *)
let member (p : point) ps = List.mem p ps (* red: List.mem at a record *)
let less a b = a < b (* red: a polymorphic helper *)
let late (deadline : float) now = now >= deadline (* red: a float *)
let empty (xs : int list) = xs = [] (* red: a list, even an empty one *)
let keyed (table : (int * int, string) Hashtbl.t) key = Hashtbl.find_opt table key (* red: a tuple key *)
let scalars (a : seg) b = a = b && "x" <> "y" && 'a' < 'b' && max true false (* green *)
let typed (a : point) b = Int.equal a.x b.x && Int.equal a.y b.y (* green *)
let counted (table : (string, int) Hashtbl.t) = Hashtbl.find_opt table "k" (* green *)
