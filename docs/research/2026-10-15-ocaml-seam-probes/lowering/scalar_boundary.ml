(* Research probe. No generated source or production API imports this module.
   Properties: representation hiding, checked bounds, and exact bit round-trips
   are tested by run.py. OCaml typechecks the invalid controls separately. *)

module type NAT_PROFILE = sig
  type t
  val of_int : int -> (t, string) result
  val to_int : t -> int
  val add : t -> t -> (t, string) result
end

module Make_nat (Bound : sig val maximum : int end) : NAT_PROFILE = struct
  type t = int
  let of_int n =
    if n < 0 || n > Bound.maximum then Error "outside profile" else Ok n
  let to_int n = n
  let add a b =
    if a > Bound.maximum - b then Error "outside profile" else Ok (a + b)
end

module Nat = Make_nat (struct let maximum = 9007199254740991 end)
module Small = Make_nat (struct let maximum = 3 end)

module Bits64 : sig
  type t
  val of_int64_bits : int64 -> t
  val to_int64_bits : t -> int64
  val equal : t -> t -> bool
end = struct
  type t = int64
  let of_int64_bits x = x
  let to_int64_bits x = x
  let equal = Int64.equal
end

let require = function Ok n -> n | Error msg -> failwith msg
let refuses = function Error "outside profile" -> true | Ok _ | Error _ -> false

let () =
  assert (refuses (Nat.of_int (-1)));
  assert (Nat.to_int (require (Nat.add (require (Nat.of_int 2))
                                         (require (Nat.of_int 3)))) = 5);
  assert (refuses (Nat.add (require (Nat.of_int 9007199254740991))
                         (require (Nat.of_int 1))));
  assert (Small.to_int (require (Small.of_int 3)) = 3);
  assert (refuses (Small.add (require (Small.of_int 3)) (require (Small.of_int 1))));
  List.iter (fun bits ->
    let value = Bits64.of_int64_bits bits in
    assert (Int64.equal (Bits64.to_int64_bits value) bits);
    assert (Bits64.equal value (Bits64.of_int64_bits bits)))
    [0L; 1L; Int64.max_int; Int64.min_int; -1L];
  print_endline "scalar-boundary: finite controls pass"
