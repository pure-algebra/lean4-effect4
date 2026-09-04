(* O3 witness: closures and application. Native: Closure_tag 247 with the arity
   in the code pointer's header. js_of_ocaml: a JS function whose declared
   arity is `.l`, with caml_call_gen (stdlib.js:23-70) splitting partial
   application (d > 0, a wrapper with `g.l = d`) from over-application
   (d < 0, apply the first n then recurse). *)
let p k v = Printf.printf "%s\t%s\n" k v
let opaque = Sys.opaque_identity

let add4 a b c d = ((a * 1000) + (b * 100) + (c * 10)) + d
let mk1 : int -> int -> int -> int = fun a -> fun b c -> (a * 100) + (b * 10) + c
let counter = ref 0
let effectful a = incr counter; fun b -> a + b

let () =
  (* partial application: 4-ary applied to 2, then to 1, then to 1 *)
  let f2 = (opaque add4) 1 2 in
  let f3 = (opaque f2) 3 in
  p "partial_2_1_1" (string_of_int ((opaque f3) 4));
  let g1 = (opaque add4) 1 in
  p "partial_1_3" (string_of_int ((opaque g1) 2 3 4));
  p "partial_1_1_1_1" (string_of_int ((opaque ((opaque ((opaque g1) 2)) 3)) 4));
  (* over-application: a 1-ary closure applied to 3 arguments at once *)
  p "over_1_of_3" (string_of_int ((opaque mk1) 1 2 3));
  p "over_2_of_3" (string_of_int ((opaque ((opaque mk1) 1)) 2 3));
  (* effects happen once per real application, not per partial step *)
  counter := 0;
  let h = (opaque effectful) 10 in
  let r1 = (opaque h) 5 in
  let r2 = (opaque h) 6 in
  p "over_effect_result" (string_of_int (r1 + r2));
  p "over_effect_count" (string_of_int !counter);
  counter := 0;
  let r3 = (opaque effectful) 10 5 in
  p "over_direct_result" (string_of_int r3);
  p "over_direct_count" (string_of_int !counter);
  (* arity is not observable through the value, only through the result *)
  p "closure_is_int" (string_of_bool (Obj.is_int (Obj.repr (opaque add4))));
  p "closure_tag" (string_of_int (Obj.tag (Obj.repr (opaque add4))));
  p "closure_compare"
    (try string_of_int (compare (opaque add4) (opaque add4))
     with Invalid_argument m -> "Invalid_argument:" ^ m);
  p "closure_equal_self"
    (try string_of_bool (opaque add4 = opaque add4)
     with Invalid_argument m -> "Invalid_argument:" ^ m);
  p "closure_phys_eq" (string_of_bool (opaque add4 == opaque add4))
