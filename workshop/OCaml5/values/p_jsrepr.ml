(* O3 probe, js_of_ocaml only: the JS-level representation of OCaml values.
   `Obj` cannot see it -- obj.js answers in OCaml's own tag alphabet -- so this
   program routes every value through `Hashtbl.hash`, which `p_jsrepr.js`
   overrides. Compile with
     js_of_ocaml compile --target-env=nodejs p_jsrepr.js p_jsrepr.byte -o p_jsrepr.js
   It is not run on native or bytecode: there the answers are the header layout
   of mlvalues.h, already witnessed by w_block.ml through Obj. *)
let opaque = Sys.opaque_identity
let probe : string -> 'a -> unit = fun k v -> ignore (Hashtbl.hash (k, Obj.repr v))

type t = A | B of int | C of int * int
type r = { f1 : int; f2 : string }

let add4 a b c d = a + b + c + d
let mk1 : int -> int -> int -> int = fun a -> fun b c -> a + b + c

let () =
  probe "int" (opaque 42);
  probe "int_neg" (opaque (-42));
  probe "unit" (opaque ());
  probe "bool_true" (opaque true);
  probe "bool_false" (opaque false);
  probe "char" (opaque 'a');
  probe "float" (opaque 1.5);
  probe "float_neg0" (opaque (-0.0));
  probe "float_integral" (opaque 3.0);
  probe "string_ascii" (opaque "abc");
  probe "string_utf8" (opaque "h\xc3\xa9llo");
  probe "bytes" (Bytes.of_string "abc");
  probe "ctor_const" (opaque A);
  probe "ctor_B" (opaque (B 7));
  probe "ctor_C" (opaque (C (1, 2)));
  probe "record" (opaque { f1 = 1; f2 = "s" });
  probe "tuple" (opaque (1, 2));
  probe "none" (opaque (None : int option));
  probe "some" (opaque (Some 1));
  probe "list" (opaque [ 1; 2 ]);
  probe "int_array" (opaque [| 1; 2; 3 |]);
  probe "float_array" (opaque [| 1.0; 2.0 |]);
  probe "int64" (opaque 3L);
  probe "int64_big" (opaque 4611686018427387903L);
  probe "int32" (opaque 3l);
  probe "nativeint" (opaque 3n);
  probe "closure_4" (opaque add4);
  probe "closure_1" (opaque mk1);
  probe "closure_partial" (opaque ((opaque add4) 1 2));
  (* `.l` is absent until a generic call site sets it from `f.length`
     (stdlib.js:24, and generate.ml:760-832 for the caml_callN wrappers).
     jsoo's flow analysis resolves an application whose callee it can track, so
     the closure has to arrive through a runtime-indexed array. *)
  let table : (int -> int -> int) array =
    [| (fun a b -> a + b); (fun a b -> a * b) |]
  in
  let pick = table.(Array.length Sys.argv - 1) in
  probe "closure_table_before_call" pick;
  ignore (pick 2 3);
  probe "closure_table_after_call" pick;
  (* a genuine caml_call_gen partial: d > 0, the wrapper gets `g.l = d`
     (stdlib.js:66) *)
  let wrapper = (Obj.magic pick : int -> int -> int -> int) 2 in
  probe "closure_call_gen_wrapper" wrapper;
  probe "exn_const" (opaque Not_found);
  probe "exn_arg" (opaque (Invalid_argument "z"))
