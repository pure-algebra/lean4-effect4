(* The value profile of a host, for `src/OCaml5/Value.lean`'s `Backend` row (`:49-58`:
   `native | jsoo`, `intBits` 63/32). The wasm column is owed before any value crosses the
   wasm boundary (host-frontier note §4.3 step 4).

   Built in the same ways as the avatar so the numbers diff directly:
   `probe.exe` (native), `probe.bc` (bytecode), `probe.bc.js` (jsoo), `probe.bc.wasm.js`
   (wasm). One tab-separated line per fact. No `Obj`, no `Marshal` (STANDARDS.md §4). *)

type _ Effect.t += Ping : int Effect.t

let () =
  let p k v = Printf.printf "%s\t%s\n" k v in
  p "backend_type"
    (match Sys.backend_type with
     | Sys.Native -> "Native"
     | Sys.Bytecode -> "Bytecode"
     | Sys.Other s -> "Other " ^ s);
  p "int_size" (string_of_int Sys.int_size);
  p "word_size" (string_of_int Sys.word_size);
  p "max_int" (string_of_int max_int);
  p "min_int" (string_of_int min_int);
  p "max_int_hex" (Printf.sprintf "%x" max_int);
  p "big_endian" (string_of_bool Sys.big_endian);
  p "max_string_length" (string_of_int Sys.max_string_length);
  p "max_array_length" (string_of_int Sys.max_array_length);
  (* `Nat` is encoded as `int` in places; these are the wrap points. *)
  p "succ_max_int" (string_of_int (max_int + 1));
  p "shift_62" (string_of_int (1 lsl 62));
  p "compare_ints" (string_of_int (compare max_int min_int));
  p "float_repr" (Printf.sprintf "%.17g" (1.0 /. 3.0));
  p "float_to_int" (string_of_int (int_of_float 1e18));
  p "string_compare" (string_of_int (compare "abc" "abd"));
  (* One effect performed and resumed: the smallest proof the effect mode works at all. *)
  let r =
    Effect.Deep.match_with
      (fun () -> Effect.perform Ping + 1)
      ()
      { Effect.Deep.retc = (fun v -> v)
      ; exnc = raise
      ; effc =
          (fun (type a) (e : a Effect.t) ->
             match e with
             | Ping ->
               Some (fun (k : (a, int) Effect.Deep.continuation) ->
                 Effect.Deep.continue k 41)
             | _ -> None)
      }
  in
  p "effect_roundtrip" (string_of_int r)
