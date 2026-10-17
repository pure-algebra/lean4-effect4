(* bench_frame.ml -- phase 5 of the OCaml estate refactor: the canonical writer, measured.

   What it is: two measurements of the frame writer (ocaml/eff/eff_frame.ml).
     1. The choice (slice 5.1): three ways to write a nested frame, each over the same encoder
        of `Eff_types.Val.t` (the frames of Eff_val.emit), on values of every shape:
          copy     the writer before slice 5.1: each nested payload goes into a fresh Buffer and
                   is copied behind its header, so a byte at depth d is written d + 1 times;
          reserve  reserve the 8-byte length, write the payload in place, fill the length after,
                   in one growable byte buffer;
          sizes    fold the sizes first, then write into one buffer of the exact size.
        Each one's bytes are checked against Eff_val.to_bytes; a mismatch prints DIFFERS.
     2. The real writer, before and after the change: Eff_val.to_bytes on the same values, and
        Eff_wire.encode_program on the program goldens (ocaml/eff/goldens) and on deep and
        balanced program trees. These calls keep their types across the change, so one source
        measures both: run it at the base, then after.
   Depends on: effect4_eff (Eff_types, Eff_val, Eff_wire), Unix.

   Properties:
   F1  Every strategy's bytes equal Eff_val.to_bytes on every value measured, or the cell
       prints DIFFERS.                                                 tested (each cell)
   F2  Nothing is asserted about the numbers: they are printed.          by construction

   Method: best of `reps` runs (default 5) by Unix.gettimeofday, native code, a full major
   collection before each run.

   It is an EXECUTABLE, not a test: `dune test` does not run it.
   Run: cd ocaml && opam exec --switch=effect4 -- dune build engine/bench &&
        ./_build/default/engine/bench/bench_frame.exe [reps] [goldens-dir]
   (the goldens default to eff/goldens, from the ocaml directory) *)

open Eff_types

let reps = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 5
let goldens = if Array.length Sys.argv > 2 then Sys.argv.(2) else "eff/goldens"

let best (f : unit -> 'r) : float * 'r =
  let run () =
    Gc.full_major ();
    let t0 = Unix.gettimeofday () in
    let r = f () in
    ((Unix.gettimeofday () -. t0) *. 1e6, r)
  in
  let rec go k us r =
    if k <= 1 then (us, r)
    else
      let us', r' = run () in
      go (k - 1) (Float.min us us') r'
  in
  let us, r = run () in
  go reps us r

(* ------------------------------------------------------------ the three writers *)

let nat_digits (n : int) : string =
  let rec count m k = if m = 0 then k else count (m lsr 8) (k + 1) in
  let k = count n 0 in
  String.init k (fun i -> Char.unsafe_chr ((n lsr (8 * (k - 1 - i))) land 0xff))

let string_of_codes (codes : int list) : string =
  let b = Bytes.create (List.length codes) in
  List.iteri (fun i c -> Bytes.set b i (Char.chr c)) codes;
  Bytes.to_string b

let be64_string (n : int) : string =
  let b = Bytes.create 8 in
  Bytes.set_int64_be b 0 (Int64.logand (Int64.of_int n) Int64.max_int);
  Bytes.to_string b

module type WRITER = sig
  type w

  val name : string
  val frame : w -> int -> string -> unit
  val nat : w -> int -> unit
  val nested : w -> int -> (w -> unit) -> unit
  val run : (w -> 'a -> unit) -> 'a -> string
end

module Copy : WRITER = struct
  type w = Buffer.t

  let name = "copy"

  let frame b tag payload =
    Buffer.add_char b (Char.chr tag);
    Buffer.add_int64_be b (Int64.of_int (String.length payload));
    Buffer.add_string b payload

  let nat b n = frame b 2 (nat_digits n)

  let nested b tag f =
    let p = Buffer.create 32 in
    f p;
    Buffer.add_char b (Char.chr tag);
    Buffer.add_int64_be b (Int64.of_int (Buffer.length p));
    Buffer.add_buffer b p

  let run f v =
    let b = Buffer.create 64 in
    f b v;
    Buffer.contents b
end

module Reserve : WRITER = struct
  type w = { mutable buf : Bytes.t; mutable len : int }

  let name = "reserve"

  let grow w need =
    let cap = ref (2 * Bytes.length w.buf) in
    while !cap < w.len + need do
      cap := 2 * !cap
    done;
    let b = Bytes.create !cap in
    Bytes.blit w.buf 0 b 0 w.len;
    w.buf <- b

  let ensure w need = if w.len + need > Bytes.length w.buf then grow w need

  let header w tag len =
    ensure w 9;
    Bytes.unsafe_set w.buf w.len (Char.unsafe_chr tag);
    Bytes.set_int64_be w.buf (w.len + 1) (Int64.of_int len);
    w.len <- w.len + 9

  let frame w tag payload =
    let k = String.length payload in
    header w tag k;
    ensure w k;
    Bytes.unsafe_blit_string payload 0 w.buf w.len k;
    w.len <- w.len + k

  let nat w n =
    let rec count m k = if m = 0 then k else count (m lsr 8) (k + 1) in
    let k = count n 0 in
    header w 2 k;
    ensure w k;
    for i = 0 to k - 1 do
      Bytes.unsafe_set w.buf (w.len + i) (Char.unsafe_chr ((n lsr (8 * (k - 1 - i))) land 0xff))
    done;
    w.len <- w.len + k

  let nested w tag f =
    header w tag 0;
    let at = w.len in
    f w;
    Bytes.set_int64_be w.buf (at - 8) (Int64.of_int (w.len - at))

  let run f v =
    let w = { buf = Bytes.create 256; len = 0 } in
    f w v;
    Bytes.sub_string w.buf 0 w.len
end

module Sizes : WRITER = struct
  type w = {
    mutable sizing : bool;
    mutable sizes : int array;  (** each nested frame's payload size, in pre-order *)
    mutable slot : int;
    mutable total : int;
    mutable buf : Bytes.t;
    mutable pos : int;
  }

  let name = "sizes"

  let header w tag len =
    Bytes.unsafe_set w.buf w.pos (Char.unsafe_chr tag);
    Bytes.set_int64_be w.buf (w.pos + 1) (Int64.of_int len);
    w.pos <- w.pos + 9

  let frame w tag payload =
    let k = String.length payload in
    if w.sizing then w.total <- w.total + 9 + k
    else begin
      header w tag k;
      Bytes.unsafe_blit_string payload 0 w.buf w.pos k;
      w.pos <- w.pos + k
    end

  let nat w n =
    let rec count m k = if m = 0 then k else count (m lsr 8) (k + 1) in
    let k = count n 0 in
    if w.sizing then w.total <- w.total + 9 + k
    else begin
      header w 2 k;
      for i = 0 to k - 1 do
        Bytes.unsafe_set w.buf (w.pos + i) (Char.unsafe_chr ((n lsr (8 * (k - 1 - i))) land 0xff))
      done;
      w.pos <- w.pos + k
    end

  let nested w tag f =
    let slot = w.slot in
    w.slot <- slot + 1;
    if w.sizing then begin
      if slot = Array.length w.sizes then begin
        let a = Array.make (2 * slot) 0 in
        Array.blit w.sizes 0 a 0 slot;
        w.sizes <- a
      end;
      w.total <- w.total + 9;
      let before = w.total in
      f w;
      w.sizes.(slot) <- w.total - before
    end
    else begin
      header w tag w.sizes.(slot);
      f w
    end

  let run f v =
    let w = { sizing = true; sizes = Array.make 64 0; slot = 0; total = 0; buf = Bytes.empty; pos = 0 } in
    f w v;
    w.buf <- Bytes.create w.total;
    w.sizing <- false;
    w.slot <- 0;
    f w v;
    Bytes.unsafe_to_string w.buf
end

(* The frames of Eff_val.emit (ocaml/eff/eff_val.ml), over a writer. *)
module Val_encoder (W : WRITER) = struct
  let rec emit w (v : Val.t) =
    match v with
    | Val.Unit -> W.frame w 9 ""
    | Val.Bool x -> W.frame w 1 (if x then "\001" else "\000")
    | Val.Nat n -> W.nat w n
    | Val.Str s ->
      if not (String.is_valid_utf_8 s) then invalid_arg "Val_encoder: not valid UTF-8";
      W.frame w 3 s
    | Val.Bytes codes -> W.frame w 8 (string_of_codes codes)
    | Val.List xs -> W.nested w 4 (fun w -> List.iter (emit w) xs)
    | Val.Pair (x, y) ->
      W.nested w 5 (fun w ->
          emit w x;
          emit w y)
    | Val.None -> W.frame w 6 ""
    | Val.Some x -> W.nested w 7 (fun w -> emit w x)
    | Val.Ctor (i, args) ->
      W.nested w 10 (fun w ->
          W.nat w i;
          List.iter (emit w) args)
    | Val.Ref (k, d) -> W.frame w 11 (String.make 1 (Char.chr k) ^ string_of_codes d)
    | Val.Handle (k, key) -> W.frame w 12 (String.make 1 (Char.chr k) ^ nat_digits key)
    | Val.NegInt n -> W.frame w 13 (nat_digits n)
    | Val.Float bits -> W.frame w 14 (be64_string bits)

  let to_bytes v = W.run emit v
end

module Enc_copy = Val_encoder (Copy)
module Enc_reserve = Val_encoder (Reserve)
module Enc_sizes = Val_encoder (Sizes)

(* ------------------------------------------------------------------ the values *)

let todo i = Val.Ctor (0, [ Val.Nat i; Val.Str (Printf.sprintf "to-do number %d" i); Val.Bool (i mod 3 = 0) ])
let todos n = Val.List (List.init n todo)
let rec deep_some d = if d = 0 then Val.Nat 1 else Val.Some (deep_some (d - 1))
let rec deep_ctor d = if d = 0 then Val.Unit else Val.Ctor (d land 7, [ Val.Str "name"; deep_ctor (d - 1) ])
let wide n = Val.List (List.init n (fun i -> Val.Nat i))
let rec tree d = if d = 0 then Val.Nat d else Val.Pair (tree (d - 1), tree (d - 1))

let values =
  [ ("1 to-do", todo 7);
    ("100 to-dos", todos 100);
    ("10 000 to-dos", todos 10_000);
    ("some, depth 1 000", deep_some 1_000);
    ("some, depth 10 000", deep_some 10_000);
    ("ctor, depth 1 000", deep_ctor 1_000);
    ("list of 100 000 nats", wide 100_000);
    ("pair tree, depth 16", tree 16) ]

(* ----------------------------------------------------------------- the programs *)

let lit n = Term.Lit (Lit.Nat n)
let rec bind_chain d = if d = 0 then Eff.Succeed (lit 1) else Eff.Bind (Eff.Succeed (lit d), bind_chain (d - 1))
let rec bind_tree d = if d = 0 then Eff.Succeed (lit 1) else Eff.Bind (bind_tree (d - 1), bind_tree (d - 1))

let golden_programs () =
  match Sys.readdir goldens with
  | exception Sys_error _ -> []
  | files ->
    Array.to_list files
    |> List.filter (fun f -> Filename.check_suffix f ".bin")
    |> List.sort String.compare
    |> List.filter_map (fun f ->
           let ic = open_in_bin (Filename.concat goldens f) in
           let s = really_input_string ic (in_channel_length ic) in
           close_in ic;
           Option.map (fun p -> (p, s)) (Eff_wire.decode_program_exact s))

(* ------------------------------------------------------------------- the report *)

let mb bytes us = float_of_int bytes /. us

let () =
  Printf.printf "bench_frame: OCaml %s, best of %d, microseconds per encoding\n" Sys.ocaml_version reps;
  Printf.printf "\n1. the choice: three writers over the frames of Eff_val.emit (MB/s in brackets)\n";
  Printf.printf "%-22s %10s %18s %18s %18s\n" "value" "bytes" "copy" "reserve" "sizes";
  List.iter
    (fun (label, v) ->
      let expected = Eff_val.to_bytes v in
      let cell to_bytes =
        let us, bytes = best (fun () -> to_bytes v) in
        if String.equal bytes expected then Printf.sprintf "%9.1f [%5.0f]" us (mb (String.length bytes) us)
        else "DIFFERS"
      in
      Printf.printf "%-22s %10d %18s %18s %18s\n%!" label (String.length expected) (cell Enc_copy.to_bytes)
        (cell Enc_reserve.to_bytes) (cell Enc_sizes.to_bytes))
    values;
  Printf.printf "\n2. the real writer: Eff_val.to_bytes and Eff_wire.encode_program\n";
  List.iter
    (fun (label, v) ->
      let us, bytes = best (fun () -> Eff_val.to_bytes v) in
      Printf.printf "%-36s %10d bytes %12.1f us [%5.0f MB/s]\n%!" ("Eff_val.to_bytes, " ^ label)
        (String.length bytes) us (mb (String.length bytes) us))
    values;
  let programs = golden_programs () in
  let identical = List.for_all (fun (p, s) -> String.equal (Eff_wire.encode_program p) s) programs in
  let total = List.fold_left (fun a (_, s) -> a + String.length s) 0 programs in
  let us, () = best (fun () -> List.iter (fun (p, _) -> ignore (Sys.opaque_identity (Eff_wire.encode_program p))) programs) in
  Printf.printf "%-36s %10d bytes %12.1f us [%5.0f MB/s] (%d programs, re-encoded %s)\n%!"
    "Eff_wire.encode_program, goldens" total us (mb total us) (List.length programs)
    (if identical then "byte for byte" else "with a DIFFERENCE");
  List.iter
    (fun (label, p) ->
      let us, bytes = best (fun () -> Eff_wire.encode_program p) in
      Printf.printf "%-36s %10d bytes %12.1f us [%5.0f MB/s]\n%!" ("Eff_wire.encode_program, " ^ label)
        (String.length bytes) us (mb (String.length bytes) us))
    [ ("bind chain, depth 1 000", bind_chain 1_000);
      ("bind chain, depth 10 000", bind_chain 10_000);
      ("bind tree, depth 14", bind_tree 14) ]
