(* test_val_frames — the two frames the shared value foundation adds (hand-written).

   What it is: Eff_frame's kernel grew tags 11 (`ref`) and 12 (`handle`), the last two
   constructors of the Lean carrier `Effect4.Store.Val` (src/Effect4/Store/Val.lean:107-111).
   Their payloads are read off the Lean encoder itself (Val.lean:158-159, restated as
   `payload` at :203-204):

     ref    k d  ->  framed 11 (k :: d)          the kind byte, then the digest bytes
     handle k n  ->  framed 12 (k :: natBytes n) the kind byte, then the key's Nat digits

   so a `ref`'s digest is opaque bytes of any length and a `handle`'s key is the same
   shortest-form digit string a `nat` frame carries — the key 0 is no digits at all
   (Val.lean:1136).

   Checks:
   V1  the two goldens are byte for byte what Eff_frame's emitters write for the tree the
       golden names, and the composed reader below reads them back to that tree;
   V2  the exactness rules of the two new arms: a payload with no kind byte (ref and handle),
       a handle key with a leading zero digit, a handle key out of the int range, and a wrong
       tag are refusals — never repairs (Val.lean:1169, 1176-1177);
   V3  no digits is the key 0, not a refusal — the encoder's rule, not a repair;
   V4  neither frame is a program frame: Eff_wire refuses both at the top level.

   The goldens are HAND-DERIVED (see `derivations` below for the byte arithmetic) because
   the Lean build was not available on 2026-09-07 when they were cut. *)

let checks = ref 0
let failures = ref 0

let check (name : string) (ok : bool) : unit =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "FAIL: %s\n%!" name
  end

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let goldens = "../goldens/"

let unhex (s : string) : string =
  let digit c =
    match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
    | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
    | _ -> invalid_arg "unhex: not a hex digit"
  in
  let clean = Buffer.create (String.length s) in
  String.iter
    (fun c -> if c <> '\n' && c <> '\r' && c <> ' ' && c <> '\t' then Buffer.add_char clean c)
    s;
  let clean = Buffer.contents clean in
  if String.length clean mod 2 <> 0 then invalid_arg "unhex: odd number of digits";
  let out = Buffer.create (String.length clean / 2) in
  let i = ref 0 in
  while !i < String.length clean do
    Buffer.add_char out (Char.chr ((digit clean.[!i] * 16) + digit clean.[!i + 1]));
    i := !i + 2
  done;
  Buffer.contents out

let hex (s : string) : string =
  String.concat "" (List.map (fun c -> Printf.sprintf "%02x" (Char.code c)) (List.init (String.length s) (String.get s)))

(* ---- the subset of Store.Val the goldens use, as a tree ---- *)

type v =
  | Nat of int
  | Str of string
  | List of v list
  | Ctor of int * v list
  | Ref of int * string
  | Handle of int * int

let rec emit (b : Buffer.t) (t : v) : unit =
  match t with
  | Nat n -> Eff_frame.emit_nat b n
  | Str s -> Eff_frame.emit_string b s
  | List xs -> Eff_frame.emit_list b emit xs
  | Ctor (i, args) -> Eff_frame.emit_ctor b i (fun p -> List.iter (emit p) args)
  | Ref (k, d) -> Eff_frame.emit_ref b (k, d)
  | Handle (k, n) -> Eff_frame.emit_handle b (k, n)

(* The reader entry point over that subset: dispatch on the frame's tag, then hand the frame
   to the kernel decoder for it. Every arm is the kernel's, so every arm's exactness is. *)
let rec dec : v Eff_frame.decoder = fun s pos limit ->
  let open Eff_frame in
  match read_frame s pos limit with
  | None -> None
  | Some (t, _, _, _) ->
    let map f = function None -> None | Some (x, n) -> Some (f x, n) in
    if t = tag_nat then map (fun n -> Nat n) (decode_nat s pos limit)
    else if t = tag_string then map (fun x -> Str x) (decode_string s pos limit)
    else if t = tag_list then map (fun xs -> List xs) (decode_list dec s pos limit)
    else if t = tag_ref then map (fun (k, d) -> Ref (k, d)) (decode_ref s pos limit)
    else if t = tag_handle then map (fun (k, n) -> Handle (k, n)) (decode_handle s pos limit)
    else if t = tag_ctor then
      (match read_ctor s pos limit with
       | None -> None
       | Some (i, p, e, next) ->
         let rec go p acc =
           if p = e then Some (Ctor (i, List.rev acc), next)
           else match dec s p e with None -> None | Some (x, p') -> go p' (x :: acc)
         in
         go p [])
    else None

let bytes_of (t : v) : string = Eff_frame.to_string emit t

(* ---- the two goldens, and the byte arithmetic they were derived from ----

   HAND-DERIVED 2026-09-07 (no Lean process could be started on this machine when these were
   cut, one-process rule), CONFIRMED the same day by the seat against Val.lean's own `#guard`s:
   the handle tree is the one decoded at `Val.lean:1174-1175` and `nat 0` as no digits is
   `:1136`; the ref tree is `:1147` with its 42-byte ref frame `:1131`. Both byte strings come
   from Val.lean's `encode`. `framed t p = t :: be64 (length p) ++ p`, be64 eight big-endian
   bytes.

   goldens/val_handle.hex — the tree `ctor 0 [handle 1 3, list [handle 2 4, nat 9]]`, which
   is the Lean round-trip guard at Val.lean:1174-1175.

     handle 1 3   payload [01 03]                       len  2 -> 0c 00*7 02 | 01 03      11 B
     handle 2 4   payload [02 04]                       len  2 -> 0c 00*7 02 | 02 04      11 B
     nat 9        payload [09]                          len  1 -> 02 00*7 01 | 09         10 B
     list [..]    payload = 11 + 10                     len 21 -> 04 00*7 15 | ...        30 B
     ctor 0 [..]  payload = framed 2 (natBytes 0)                                          9 B
                          ++ 11 (handle 1 3) ++ 30 (list)                                 41 B
                                                        len 50 -> 0a 00*7 32 | ...        59 B

     0a 0000000000000032  02 0000000000000000
     0c 0000000000000002 0103  04 0000000000000015
     0c 0000000000000002 0204  02 0000000000000001 09

   goldens/val_ref.hex — the tree `ctor 0 [str "Effect", ref 2 (32 zero bytes)]`, which is
   the Lean `handles = []` guard at Val.lean:1147; its ref frame's length 42 is the guard at
   Val.lean:1131.

     str "Effect" payload 45 66 66 65 63 74               len  6 -> 03 00*7 06 | ...      15 B
     ref 2 0^32   payload [02] ++ 32 zero bytes           len 33 -> 0b 00*7 21 | ...      42 B
     ctor 0 [..]  payload = 9 (framed 2 []) + 15 + 42     len 66 -> 0a 00*7 42 | ...      75 B

     0a 0000000000000042  02 0000000000000000
     03 0000000000000006 456666656374
     0b 0000000000000021 02 00*32                                                        *)

let tree_handle : v = Ctor (0, [ Handle (1, 3); List [ Handle (2, 4); Nat 9 ] ])
let tree_ref : v = Ctor (0, [ Str "Effect"; Ref (2, String.make 32 '\000') ])

let golden (name : string) (tree : v) (expected_len : int) : unit =
  let want = unhex (read_file (goldens ^ name ^ ".hex")) in
  let got = bytes_of tree in
  check (name ^ ": the golden is " ^ string_of_int expected_len ^ " bytes")
    (String.length want = expected_len);
  check (name ^ ": the emitters write the golden byte for byte") (got = want);
  if got <> want then Printf.printf "    want %s\n    got  %s\n%!" (hex want) (hex got);
  check (name ^ ": the golden decodes exactly to the tree") (Eff_frame.exact dec want = Some tree);
  check (name ^ ": a trailing byte is refused") (Eff_frame.exact dec (want ^ "\000") = None);
  check (name ^ ": a truncated golden is refused")
    (Eff_frame.exact dec (String.sub want 0 (String.length want - 1)) = None);
  check (name ^ ": the program wire refuses it") (Eff_wire.decode_program_exact want = None);
  Printf.printf "  %-14s %4d bytes  emit=golden  decode=tree\n%!" name (String.length want)

(* ---- V1 ---- *)

let () =
  Printf.printf "test_val_frames: the ref (11) and handle (12) frames\n%!";
  golden "val_handle" tree_handle 59;
  golden "val_ref" tree_ref 75

(* ---- V2, V3, V4 ---- *)

let () =
  let open Eff_frame in
  let frame tag payload = to_string (fun b () -> emit_frame b tag payload) () in
  (* round trips of the frames alone *)
  let rt_h k n = exact decode_handle (to_string emit_handle (k, n)) = Some (k, n) in
  check "handle round trip at keys 0, 1, 255, 256, 2^32, max_int"
    (rt_h 2 0 && rt_h 2 1 && rt_h 0 255 && rt_h 255 256 && rt_h 7 (1 lsl 32) && rt_h 1 max_int);
  let rt_r k d = exact decode_ref (to_string emit_ref (k, d)) = Some (k, d) in
  check "ref round trip on an empty, a short and a 32-byte digest"
    (rt_r 2 "" && rt_r 0 "\001\002\003" && rt_r 255 (String.make 32 '\255'));
  (* V3: no digits is the key 0, the encoder's rule (Val.lean:1136) *)
  check "a handle payload of one kind byte is the key 0"
    (exact decode_handle (frame tag_handle "\001") = Some (1, 0)
     && to_string emit_handle (1, 0) = frame tag_handle "\001");
  (* V2: the refusals *)
  check "a handle key with a leading zero digit is refused"
    (exact decode_handle (frame tag_handle "\002\000\007") = None);
  check "a handle with an empty payload (no kind byte) is refused"
    (exact decode_handle (frame tag_handle "") = None);
  check "a ref with an empty payload (no kind byte) is refused"
    (exact decode_ref (frame tag_ref "") = None);
  check "a handle key of nine digits is refused"
    (exact decode_handle (frame tag_handle "\002\001\000\000\000\000\000\000\000\000") = None);
  check "a handle key of eight digits above max_int is refused"
    (exact decode_handle (frame tag_handle "\002\064\000\000\000\000\000\000\000") = None);
  check "a handle key of eight digits at max_int is accepted"
    (exact decode_handle (frame tag_handle "\002\063\255\255\255\255\255\255\255") = Some (2, max_int));
  check "the two tags do not read each other's frames"
    (exact decode_handle (frame tag_ref "\002\003") = None
     && exact decode_ref (frame tag_handle "\002\003") = None);
  check "a ref or handle frame under any other decoder is refused"
    (exact decode_nat (frame tag_handle "\002\003") = None
     && exact decode_string (frame tag_ref "\002\003") = None
     && exact (decode_list decode_nat) (frame tag_ref "\002") = None);
  check "a frame whose length prefix runs past the end is refused"
    (exact decode_handle ("\012\000\000\000\000\000\000\000\004\002\003") = None
     && exact decode_ref ("\011\000\000\000\000\000\000\000\004\002") = None);
  check "a ref or handle frame shorter than nine bytes is refused"
    (exact decode_ref "\011\000\000" = None && exact decode_handle "\012" = None);
  (* V4: neither frame is a program frame *)
  check "the program wire refuses a bare handle and a bare ref"
    (Eff_wire.decode_program_exact (to_string emit_handle (1, 3)) = None
     && Eff_wire.decode_program_exact (to_string emit_ref (2, String.make 32 '\000')) = None)

let () =
  Printf.printf "test_val_frames: %d checks, %d failures\n%!" !checks !failures;
  if !failures > 0 then exit 1
