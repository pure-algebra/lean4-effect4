(* Eff_val — a value's canonical frames (hand-written), the lanes' one writer and reader.

   What it is: `Val.encode` of src/Effect4/Store/Carrier/Val.lean, as OCaml over Eff_frame, for
   `Eff_types.Val.t`. The engine's lanes compare a value by these bytes: the scenarios lane
   (engine/test/scenarios), the to-do host lane (engine/test/todo) and the Modeled lane
   (engine/test/modeled).
   Depends on: Eff_frame, Eff_types.

   Behaviours it holds itself to:
   V1  `emit` writes every value in Lean's frames: tags 1..14 of Eff_frame, a negative integer
       `-(n+1)` as tag 13 over n's digits, a double's bits as tag 14 over 8 big-endian bytes.
                                                    by construction; tested (test_scenarios S3)
   V2  `decode` reads scalars, strings, lists, options, pairs, constructor applications and
       negative integers, and refuses every other frame (bytes, references, handles, doubles):
       a lane's fixture carries none of them, and a refusal is never a guess. A negative
       integer reads by the `nat` digit rule (`Eff_frame.decode_neg_int`); the Modeled lane's
       fixture carries them (engine/test/modeled).                     by construction; tested
   V3  Round trip: for every value a fixture carries, `emit (decode bytes) = bytes`.
                                                                tested (test_scenarios S3)
   V4  A byte string or a digest is written in time linear in its length.  by construction
   V5  `equal` is structural equality, the relation of Lean's derived `DecidableEq Store.Val`,
       and compares each field by its own type's equality (ocaml/STANDARDS.md rule 7).
                                                                       by construction *)

(* The bytes whose codes are listed, in one pass; a code outside 0..255 raises Invalid_argument,
   as `Char.chr` does (V4). *)
let string_of_codes (codes : int list) : string =
  let s = Bytes.create (List.length codes) in
  List.iteri (fun i code -> Bytes.set s i (Char.chr code)) codes;
  Bytes.unsafe_to_string s

let be64 (n : int) : string = Eff_frame.to_string Eff_frame.emit_be64 n

(* The frames of `Val.encode`. *)
let rec emit (b : Eff_frame.writer) (v : Eff_types.Val.t) : unit =
  match v with
  | Eff_types.Val.Unit -> Eff_frame.emit_unit b ()
  | Eff_types.Val.Bool x -> Eff_frame.emit_bool b x
  | Eff_types.Val.Nat n -> Eff_frame.emit_nat b n
  | Eff_types.Val.Str s -> Eff_frame.emit_string b s
  | Eff_types.Val.Bytes codes -> Eff_frame.emit_frame b Eff_frame.tag_bytes (string_of_codes codes)
  | Eff_types.Val.List xs -> Eff_frame.emit_list b emit xs
  | Eff_types.Val.Pair (x, y) -> Eff_frame.emit_pair b emit emit (x, y)
  | Eff_types.Val.None -> Eff_frame.emit_option b emit None
  | Eff_types.Val.Some x -> Eff_frame.emit_option b emit (Some x)
  | Eff_types.Val.Ctor (index, args) -> Eff_frame.emit_ctor b index (fun p -> List.iter (emit p) args)
  | Eff_types.Val.Ref (kind, digest) -> Eff_frame.emit_ref b (kind, string_of_codes digest)
  | Eff_types.Val.Handle (kind, key) -> Eff_frame.emit_handle b (kind, key)
  | Eff_types.Val.NegInt n -> Eff_frame.emit_frame b Eff_frame.tag_int (Eff_frame.nat_digits n)
  | Eff_types.Val.Float bits -> Eff_frame.emit_frame b Eff_frame.tag_float (be64 bits)

(* A value's canonical bytes. *)
let to_bytes (v : Eff_types.Val.t) : string = Eff_frame.to_string emit v

(* The reader of the same frames (V2). *)
let rec decode : Eff_types.Val.t Eff_frame.decoder =
 fun s pos limit ->
  match Eff_frame.read_frame s pos limit with
  | None -> None
  | Some (tag, p, e, next) ->
    if tag = Eff_frame.tag_unit then if p = e then Some (Eff_types.Val.Unit, next) else None
    else if tag = Eff_frame.tag_bool then
      Option.map (fun (x, n) -> (Eff_types.Val.Bool x, n)) (Eff_frame.decode_bool s pos limit)
    else if tag = Eff_frame.tag_nat then
      Option.map (fun (x, n) -> (Eff_types.Val.Nat x, n)) (Eff_frame.decode_nat s pos limit)
    else if tag = Eff_frame.tag_string then
      Option.map (fun (x, n) -> (Eff_types.Val.Str x, n)) (Eff_frame.decode_string s pos limit)
    else if tag = Eff_frame.tag_list then
      Option.map (fun (xs, n) -> (Eff_types.Val.List xs, n)) (Eff_frame.decode_list decode s pos limit)
    else if tag = Eff_frame.tag_pair then
      Option.map
        (fun ((x, y), n) -> (Eff_types.Val.Pair (x, y), n))
        (Eff_frame.decode_pair decode decode s pos limit)
    else if tag = Eff_frame.tag_none || tag = Eff_frame.tag_some then
      Option.map
        (fun (o, n) -> ((match o with None -> Eff_types.Val.None | Some x -> Eff_types.Val.Some x), n))
        (Eff_frame.decode_option decode s pos limit)
    else if tag = Eff_frame.tag_int then
      Option.map (fun (n, next) -> (Eff_types.Val.NegInt n, next)) (Eff_frame.decode_neg_int s pos limit)
    else if tag = Eff_frame.tag_ctor then
      match Eff_frame.read_ctor s pos limit with
      | None -> None
      | Some (index, p', e', next') ->
        let rec args p acc =
          if p = e' then Some (List.rev acc)
          else match decode s p e' with None -> None | Some (x, p'') -> args p'' (x :: acc)
        in
        Option.map (fun xs -> (Eff_types.Val.Ctor (index, xs), next')) (args p' [])
    else None

(* Exactly one value: trailing bytes are a refusal. *)
let decode_exact (s : string) : Eff_types.Val.t option = Eff_frame.exact decode s

(* Structural equality (V5). The last case names every constructor, so a new one is a
   non-exhaustive match until it has its own case. *)
let rec equal (a : Eff_types.Val.t) (b : Eff_types.Val.t) : bool =
  let module V = Eff_types.Val in
  match a, b with
  | V.Unit, V.Unit | V.None, V.None -> true
  | V.Bool x, V.Bool y -> Bool.equal x y
  | V.Nat x, V.Nat y | V.NegInt x, V.NegInt y | V.Float x, V.Float y -> Int.equal x y
  | V.Str x, V.Str y -> String.equal x y
  | V.Bytes x, V.Bytes y -> List.equal Int.equal x y
  | V.List xs, V.List ys -> List.equal equal xs ys
  | V.Pair (x, x'), V.Pair (y, y') -> equal x y && equal x' y'
  | V.Some x, V.Some y -> equal x y
  | V.Ctor (i, xs), V.Ctor (j, ys) -> Int.equal i j && List.equal equal xs ys
  | V.Ref (k, d), V.Ref (k', d') -> Int.equal k k' && List.equal Int.equal d d'
  | V.Handle (k, x), V.Handle (k', y) -> Int.equal k k' && Int.equal x y
  | ( ( V.Unit | V.Bool _ | V.Nat _ | V.Str _ | V.Bytes _ | V.List _ | V.Pair _ | V.None
      | V.Some _ | V.Ctor _ | V.Ref _ | V.Handle _ | V.NegInt _ | V.Float _ ),
      _ ) -> false
