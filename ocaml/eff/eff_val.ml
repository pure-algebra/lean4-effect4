(* Eff_val — a value's canonical frames (hand-written), the lanes' one writer and reader.

   What it is: `Val.encode` of src/Effect4/Store/Carrier/Val.lean, as OCaml over Eff_frame, for
   `Eff_types.val_`. The engine's lanes compare a value by these bytes: the scenarios lane
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
                                                                tested (test_scenarios S3) *)

let string_of_codes (codes : int list) : string =
  String.init (List.length codes) (fun i -> Char.chr (List.nth codes i))

let be64 (n : int) : string =
  let b = Buffer.create 8 in
  Eff_frame.emit_be64 b n;
  Buffer.contents b

(* The frames of `Val.encode`. *)
let rec emit (b : Buffer.t) (v : Eff_types.val_) : unit =
  match v with
  | Eff_types.Val_unit -> Eff_frame.emit_unit b ()
  | Eff_types.Val_bool x -> Eff_frame.emit_bool b x
  | Eff_types.Val_nat n -> Eff_frame.emit_nat b n
  | Eff_types.Val_str s -> Eff_frame.emit_string b s
  | Eff_types.Val_bytes codes -> Eff_frame.emit_frame b Eff_frame.tag_bytes (string_of_codes codes)
  | Eff_types.Val_list xs -> Eff_frame.emit_list b emit xs
  | Eff_types.Val_pair (x, y) -> Eff_frame.emit_pair b emit emit (x, y)
  | Eff_types.Val_none -> Eff_frame.emit_option b emit None
  | Eff_types.Val_some x -> Eff_frame.emit_option b emit (Some x)
  | Eff_types.Val_ctor (index, args) -> Eff_frame.emit_ctor b index (fun p -> List.iter (emit p) args)
  | Eff_types.Val_ref (kind, digest) -> Eff_frame.emit_ref b (kind, string_of_codes digest)
  | Eff_types.Val_handle (kind, key) -> Eff_frame.emit_handle b (kind, key)
  | Eff_types.Val_negInt n -> Eff_frame.emit_frame b Eff_frame.tag_int (Eff_frame.nat_digits n)
  | Eff_types.Val_float bits -> Eff_frame.emit_frame b Eff_frame.tag_float (be64 bits)

(* A value's canonical bytes. *)
let to_bytes (v : Eff_types.val_) : string = Eff_frame.to_string emit v

(* The reader of the same frames (V2). *)
let rec decode : Eff_types.val_ Eff_frame.decoder =
 fun s pos limit ->
  match Eff_frame.read_frame s pos limit with
  | None -> None
  | Some (tag, p, e, next) ->
    if tag = Eff_frame.tag_unit then if p = e then Some (Eff_types.Val_unit, next) else None
    else if tag = Eff_frame.tag_bool then
      Option.map (fun (x, n) -> (Eff_types.Val_bool x, n)) (Eff_frame.decode_bool s pos limit)
    else if tag = Eff_frame.tag_nat then
      Option.map (fun (x, n) -> (Eff_types.Val_nat x, n)) (Eff_frame.decode_nat s pos limit)
    else if tag = Eff_frame.tag_string then
      Option.map (fun (x, n) -> (Eff_types.Val_str x, n)) (Eff_frame.decode_string s pos limit)
    else if tag = Eff_frame.tag_list then
      Option.map (fun (xs, n) -> (Eff_types.Val_list xs, n)) (Eff_frame.decode_list decode s pos limit)
    else if tag = Eff_frame.tag_pair then
      Option.map
        (fun ((x, y), n) -> (Eff_types.Val_pair (x, y), n))
        (Eff_frame.decode_pair decode decode s pos limit)
    else if tag = Eff_frame.tag_none || tag = Eff_frame.tag_some then
      Option.map
        (fun (o, n) -> ((match o with None -> Eff_types.Val_none | Some x -> Eff_types.Val_some x), n))
        (Eff_frame.decode_option decode s pos limit)
    else if tag = Eff_frame.tag_int then
      Option.map (fun (n, next) -> (Eff_types.Val_negInt n, next)) (Eff_frame.decode_neg_int s pos limit)
    else if tag = Eff_frame.tag_ctor then
      match Eff_frame.read_ctor s pos limit with
      | None -> None
      | Some (index, p', e', next') ->
        let rec args p acc =
          if p = e' then Some (List.rev acc)
          else match decode s p e' with None -> None | Some (x, p'') -> args p'' (x :: acc)
        in
        Option.map (fun xs -> (Eff_types.Val_ctor (index, xs), next')) (args p' [])
    else None

(* Exactly one value: trailing bytes are a refusal. *)
let decode_exact (s : string) : Eff_types.val_ option = Eff_frame.exact decode s
