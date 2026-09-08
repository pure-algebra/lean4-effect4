(* E4_addr — Addr / Ref / Cid / Handle.  The property list is in e4_addr.mli. *)

open Effect4_engine

module Addr = struct
  type t = string                      (* exactly 32 raw bytes; AD1 *)

  let length = 32

  let of_digest (s : string) : t =
    if String.length s <> length then
      invalid_arg "E4_addr.Addr.of_digest: a digest is exactly 32 bytes";
    s

  let of_digest_opt (s : string) : t option =
    if String.length s = length then Some s else None

  let bytes (t : t) : string = t

  (* AD2: forwarded, never reimplemented (Digest.hex / Digest.ofHex?, Digest.lean:252-259). *)
  let hex (t : t) : string = E4_hex.of_bytes t
  let of_hex (s : string) : t option = E4_hex.digest_of_hex s

  let equal : t -> t -> bool = String.equal
  let compare : t -> t -> int = String.compare

  (* AD6/D1: the leading 62 bits, non-negative.  Built in two 32-bit halves so nothing
     overflows the 63-bit host int: value = (hi * 2^32 + lo) lsr 2 = hi lsl 30 lor lo lsr 2,
     and hi lsl 30 < 2^62 because hi < 2^32. *)
  let prefix63 (t : t) : int =
    let b i = Char.code (String.unsafe_get t i) in
    let hi = (b 0 lsl 24) lor (b 1 lsl 16) lor (b 2 lsl 8) lor b 3 in
    let lo = (b 4 lsl 24) lor (b 5 lsl 16) lor (b 6 lsl 8) lor b 7 in
    (hi lsl 30) lor (lo lsr 2)

  let zero : t = String.make length '\000'
end

module Ref = struct
  type t = { kind : E4_kind.t; addr : Addr.t }

  let make (kind : E4_kind.t) (addr : Addr.t) : t = { kind; addr }

  let present (r : t) : string = E4_kind.name r.kind ^ ":" ^ Addr.hex r.addr

  (* "<kind>:<hex>": exactly one colon, a registered kind name, 64 hex characters. *)
  let parse (s : string) : t option =
    match String.index_opt s ':' with
    | None -> None
    | Some i ->
      let rest = String.sub s (i + 1) (String.length s - i - 1) in
      if String.contains rest ':' then None                    (* the Cid form is refused *)
      else
        (match E4_kind.of_name (String.sub s 0 i), Addr.of_hex rest with
         | Some k, Some a -> Some { kind = k; addr = a }
         | _ -> None)

  let equal (a : t) (b : t) : bool = E4_kind.equal a.kind b.kind && Addr.equal a.addr b.addr

  let compare (a : t) (b : t) : int =
    let c = E4_kind.compare a.kind b.kind in
    if c <> 0 then c else Addr.compare a.addr b.addr
end

module Cid = struct
  type t = Addr.t

  let present (k : E4_kind.t) (c : t) : string =
    E4_kind.name k ^ ":cid:" ^ Addr.hex c

  (* "<kind>:cid:<hex>": exactly two colons, the middle segment "cid". *)
  let parse (s : string) : (E4_kind.t * t) option =
    match String.index_opt s ':' with
    | None -> None
    | Some i ->
      let rest = String.sub s (i + 1) (String.length s - i - 1) in
      (match String.index_opt rest ':' with
       | None -> None                                          (* the Ref form is refused *)
       | Some j ->
         if String.sub rest 0 j <> "cid" then None
         else
           let hex = String.sub rest (j + 1) (String.length rest - j - 1) in
           if String.contains hex ':' then None
           else
             (match E4_kind.of_name (String.sub s 0 i), Addr.of_hex hex with
              | Some k, Some a -> Some (k, a)
              | _ -> None))

  let equal : t -> t -> bool = Addr.equal
end

module Handle = struct
  type t =
    | Direct of { addr : Addr.t; seg : int; off : int; len : int }
    | Located of Addr.t

  let direct ~addr ~seg ~off ~len = Direct { addr; seg; off; len }
  let located (a : Addr.t) : t = Located a

  let addr = function Direct d -> d.addr | Located a -> a
end
