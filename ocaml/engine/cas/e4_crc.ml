(* E4_crc — CRC-32 (IEEE 802.3, reflected) and the four bytes a checksum field occupies.
   The property list is in e4_crc.mli.

   Table-driven: 256 entries built once at module initialisation from the reflected
   polynomial 0xEDB88320.  The running value carried between calls is the FINISHED crc of
   the prefix (zlib's convention), so `init` is the crc of the empty string and
   `update (update init a) b = string (a ^ b)` with no separate `finish`. *)

let poly = 0xEDB88320
let mask = 0xFFFFFFFF

let table =
  let t = Array.make 256 0 in
  for n = 0 to 255 do
    let c = ref n in
    for _ = 0 to 7 do
      c := if !c land 1 <> 0 then poly lxor (!c lsr 1) else !c lsr 1
    done;
    t.(n) <- !c
  done;
  t

let init = 0

let update_sub (crc : int) (s : string) (pos : int) (len : int) : int =
  if pos < 0 || len < 0 || pos + len > String.length s then
    invalid_arg "E4_crc.update_sub: window out of range";
  if crc < 0 || crc > mask then invalid_arg "E4_crc.update_sub: crc is not a 32-bit value";
  let c = ref (lnot crc land mask) in
  for i = pos to pos + len - 1 do
    c := Array.unsafe_get table ((!c lxor Char.code (String.unsafe_get s i)) land 0xff)
         lxor (!c lsr 8)
  done;
  lnot !c land mask

let update (crc : int) (s : string) : int = update_sub crc s 0 (String.length s)

let update_char (crc : int) (c : char) : int =
  if crc < 0 || crc > mask then invalid_arg "E4_crc.update_char: crc is not a 32-bit value";
  let x = lnot crc land mask in
  let x = Array.unsafe_get table ((x lxor Char.code c) land 0xff) lxor (x lsr 8) in
  lnot x land mask

let string (s : string) : int = update_sub init s 0 (String.length s)

let sub (s : string) (pos : int) (len : int) : int = update_sub init s pos len

(* ---- the checksum field: four big-endian bytes (§1.2 `be32 rec_crc`) ---- *)

let be32 (n : int) : string =
  if n < 0 || n > mask then invalid_arg "E4_crc.be32: not a 32-bit value";
  let b = Bytes.create 4 in
  for i = 0 to 3 do
    Bytes.unsafe_set b i (Char.unsafe_chr ((n lsr (8 * (3 - i))) land 0xff))
  done;
  Bytes.unsafe_to_string b

let read_be32 (s : string) (pos : int) : int option =
  if pos < 0 || pos + 4 > String.length s then None
  else begin
    let n = ref 0 in
    for i = 0 to 3 do
      n := (!n lsl 8) lor Char.code (String.unsafe_get s (pos + i))
    done;
    Some !n
  end

let field_length = 4
