(* E4_hex — the one hexadecimal codec.  The property list is in e4_hex.mli. *)

(* Digest.hexDigit (Digest.lean:63): 0-9 then a-f, lowercase. *)
let hex_digit (n : int) : char = if n < 10 then Char.unsafe_chr (48 + n) else Char.unsafe_chr (87 + n)

(* Digest.hexVal (Digest.lean:66-70): 0-9, a-f, A-F; -1 stands for `none`. *)
let hex_val (c : int) : int =
  if c >= 48 && c <= 57 then c - 48
  else if c >= 97 && c <= 102 then c - 87
  else if c >= 65 && c <= 70 then c - 55
  else -1

let of_bytes (s : string) : string =
  let n = String.length s in
  let out = Bytes.create (2 * n) in
  for i = 0 to n - 1 do
    let b = Char.code (String.unsafe_get s i) in
    Bytes.unsafe_set out (2 * i) (hex_digit (b lsr 4));
    Bytes.unsafe_set out ((2 * i) + 1) (hex_digit (b land 15))
  done;
  Bytes.unsafe_to_string out

let to_bytes (s : string) : string option =
  let n = String.length s in
  if n land 1 <> 0 then None
  else begin
    let out = Bytes.create (n / 2) in
    let ok = ref true in
    let i = ref 0 in
    while !ok && !i < n do
      let h = hex_val (Char.code (String.unsafe_get s !i)) in
      let l = hex_val (Char.code (String.unsafe_get s (!i + 1))) in
      if h < 0 || l < 0 then ok := false
      else begin
        Bytes.unsafe_set out (!i / 2) (Char.unsafe_chr ((h * 16) + l));
        i := !i + 2
      end
    done;
    if !ok then Some (Bytes.unsafe_to_string out) else None
  end

let digest_of_hex (s : string) : string option =
  match to_bytes s with
  | Some b when String.length b = 32 -> Some b
  | _ -> None
