(* E4_sha256 — SHA-256 (FIPS 180-4).  The property list is in e4_sha256.mli.

   Words are OCaml ints masked to 32 bits (`land 0xffffffff`); on this host an int is 63
   bits, so a sum of four 32-bit words never leaves the range before the mask. *)

let digest_length = 32
let block_length = 64

let mask32 = 0xffffffff

(* FIPS 180-4 §4.2.2: the first 32 bits of the fractional parts of the cube roots of the
   first sixty-four primes. *)
let k =
  [| 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4;
     0xab1c5ed5; 0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe;
     0x9bdc06a7; 0xc19bf174; 0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f;
     0x4a7484aa; 0x5cb0a9dc; 0x76f988da; 0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
     0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967; 0x27b70a85; 0x2e1b2138; 0x4d2c6dfc;
     0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85; 0xa2bfe8a1; 0xa81a664b;
     0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070; 0x19a4c116;
     0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
     0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7;
     0xc67178f2 |]

(* §5.3.3: the first 32 bits of the fractional parts of the square roots of the first
   eight primes. *)
let init_h =
  [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab;
     0x5be0cd19 |]

type ctx = {
  h : int array;            (* eight 32-bit words *)
  w : int array;            (* the 64-word message schedule, reused *)
  block : Bytes.t;          (* the partial block, 64 bytes *)
  mutable used : int;       (* bytes held in `block` *)
  mutable total : int;      (* bytes fed so far *)
  mutable finished : bool;
}

let create () =
  { h = Array.copy init_h;
    w = Array.make 64 0;
    block = Bytes.create block_length;
    used = 0;
    total = 0;
    finished = false }

let rotr x n = ((x lsr n) lor (x lsl (32 - n))) land mask32

(* One block, read straight out of [s] at [off].  [s] must hold 64 bytes there. *)
let compress (c : ctx) (s : string) (off : int) : unit =
  let w = c.w in
  for i = 0 to 15 do
    let j = off + (4 * i) in
    w.(i) <-
      (Char.code (String.unsafe_get s j) lsl 24)
      lor (Char.code (String.unsafe_get s (j + 1)) lsl 16)
      lor (Char.code (String.unsafe_get s (j + 2)) lsl 8)
      lor Char.code (String.unsafe_get s (j + 3))
  done;
  for i = 16 to 63 do
    let x = Array.unsafe_get w (i - 15) in
    let s0 = rotr x 7 lxor rotr x 18 lxor (x lsr 3) in
    let y = Array.unsafe_get w (i - 2) in
    let s1 = rotr y 17 lxor rotr y 19 lxor (y lsr 10) in
    Array.unsafe_set w i
      ((Array.unsafe_get w (i - 16) + s0 + Array.unsafe_get w (i - 7) + s1) land mask32)
  done;
  let h = c.h in
  let a = ref h.(0) and b = ref h.(1) and cc = ref h.(2) and d = ref h.(3) in
  let e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
  for i = 0 to 63 do
    let s1 = rotr !e 6 lxor rotr !e 11 lxor rotr !e 25 in
    let ch = (!e land !f) lxor (lnot !e land mask32 land !g) in
    let t1 = (!hh + s1 + ch + Array.unsafe_get k i + Array.unsafe_get w i) land mask32 in
    let s0 = rotr !a 2 lxor rotr !a 13 lxor rotr !a 22 in
    let maj = (!a land !b) lxor (!a land !cc) lxor (!b land !cc) in
    let t2 = (s0 + maj) land mask32 in
    hh := !g;
    g := !f;
    f := !e;
    e := (!d + t1) land mask32;
    d := !cc;
    cc := !b;
    b := !a;
    a := (t1 + t2) land mask32
  done;
  h.(0) <- (h.(0) + !a) land mask32;
  h.(1) <- (h.(1) + !b) land mask32;
  h.(2) <- (h.(2) + !cc) land mask32;
  h.(3) <- (h.(3) + !d) land mask32;
  h.(4) <- (h.(4) + !e) land mask32;
  h.(5) <- (h.(5) + !f) land mask32;
  h.(6) <- (h.(6) + !g) land mask32;
  h.(7) <- (h.(7) + !hh) land mask32

(* The feed that does not touch [total]; [finish] uses it for the padding. *)
let feed (c : ctx) (s : string) (pos : int) (len : int) : unit =
  let i = ref pos in
  let left = ref len in
  if c.used > 0 then begin
    let take = if !left < block_length - c.used then !left else block_length - c.used in
    Bytes.blit_string s !i c.block c.used take;
    c.used <- c.used + take;
    i := !i + take;
    left := !left - take;
    if c.used = block_length then begin
      compress c (Bytes.unsafe_to_string c.block) 0;
      c.used <- 0
    end
  end;
  while !left >= block_length do
    compress c s !i;
    i := !i + block_length;
    left := !left - block_length
  done;
  if !left > 0 then begin
    Bytes.blit_string s !i c.block 0 !left;
    c.used <- !left
  end

let update (c : ctx) (s : string) (pos : int) (len : int) : unit =
  if c.finished then invalid_arg "E4_sha256.update: context already finished";
  if pos < 0 || len < 0 || pos + len > String.length s then
    invalid_arg "E4_sha256.update: window out of range";
  c.total <- c.total + len;
  feed c s pos len

let update_string (c : ctx) (s : string) : unit = update c s 0 (String.length s)

let finish (c : ctx) : string =
  if c.finished then invalid_arg "E4_sha256.finish: context already finished";
  let bitlen = c.total * 8 in
  (* 0x80, then zeros, then the 64-bit big-endian bit length, to a multiple of 64. *)
  let r = (c.used + 9) mod block_length in
  let padlen = if r = 0 then 0 else block_length - r in
  let tail = Bytes.make (1 + padlen + 8) '\000' in
  Bytes.unsafe_set tail 0 '\x80';
  for j = 0 to 7 do
    Bytes.unsafe_set tail (1 + padlen + j)
      (Char.unsafe_chr ((bitlen lsr (8 * (7 - j))) land 0xff))
  done;
  feed c (Bytes.unsafe_to_string tail) 0 (Bytes.length tail);
  c.finished <- true;
  let out = Bytes.create digest_length in
  for i = 0 to 7 do
    let v = c.h.(i) in
    Bytes.unsafe_set out (4 * i) (Char.unsafe_chr ((v lsr 24) land 0xff));
    Bytes.unsafe_set out ((4 * i) + 1) (Char.unsafe_chr ((v lsr 16) land 0xff));
    Bytes.unsafe_set out ((4 * i) + 2) (Char.unsafe_chr ((v lsr 8) land 0xff));
    Bytes.unsafe_set out ((4 * i) + 3) (Char.unsafe_chr (v land 0xff))
  done;
  Bytes.unsafe_to_string out

let digest_sub (s : string) (pos : int) (len : int) : string =
  let c = create () in
  update c s pos len;
  finish c

let digest (s : string) : string = digest_sub s 0 (String.length s)

let hex (s : string) : string = E4_hex.of_bytes (digest s)
