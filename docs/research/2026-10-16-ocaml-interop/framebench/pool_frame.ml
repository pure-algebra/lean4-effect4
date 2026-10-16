let tag_list = 4 let tag_pair = 5 let tag_none = 6 let tag_some = 7 let tag_ctor = 10 let tag_nat = 2 let tag_string = 3 let tag_bool = 1
let emit_be64 (b : Buffer.t) (n : int) : unit = Buffer.add_int64_be b (Int64.of_int n)
let emit_frame b tag payload = Buffer.add_char b (Char.chr tag); emit_be64 b (String.length payload); Buffer.add_string b payload
type pool = { buffers : Buffer.t array; mutable top : int }
let pool_key = Domain.DLS.new_key (fun () -> { buffers = Array.make 32 (Buffer.create 1); top = 0 })
let with_payload (b : Buffer.t) (tag : int) (f : Buffer.t -> unit) : unit =
  let pool = Domain.DLS.get pool_key in
  let p = if pool.top > 0 then (pool.top <- pool.top - 1; pool.buffers.(pool.top)) else Buffer.create 256 in
  Buffer.clear p;
  f p;
  Buffer.add_char b (Char.chr tag);
  emit_be64 b (Buffer.length p);
  Buffer.add_buffer b p;
  if Buffer.length p > 65536 then Buffer.reset p;
  let pool = Domain.DLS.get pool_key in
  if pool.top < Array.length pool.buffers then (pool.buffers.(pool.top) <- p; pool.top <- pool.top + 1)
let nat_width n = let rec count m k = if m = 0 then k else count (m lsr 8) (k + 1) in count n 0
let emit_nat b n =
  if n < 0 then invalid_arg "neg";
  let k = nat_width n in
  Buffer.add_char b (Char.chr tag_nat); emit_be64 b k;
  for i = k - 1 downto 0 do Buffer.add_char b (Char.unsafe_chr ((n lsr (8 * i)) land 0xff)) done
let emit_string b s = if not (String.is_valid_utf_8 s) then invalid_arg "utf8"; emit_frame b tag_string s
let emit_bool b v = emit_frame b tag_bool (if v then "\001" else "\000")
let emit_list b f xs = with_payload b tag_list (fun p -> List.iter (f p) xs)
let emit_ctor b index args = with_payload b tag_ctor (fun p -> emit_nat p index; args p)
let to_string f v = let b = Buffer.create 64 in f b v; Buffer.contents b
