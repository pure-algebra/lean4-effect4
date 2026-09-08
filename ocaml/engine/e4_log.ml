(* e4_log.ml — the append-only log as a persistent chunked vector.
   The property list L1-L5, the measurement and the `E4_trace` follow-up are in e4_log.mli.

   THE CARRIER, and why each half is what it is.
     `full`     a Map from CHUNK NUMBER (not from row index) to a frozen 256-row array.  The
                depth is log(n / 256), so a random `get` at 1e6 rows walks 12 nodes and not
                20; the array index is a mask, never a `mod`.
     `tail`     the open chunk, MOST RECENT FIRST, so `append` is one cons.  It is promoted
                to a frozen array exactly when it reaches `chunk_size`, and the array is
                filled backwards from the tail in one pass -- one `List.rev` is what the
                probe's `chunk` candidate avoided and it is why append measures 76 M rows/s
                (design §6.3) against `revlist`'s 36 M and `Map.Make(Int)`'s 6.5 M.
     `tail_len` maintained incrementally, so the promotion test is an int compare.
     `len`      the total, so `length` is O(1) -- the reading axis asks for it per row.

   L5 in one sentence: `Array.make` + the backward fill happen inside `append` on a list
   that is dropped in the same expression, and no other function in this file writes an
   array element.  So no array a `t` can reach is ever written after the `append` that
   created it, and a saved value holds no mutable structure anything can observe. *)

let chunk_bits = 8
let chunk_size = 1 lsl chunk_bits
let chunk_mask = chunk_size - 1

module Im = Map.Make (Int)

module Vec = struct
  type 'a t = {
    full : 'a array Im.t;  (** chunk number -> the frozen 256 rows of that chunk *)
    tail : 'a list;  (** the open chunk, most recent first *)
    tail_len : int;
    len : int;
  }

  let empty = { full = Im.empty; tail = []; tail_len = 0; len = 0 }
  let length t = t.len
  let is_empty t = t.len = 0

  let append t x =
    let tail = x :: t.tail and tail_len = t.tail_len + 1 and len = t.len + 1 in
    if tail_len = chunk_size then begin
      let a = Array.make chunk_size x in
      let rec fill i = function
        | [] -> ()
        | y :: rest ->
          a.(i) <- y;
          fill (i - 1) rest
      in
      fill (chunk_size - 1) tail;
      { full = Im.add ((len - 1) lsr chunk_bits) a t.full; tail = []; tail_len = 0; len }
    end
    else { t with tail; tail_len; len }

  (* The open tail holds positions [len - tail_len, len - 1] reversed, so position i is at
     offset len - 1 - i in it. *)
  let rec nth_tail k = function
    | [] -> None
    | x :: r -> if k = 0 then Some x else nth_tail (k - 1) r

  let get t i =
    if i < 0 || i >= t.len then None
    else
      match Im.find_opt (i lsr chunk_bits) t.full with
      | Some a -> Some (Array.unsafe_get a (i land chunk_mask))
      | None -> nth_tail (t.len - 1 - i) t.tail

  let get_exn t i =
    match get t i with
    | Some x -> x
    | None -> invalid_arg (Printf.sprintf "E4_log.Vec.get_exn: %d outside [0,%d)" i t.len)

  (* Descending walk, so the result is built by consing and never reversed. *)
  let slice t ~from ~upto =
    let lo = if from < 0 then 0 else from and hi = if upto > t.len then t.len else upto in
    let rec go i acc = if i < lo then acc else go (i - 1) (get_exn t i :: acc) in
    if hi <= lo then [] else go (hi - 1) []

  let to_list t = slice t ~from:0 ~upto:t.len

  (* Ascending, and NOT via `get`: the frozen chunks are walked in `Im.iter`'s own ascending
     key order and the open tail by a bounded (<= chunk_size) recursion that applies `f` on
     the way OUT, so the whole fold costs one visit per row and no map lookup per row.  This
     is the call `E4_logindex.of_log` sits on, and it is what the B-Q3c floor measures. *)
  let fold t ~init ~f =
    let acc = ref init in
    Im.iter
      (fun c a ->
         let base = c lsl chunk_bits in
         for j = 0 to chunk_size - 1 do
           acc := f (base + j) (Array.unsafe_get a j) !acc
         done)
      t.full;
    let rec asc i l =
      match l with
      | [] -> ()
      | x :: r ->
        asc (i - 1) r;
        acc := f i x !acc
    in
    asc (t.len - 1) t.tail;
    !acc

  let of_list xs = List.fold_left append empty xs
end

type row = string
type t = row Vec.t

let empty = Vec.empty
let length = Vec.length
let append = Vec.append
let append_all t rows = List.fold_left Vec.append t rows
let get = Vec.get
let slice = Vec.slice
let fold = Vec.fold
let to_list = Vec.to_list
let of_list = Vec.of_list
