(* Lcnf_array -- see lcnf_array.mli. The carrier and its `push`, `get`, `slice`, `fold` and
   `to_list` are `E4_log.Vec`'s, moved here unchanged; `set_exn` and `replicate` are the ones slice
   3.1 measured (ocaml/engine/bench/bench_array.ml).

   THE CARRIER, and why each half is what it is.
     `full`     a Map from CHUNK NUMBER (not from element index) to a frozen chunk of
                `chunk_size` elements. The depth is log(n / chunk_size), and the index into a
                chunk is a mask, never a `mod`.
     `tail`     the open chunk, MOST RECENT FIRST, so `push` is one cons. It is turned into a
                frozen array exactly when it reaches `chunk_size`, filled backwards from the tail
                in one pass.
     `tail_len` maintained incrementally, so the promotion test is an int compare.
     `len`      the total, so `length` is O(1).

   V4 in one sentence: `Array.make` and the backward fill happen inside `push` on a list that is
   dropped in the same expression, `set_exn` writes only an `Array.copy` it has just made, and
   `replicate` writes no element after `Array.make`. So no array a `t` can reach is ever written
   after the operation that created it. *)

let chunk_bits = 8
let chunk_size = 1 lsl chunk_bits
let chunk_mask = chunk_size - 1

module Im = Map.Make (Int)

type 'a t = {
  full : 'a array Im.t;  (** chunk number -> the frozen elements of that chunk *)
  tail : 'a list;  (** the open chunk, most recent first *)
  tail_len : int;
  len : int;
}

let empty = { full = Im.empty; tail = []; tail_len = 0; len = 0 }
let with_capacity _ = empty
let length t = t.len
let is_empty t = t.len = 0

let push t x =
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

(* The open tail holds positions [len - tail_len, len - 1] reversed, so position i is at offset
   len - 1 - i in it. *)
let rec nth_tail k = function
  | [] -> None
  | x :: r -> if k = 0 then Some x else nth_tail (k - 1) r

let get t i =
  if i < 0 || i >= t.len then None
  else
    match Im.find_opt (i lsr chunk_bits) t.full with
    | Some a -> Some (Array.unsafe_get a (i land chunk_mask))
    | None -> nth_tail (t.len - 1 - i) t.tail

let outside name t i =
  invalid_arg (Printf.sprintf "Lcnf_array.%s: %d outside [0,%d)" name i t.len)

let get_exn t i =
  match get t i with
  | Some x -> x
  | None -> outside "get_exn" t i

let rec replace_nth k v = function
  | [] -> []
  | x :: r -> if k = 0 then v :: r else x :: replace_nth (k - 1) v r

(* A frozen chunk is copied before its element is written, so every value that shares it keeps
   its elements (V4); the open tail is a list, rebuilt up to the element. *)
let set_exn t i v =
  if i < 0 || i >= t.len then outside "set_exn" t i
  else
    match Im.find_opt (i lsr chunk_bits) t.full with
    | Some a ->
      let a = Array.copy a in
      a.(i land chunk_mask) <- v;
      { t with full = Im.add (i lsr chunk_bits) a t.full }
    | None -> { t with tail = replace_nth (t.len - 1 - i) v t.tail }

(* Descending walk, so the result is built by consing and never reversed. *)
let slice t ~from ~upto =
  let lo = if from < 0 then 0 else from and hi = if upto > t.len then t.len else upto in
  let rec go i acc = if i < lo then acc else go (i - 1) (get_exn t i :: acc) in
  if hi <= lo then [] else go (hi - 1) []

(* Ascending, and NOT via `get`: the frozen chunks are walked in `Im.iter`'s own ascending key
   order and the open tail by a bounded (<= chunk_size) recursion that applies `f` on the way
   OUT, so the whole fold costs one visit per element and no map lookup per element. *)
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

let fold_left f init t = fold t ~init ~f:(fun _ x acc -> f acc x)

(* Index order through `fold`: the ascending walk conses the elements most recent first, and one
   `List.rev` turns them. *)
let to_list t = List.rev (fold t ~init:[] ~f:(fun _ x acc -> x :: acc))

let append_list t xs = List.fold_left push t xs
let of_list xs = append_list empty xs

(* One frozen chunk serves every full chunk: nothing writes it, and `set_exn` copies it. *)
let replicate n v =
  if n <= 0 then empty
  else
    let a = Array.make chunk_size v and full_chunks = n lsr chunk_bits and tail_len = n land chunk_mask in
    let rec chunks c m = if c = full_chunks then m else chunks (c + 1) (Im.add c a m) in
    { full = chunks 0 Im.empty; tail = List.init tail_len (fun _ -> v); tail_len; len = n }
