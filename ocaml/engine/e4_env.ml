(* E4_env — see e4_env.mli.  The spine is reversed and the length is cached. *)

type 'a t =
  { rev : 'a list
  ; len : int
  }

let empty : 'a t = { rev = []; len = 0 }
let snoc (e : 'a t) (v : 'a) : 'a t = { rev = v :: e.rev; len = e.len + 1 }
let append (e : 'a t) (l : 'a list) : 'a t = List.fold_left snoc e l

let rec nth (l : 'a list) (k : int) : 'a option =
  match l with
  | [] -> None
  | v :: rest -> if k = 0 then Some v else nth rest (k - 1)
;;

(* A natural index past `max_int` is past every environment a heap holds, so it answers
   `None`, as Lean's `env[i]?` does past the length. *)
let get (e : 'a t) (i : Z.t) : 'a option =
  if not (Z.fits_int i)
  then None
  else (
    let i = Z.to_int i in
    if i < 0 || i >= e.len then None else nth e.rev (e.len - 1 - i))
;;

let length (e : 'a t) : Z.t = Z.of_int e.len

let rec drop (l : 'a list) (k : int) : 'a list =
  if k <= 0
  then l
  else (
    match l with
    | [] -> []
    | _ :: rest -> drop rest (k - 1))
;;

let take_int (e : 'a t) (k : int) : 'a t =
  if k >= e.len
  then e
  else if k <= 0
  then empty
  else { rev = drop e.rev (e.len - k); len = k }
;;

(* A count past `max_int` is past every length, so it takes the whole environment, as Lean's
   `List.take` clamps. *)
let take (e : 'a t) (k : Z.t) : 'a t =
  if not (Z.fits_int k)
  then e
  else (
    let k = Z.to_int k in
    take_int e k)
;;

let to_list (e : 'a t) : 'a list = List.rev e.rev
let of_list (l : 'a list) : 'a t = { rev = List.rev l; len = List.length l }
