(* E4_ppath — see e4_ppath.mli.  The spine is reversed and the node rides along. *)

type 'n t =
  { rev : Z.t list
  ; node : 'n option
  ; base : 'n
  }

let make (n : 'n) : 'n t = { rev = []; node = Some n; base = n }
let root (p : 'n t) : 'n = p.base

let snoc (child : 'n -> Z.t -> 'n option) (p : 'n t) (i : Z.t) : 'n t =
  { rev = i :: p.rev
  ; node =
      (match p.node with
       | None -> None
       | Some n -> child n i)
  ; base = p.base
  }
;;

let append (child : 'n -> Z.t -> 'n option) (p : 'n t) (l : Z.t list) : 'n t =
  List.fold_left (fun q i -> snoc child q i) p l
;;

let node (_child : 'n -> Z.t -> 'n option) (p : 'n t) : 'n option = p.node

let rec walk (child : 'n -> Z.t -> 'n option) (n : 'n) (l : Z.t list) : 'n option =
  match l with
  | [] -> Some n
  | i :: rest ->
    (match child n i with
     | None -> None
     | Some m -> walk child m rest)
;;

let to_list (p : 'n t) : Z.t list = List.rev p.rev
let length (p : 'n t) : Z.t = Z.of_int (List.length p.rev)
