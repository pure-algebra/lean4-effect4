(* E4_ppath_list — the LIST twin of E4_ppath: the same signature (`PPATH`,
   src/OCaml5/Lcnf/Externs.lean `carrierSignatures`), backed by the list Lean actually
   carries, in path order.

   It reproduces `Effect4.Program.Point.child` (src/Effect4/Program/Compile.lean:149-150,
   `path := p.path ++ [i]`) and `Effect4.Program.resolve`'s
   `Node.at_ (Node.eff root) p.path` (:169) operation for operation: `snoc` copies the whole
   spine and `node` WALKS from the root every time.  So `Ref` still means what Lean means, and
   the only difference from E4_ppath is the Θ(depth) per step that lane PROF measured — which
   is the point of the differential (test/test_diff.ml, `Ref` vs `Fast`).

   Depends on: the OCaml standard library only (List).

   Behaviours:
   PLT1 to_list is the identity on the stored list: the carrier IS the path
                                                                        by construction
   PLT2 snoc c p i = p @ [i], a full copy, and it ignores `c`            by construction
   PLT3 node c p = walk c base p, the whole walk from the root, on every call
                                                                        by construction *)

type 'n t = { path : int list; base : 'n }

let make (n : 'n) : 'n t = { path = []; base = n }

let root (p : 'n t) : 'n = p.base

let snoc (_child : 'n -> int -> 'n option) (p : 'n t) (i : int) : 'n t =
  { p with path = p.path @ [ i ] }

let rec walk (child : 'n -> int -> 'n option) (n : 'n) (l : int list) : 'n option =
  match l with
  | [] -> Some n
  | i :: rest -> (match child n i with None -> None | Some m -> walk child m rest)

let append (child : 'n -> int -> 'n option) (p : 'n t) (l : int list) : 'n t =
  List.fold_left (fun q i -> snoc child q i) p l

let node (child : 'n -> int -> 'n option) (p : 'n t) : 'n option = walk child p.base p.path

let to_list (p : 'n t) : int list = p.path

let length (p : 'n t) : int = List.length p.path
