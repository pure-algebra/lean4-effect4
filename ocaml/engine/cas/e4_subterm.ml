(* E4_subterm — see e4_subterm.mli for what this is and the behaviours it holds itself to. *)

open Effect4_engine

(* ============================================================ 1. families and paths *)

type family = Eff | Stmt | Stmts | Effs | Action

let family_name = function
  | Eff -> "eff"
  | Stmt -> "stmt"
  | Stmts -> "stmts"
  | Effs -> "effs"
  | Action -> "action"

let families = [ Eff; Stmt; Stmts; Effs; Action ]

let family_ctor_names = function
  | Eff -> Eff_types.ctor_names_eff
  | Stmt -> Eff_types.ctor_names_stmt
  | Stmts -> Eff_types.ctor_names_stmts
  | Effs -> Eff_types.ctor_names_effs
  | Action -> Eff_types.ctor_names_action_term

let arity f = List.length (family_ctor_names f)

let path_to_string (p : int list) : string =
  if p = [] then "." else String.concat "." (List.map string_of_int p)

(* ============================================================ 2. the child table

   Transcribed from `Effect4.Program.Node.child` (src/Effect4/Program/Compile.lean:65-115),
   arm for arm, restricted to the constructors `ocaml/eff/eff_types.ml` carries.  The right
   column of each row is the VALUE argument index in `Eff_wire.emit_*` (eff_wire.ml:458-517),
   which is where the two path spaces come apart (M5): the four rows marked M5 below are the
   whole of the divergence in this alphabet.

   There is no default arm that maps a program child to the argument of the same index: M3
   records that `Node.argIndex`'s fallback is wrong, and a table with a fallback is not a
   table.  Every constructor with children is listed; every constructor without them falls to
   the `_ -> []` that says "no children", not "children I did not think about". *)

let children (f : family) (c : int) : (int * family) list =
  match f with
  | Eff -> (
    match c with
    | 5 -> [ (0, Eff) ] (* suspend b *)
    | 7 -> [ (0, Eff); (1, Eff) ] (* bind a b *)
    | 8 -> [ (0, Stmts) ] (* gen ss *)
    | 9 -> [ (0, Eff); (1, Eff) ] (* catchCause b h *)
    | 10 -> [ (0, Eff); (1, Eff); (2, Eff) ] (* matchCause b v c *)
    | 11 -> [ (0, Eff); (1, Eff) ] (* onExit b f *)
    | 12 -> [ (0, Eff) ] (* exit b *)
    | 13 -> [ (0, Eff) ] (* uninterruptible b *)
    | 14 -> [ (0, Eff) ] (* interruptible b *)
    | 15 -> [ (1, Eff); (2, Eff) ] (* branch t a b        -- M5: 0,1 -> 1,2 *)
    | 16 -> [ (3, Eff) ] (* whileLoop i c s b   -- M5: 0   -> 3   *)
    | 20 -> [ (0, Action) ] (* withFiber a *)
    | 21 -> [ (0, Eff) ] (* scoped b *)
    | 22 -> [ (0, Eff); (1, Eff) ] (* acquireRelease a r *)
    | 25 -> [ (2, Eff) ] (* provideService k t e -- M5: 0 -> 2 *)
    | 26 -> [ (1, Eff); (2, Eff) ] (* catchIf t b h -- M5: 0,1 -> 1,2 *)
    | _ -> [])
  | Stmt -> (
    match c with
    | 0 -> [ (0, Eff) ] (* bindYield e *)
    | 1 -> [ (0, Eff) ] (* yieldDiscard e *)
    | 3 -> [ (1, Stmts); (2, Stmts) ] (* ifElse t a b      -- M5: 0,1 -> 1,2 *)
    | 4 -> [ (0, Stmts) ] (* whileTrue b *)
    | _ -> [])
  | Stmts -> ( match c with 1 -> [ (0, Stmt); (1, Stmts) ] (* cons h t *) | _ -> [])
  | Effs -> ( match c with 1 -> [ (0, Eff); (1, Effs) ] (* cons h t *) | _ -> [])
  | Action -> (
    match c with
    | 0 -> [ (0, Eff) ] (* fork p _ *)
    | 1 -> [ (0, Eff) ] (* forkIn p _ _ *)
    | 2 -> [ (0, Eff) ] (* forkScoped p _ *)
    | 11 -> [ (0, Effs) ] (* raceAll es *)
    | _ -> [])

let val_of_prog (f : family) (c : int) (k : int) : int option =
  match List.nth_opt (children f c) k with Some (v, _) -> Some v | None -> None

let prog_of_val (f : family) (c : int) (j : int) : int option =
  let rec go k = function
    | [] -> None
    | (v, _) :: rest -> if v = j then Some k else go (k + 1) rest
  in
  go 0 (children f c)

(* ============================================================ 3. the value side (D3) *)

module Tree = struct
  open Eff_types

  type node =
    | N_eff of Eff_types.eff
    | N_stmt of Eff_types.stmt
    | N_stmts of Eff_types.stmts
    | N_effs of Eff_types.effs
    | N_action of Eff_types.action_term

  let family_of = function
    | N_eff _ -> Eff
    | N_stmt _ -> Stmt
    | N_stmts _ -> Stmts
    | N_effs _ -> Effs
    | N_action _ -> Action

  let ctor_index = function
    | N_eff e -> ctor_index_eff e
    | N_stmt s -> ctor_index_stmt s
    | N_stmts s -> ctor_index_stmts s
    | N_effs e -> ctor_index_effs e
    | N_action a -> ctor_index_action_term a

  (* `Node.child` (Compile.lean:65-115), arm for arm. *)
  let child (n : node) (i : int) : node option =
    match (n, i) with
    | N_eff (Eff_suspend b), 0 -> Some (N_eff b)
    | N_eff (Eff_bind (a, _)), 0 -> Some (N_eff a)
    | N_eff (Eff_bind (_, b)), 1 -> Some (N_eff b)
    | N_eff (Eff_gen ss), 0 -> Some (N_stmts ss)
    | N_eff (Eff_catchCause (b, _)), 0 -> Some (N_eff b)
    | N_eff (Eff_catchCause (_, h)), 1 -> Some (N_eff h)
    | N_eff (Eff_matchCause (b, _, _)), 0 -> Some (N_eff b)
    | N_eff (Eff_matchCause (_, v, _)), 1 -> Some (N_eff v)
    | N_eff (Eff_matchCause (_, _, c)), 2 -> Some (N_eff c)
    | N_eff (Eff_onExit (b, _)), 0 -> Some (N_eff b)
    | N_eff (Eff_onExit (_, f)), 1 -> Some (N_eff f)
    | N_eff (Eff_exit b), 0 -> Some (N_eff b)
    | N_eff (Eff_uninterruptible b), 0 -> Some (N_eff b)
    | N_eff (Eff_interruptible b), 0 -> Some (N_eff b)
    | N_eff (Eff_branch (_, a, _)), 0 -> Some (N_eff a)
    | N_eff (Eff_branch (_, _, b)), 1 -> Some (N_eff b)
    | N_eff (Eff_whileLoop (_, _, _, b)), 0 -> Some (N_eff b)
    | N_eff (Eff_withFiber a), 0 -> Some (N_action a)
    | N_eff (Eff_scoped b), 0 -> Some (N_eff b)
    | N_eff (Eff_acquireRelease (a, _)), 0 -> Some (N_eff a)
    | N_eff (Eff_acquireRelease (_, r)), 1 -> Some (N_eff r)
    | N_eff (Eff_provideService (_, _, b)), 0 -> Some (N_eff b)
    | N_eff (Eff_catchIf (_, b, _)), 0 -> Some (N_eff b)
    | N_eff (Eff_catchIf (_, _, h)), 1 -> Some (N_eff h)
    | N_stmts (Stmts_cons (h, _)), 0 -> Some (N_stmt h)
    | N_stmts (Stmts_cons (_, t)), 1 -> Some (N_stmts t)
    | N_stmt (Stmt_bindYield e), 0 -> Some (N_eff e)
    | N_stmt (Stmt_yieldDiscard e), 0 -> Some (N_eff e)
    | N_stmt (Stmt_ifElse (_, a, _)), 0 -> Some (N_stmts a)
    | N_stmt (Stmt_ifElse (_, _, b)), 1 -> Some (N_stmts b)
    | N_stmt (Stmt_whileTrue b), 0 -> Some (N_stmts b)
    | N_action (Action_term_fork (p, _)), 0 -> Some (N_eff p)
    | N_action (Action_term_forkIn (p, _, _)), 0 -> Some (N_eff p)
    | N_action (Action_term_forkScoped (p, _)), 0 -> Some (N_eff p)
    | N_action (Action_term_raceAll es), 0 -> Some (N_effs es)
    | N_effs (Effs_cons (h, _)), 0 -> Some (N_eff h)
    | N_effs (Effs_cons (_, t)), 1 -> Some (N_effs t)
    | _, _ -> None

  (* `Node.at_` (Compile.lean:118-120). *)
  let rec at_ (n : node) (p : int list) : node option =
    match p with
    | [] -> Some n
    | i :: rest -> ( match child n i with None -> None | Some c -> at_ c rest)

  let encode = function
    | N_eff e -> Eff_wire.encode_eff e
    | N_stmt s -> Eff_wire.encode_stmt s
    | N_stmts s -> Eff_wire.encode_stmts s
    | N_effs e -> Eff_wire.encode_effs e
    | N_action a -> Eff_wire.encode_action_term a

  let of_bytes (s : string) : node option =
    match Eff_wire.decode_program_exact s with None -> None | Some e -> Some (N_eff e)

  let rec subtree_count (n : node) : int =
    let f = family_of n and c = ctor_index n in
    List.fold_left
      (fun acc k -> match child n k with None -> acc | Some ch -> acc + subtree_count ch)
      1
      (List.init (List.length (children f c)) (fun k -> k))
end

(* ============================================================ 4. the index *)

type entry = {
  prog_path : int list;
  val_path : int list;
  family : family;
  ctor : int;
  off : int;
  len : int;
  cid : E4_addr.Cid.t;
}

type t = { t_bytes : string; t_entries : entry array }

let cid_of_bytes (s : string) : E4_addr.Cid.t = E4_addr.Addr.of_digest (E4_sha256.digest s)

exception Malformed

(* The start of every argument frame of a ctor payload, in order.  `from` is the position just
   past the leading nat frame that carries the constructor index (Eff_frame.read_ctor). *)
let arg_positions (s : string) (from : int) (limit : int) : int array =
  let acc = ref [] in
  let cur = ref from in
  while !cur < limit do
    (match Eff_frame.read_frame s !cur limit with
     | None -> raise Malformed
     | Some (_, _, _, next) ->
       if next <= !cur then raise Malformed;
       acc := !cur :: !acc;
       cur := next)
  done;
  if !cur <> limit then raise Malformed;
  Array.of_list (List.rev !acc)

let build (b : string) : t =
  let n = String.length b in
  let acc = ref [] in
  let rec go ~(family : family) ~(prog_rev : int list) ~(val_rev : int list) ~(pos : int)
      ~(limit : int) : unit =
    match Eff_frame.read_ctor b pos limit with
    | None -> raise Malformed
    | Some (ci, after_index, payload_end, next) ->
      let len = next - pos in
      if len <= 0 then raise Malformed;
      let e =
        {
          prog_path = List.rev prog_rev;
          val_path = List.rev val_rev;
          family;
          ctor = ci;
          off = pos;
          len;
          cid = E4_addr.Addr.of_digest (E4_sha256.digest_sub b pos len);
        }
      in
      acc := e :: !acc;
      (match children family ci with
      | [] -> ()
      | rows ->
        let args = arg_positions b after_index payload_end in
        List.iteri
          (fun k (vidx, cf) ->
            if vidx < 0 || vidx >= Array.length args then raise Malformed;
            go ~family:cf ~prog_rev:(k :: prog_rev) ~val_rev:(vidx :: val_rev)
              ~pos:args.(vidx) ~limit:payload_end)
          rows)
  in
  go ~family:Eff ~prog_rev:[] ~val_rev:[] ~pos:0 ~limit:n;
  { t_bytes = b; t_entries = Array.of_list (List.rev !acc) }

(* SB7: exactness is the WIRE's own refusal.  `decode_program_exact` is what says these bytes
   are one program; the walk that follows can then only fail if this module's table and
   `Eff_wire`'s encoder disagree, which is the failure `Malformed` reports. *)
let of_program_opt (b : string) : t option =
  match Eff_wire.decode_program_exact b with
  | None -> None
  | Some _ -> ( try Some (build b) with Malformed -> None)

let of_program (b : string) : t =
  match of_program_opt b with
  | Some t -> t
  | None -> invalid_arg "E4_subterm.of_program: not exactly one well-formed program"

let bytes (t : t) : string = t.t_bytes
let entries (t : t) : entry list = Array.to_list t.t_entries
let count (t : t) : int = Array.length t.t_entries
let root (t : t) : entry = t.t_entries.(0)

let rec path_eq (a : int list) (b : int list) : bool =
  match (a, b) with
  | [], [] -> true
  | x :: xs, y :: ys -> x = y && path_eq xs ys
  | _ -> false

let find_entry (t : t) (pick : entry -> bool) : entry option =
  let n = Array.length t.t_entries in
  let res = ref None in
  let found = ref false in
  let i = ref 0 in
  while (not !found) && !i < n do
    let e = t.t_entries.(!i) in
    if pick e then begin
      res := Some e;
      found := true
    end;
    incr i
  done;
  !res

let at_prog_path (t : t) (p : int list) : entry option =
  find_entry t (fun e -> path_eq e.prog_path p)

let at_val_path (t : t) (p : int list) : entry option =
  find_entry t (fun e -> path_eq e.val_path p)

let family_eq (a : family) (b : family) : bool =
  match (a, b) with
  | Eff, Eff | Stmt, Stmt | Stmts, Stmts | Effs, Effs | Action, Action -> true
  | _ -> false

let entries_at_family (t : t) (f : family) : entry list =
  List.filter (fun e -> family_eq e.family f) (Array.to_list t.t_entries)

let slice (b : string) (e : entry) : string = String.sub b e.off e.len
let slice_of (t : t) (e : entry) : string = slice t.t_bytes e
