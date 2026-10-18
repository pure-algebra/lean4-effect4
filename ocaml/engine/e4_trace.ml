(* E4_trace -- the machine event log over Lcnf_array.
   Properties TR1-TR8 are in e4_trace.mli and checked by prop_trace.
   Depends on: Lcnf_array. The array owner also owns conversion to lists. *)

type 'e t = 'e Lcnf_array.t

let empty : 'e t = Lcnf_array.empty
let length (t : 'e t) : int = Lcnf_array.length t
let is_empty (t : 'e t) : bool = Lcnf_array.is_empty t

(* TR2 is the `[] ->` arm: the argument itself, physically.  The general arm appends in list
   order, which is the order `RunMachine.emit` appends in (RunMachine.emit (src/Effect4/Machine/Fibers.lean)). *)
let emit (evs : 'e list) (t : 'e t) : 'e t =
  match evs with
  | [] -> t
  | _ -> List.fold_left Lcnf_array.push t evs
;;

let to_list (t : 'e t) : 'e list = Lcnf_array.to_list t

(* Row i of the finished trace, counted from the front of the emission order — which is the
   vector's own index, so this is one lookup and not a walk. *)
let nth_opt (i : int) (t : 'e t) : 'e option = Lcnf_array.get t i
