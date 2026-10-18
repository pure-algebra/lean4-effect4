(* Lcnf_list -- membership through an instance: the form of the row `List.contains`.

   What it is: `contains inst l a` is Lean's `List.contains l a`, which is `List.elem a l`. Lean's
   `List.elem a (b :: l)` tests `a == b`, so the target `a` is the instance's first argument
   (Lean 4.33.1, `Init/Data/List/Basic.lean`). Mono LCNF passes the `BEq` instance as the
   function itself. The target evaluator runs it from its reference definition in
   `OCaml5.Lcnf.support`.

   Depends on: the standard library only.

   Properties:
   L1  `contains inst l a` applies `inst a e` to each element `e` of `l` in order, and answers
       `true` at the first `true`, or `false` at the end of the list.   tested (test_lcnf)
   L2  An exception that `inst` raises passes through, and no later element is reached.
                                                                        tested (test_lcnf) *)

(** [contains inst l a]: whether [inst a e] holds for some element [e] of [l]. *)
val contains : ('a -> 'a -> bool) -> 'a list -> 'a -> bool
