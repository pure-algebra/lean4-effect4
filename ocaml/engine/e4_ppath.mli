(* E4_ppath — the position of a point inside a program: a snoc-shared spine that CARRIES
   the node it addresses (docs/research/2026-09-08-engine-prof-chain.md §5.1, finding P-6).

   What it is: the carrier behind `Effect4.Program.Point.path` and
   `Effect4.Machine.Capture.path` (src/Effect4/Program/Compile.lean:127-165).  Lean's field
   is a `List Nat` extended at the TAIL — `p.path ++ [i]` in `Point.child`/`childWith` and at
   nine inline sites — so every child allocates a fresh spine of its parent's length: Σ|path|
   = n(n-1)/2 cons cells at chain-n, which lane PROF measured as 98.5 % of the finished
   machine and 58 % of the run time (P-2, P-3).  Reversed, the extension is a cons: O(1), and
   every prefix is PHYSICALLY SHARED with its parent.

   The second half is `node`.  `Program.resolve` is `Node.at_ (Node.eff root) p.path`, a walk
   of the whole path from the root on every step (501 500 `Node.child` matches at chain-1000,
   P-4).  `snoc` computes the child's node from the PARENT's node with one `Node.child`, so
   the node is already there when `resolve` asks: O(1), pure, no cache and no host state — the
   whole value stays immutable and persistent (brief §2.3).

   The `'n` parameter is the generated `node` type, which is declared INSIDE the functor, so
   the carrier cannot name it: the extern row spells the field `node P.t` through the chain's
   leading-type token (`field Effect4.Program.Point.path @node P.t`).  For the same reason
   `snoc`/`append`/`node`/`walk` take `Node.child` as their first argument rather than closing
   over it.

   This module satisfies the generated functor's `PPATH` signature (src/OCaml5/Lcnf/
   Externs.lean `carrierSignatures`) verbatim; `e4_ppath_list.ml` is its list twin — it
   carries the list and walks on every `node`, which is exactly Lean's meaning — and
   satisfies the same signature.  Both ascriptions are checked in test/prop_point.ml.

   Depends on: the OCaml standard library only (List).

   Representation: { rev : the path, LAST index first; node : the node at that path, or None
   when the path leaves the tree; base : the node the path is rooted at }.  `base` is carried
   so that `node` can answer for a root it was NOT built from (see PP4) instead of assuming
   every caller passes the same root.

   Behaviours (each is a named PASS/FAIL line in test/prop_point.ml):
   PP1 to_list (make n) = [] and to_list (snoc c p i) = to_list p @ [i]      tested
   PP2 snoc is O(1) and allocates one cons + one record; every prefix of the result is
       physically the parent's spine                              by construction; benched
   PP3 node c p = walk c (root p) (to_list p) — the carried node IS `Node.at_` of the
       spine, at every depth and for a path that leaves the tree           tested
   PP4 node is a pure function of the value: no mutation, no memo table, nothing outside
       the record (brief §2.3)                                            by construction
   PP5 append c p l = List.fold_left (snoc c) p l, and to_list (append c p l)
       = to_list p @ l                                                    tested
   PP6 persistence: `p` is unchanged by any snoc/append on it              tested
   PP7 agreement with the list twin on random spine sequences, on both to_list and node
                                                                          tested
   Bound: the path is unbounded in Lean; on this host its length is bounded by the heap. *)

type 'n t

val make : 'n -> 'n t
(** The empty path rooted at this node.  [to_list (make n) = \[\]] and [node c (make n) =
    Some n]. *)

val root : 'n t -> 'n
(** The node [make] was given.  Used by the seam's `Node.at_` row to decide whether the node
    a caller passes is the one this spine was built from. *)

val snoc : ('n -> int -> 'n option) -> 'n t -> int -> 'n t
(** [snoc child p i] is the path [to_list p @ [i]], sharing [p]'s spine, with its node
    computed from [p]'s by one [child] (PP1, PP2). *)

val append : ('n -> int -> 'n option) -> 'n t -> int list -> 'n t
(** [snoc] folded over the list (PP5). *)

val node : ('n -> int -> 'n option) -> 'n t -> 'n option
(** The node this path addresses: [walk child (root p) (to_list p)], answered in O(1) from
    the carried node (PP3).  [child] is taken so that the list twin can walk. *)

val walk : ('n -> int -> 'n option) -> 'n -> int list -> 'n option
(** Lean's `Node.at_`: [child] applied along the list, [None] as soon as one step fails. *)

val to_list : 'n t -> int list
(** The Lean `Point.path` value.  One reversal, O(length); it is what the three observable
    sites (`FinName.memoEntry`, `SyncOp.memoBuild`, `SyncOp.memoGet` — all `LayerId`) are
    handed, so the memo keys and the layer bytes are unchanged. *)

val length : 'n t -> int
(** The depth.  O(length): the spine is not counted, because nothing on the hot path asks. *)
