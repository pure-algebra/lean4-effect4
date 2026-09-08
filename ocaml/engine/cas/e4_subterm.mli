(* E4_subterm — the subterm index of a program: every subterm's path, its byte range in the
   program's own canonical bytes, and its `Cid`.

   What it is: the index of 2026-09-08-cas-repository-algebra.md §3.5 and §6 and of A2 §1.6's
   `E4_index.Subterm`, built from the WIRE.  For a program's canonical bytes — the bytes
   `ocaml/eff/eff_wire.ml` writes and reads exactly (`encode_program` / `decode_program_exact`,
   eff_wire.ml:1056-1058) — every subterm at a `ProgPath` occupies a contiguous byte range of
   the whole, and the subterm's OWN encoding is exactly that slice.  That is `slice_atPath`,
   proved in Lean over `Val` (repository algebra §2.2, probe 2: `∃ off, (encode v).drop off
   .take (encode c).length = encode c`); here it is a law this module holds itself to and the
   test checks on all 37 goldens of `ocaml/eff/goldens` and on every constructor of every
   family.

   Why it is built from the wire and not from a Lean emitter.  Amendment M18 rules that the
   subterm index is `TreeSig`-driven — a rose-tree signature the generator can emit as
   `effSig`, retiring M3's hand table.  That emitter does not exist in the tree today
   (`src/Effect4/Program/Subterm.lean` is commit 6 of the CAS packet and is not landed), so
   this module carries the `TreeSig` children function by hand, transcribed from
   `Effect4.Program.Node.child` (src/Effect4/Program/Compile.lean:65-115), and golden G9 —
   "for each constructor of each family, the `ProgPath -> ValPath` mapping and one
   `(path, off, len, cid)` entry with the slice equal to the subterm's own bytes" (A2 §4.1) —
   is what will pin it against Lean.  Until G9 is cut, the evidence is this module's own
   double-entry: the BYTE side walks the frames of the encoded program, the VALUE side
   (`Tree`) walks the decoded `Eff_types` tree with a separately written `child`, and the test
   requires them to agree at every node of every golden.

   THE TWO PATH SPACES (amendment M5, and the reason this module exists at all).  A `ProgPath`
   is a list of child indices in `Node.child`; a `ValPath` is a list of argument indices in the
   encoded tree.  They are NOT equal, and M3 records that `Node.argIndex`'s fallback "program
   child i = value argument i" is wrong.  In the alphabet `ocaml/eff/eff_types.ml` carries they
   differ at exactly four constructors:

     eff  branch    (term, eff, eff)          prog 0,1 -> val 1,2
     eff  whileLoop (term, term, term, eff)   prog 0   -> val 3
     eff  choose    (nat, eff, eff)           prog 0,1 -> val 1,2
     stmt ifElse    (term, stmts, stmts)      prog 0,1 -> val 1,2

   (Lean's `Eff` has three arms this wire does not — `provideLayer`, `service`,
   `provideService` — and `provideService` is M3's own example of the broken fallback.  They
   are absent from `Eff_types` (`ocaml/engine/e4_program.mli` P3: the wire's constructors are a
   PREFIX of the engine's, 24 against 27), so no entry of this table can name them; when they
   join the wire, `children` gains three rows and G9 catches their absence.)

   Depends on: E4_addr, E4_sha256 (ocaml/engine, lane M), Eff_frame / Eff_types / Eff_wire
   (ocaml/eff, read-only).  It writes no second framing reader: `Eff_frame.read_frame` and
   `Eff_frame.read_ctor` are the only decoders it uses, and the value side is `Eff_wire`'s own.

   Behaviours:
   SB1 SLICE (L-SUB-1, `slice_atPath`).  For every entry `e` of `of_program bytes`,
       `String.sub bytes e.off e.len` is exactly the encoding of the node
       `Tree.at_ root e.prog_path` names — `Tree.encode` of it, byte for byte.
                                                   tested (S1: all 37 goldens; S2: every ctor)
   SB2 The root is the whole: the first entry is `{ prog_path = []; val_path = []; off = 0;
       len = String.length bytes }` and its slice is the program.               tested (S3)
   SB3 CID.  `e.cid` is `sha256` of the slice — the payload digest of the subterm as a program
       (amendment M6: a `Cid` erases the kind).  Two occurrences of one subterm, in one program
       or in two, have equal `cid` and different `off`.                          tested (S4)
   SB4 TWO PATH SPACES (L-SUB-2, M5).  `val_path` is the `ProgPath` mapped through `children`
       and it differs from `prog_path` at exactly `branch`, `whileLoop`, `choose` and
       `ifElse`; `prog_of_val`/`val_of_prog` are the two directions and each is the other's
       inverse where both are defined.                                        tested (S5, S6)
   SB5 TABLE-DRIVEN, NO FALLBACK (L-SUB-3, M3).  `children` enumerates every constructor of
       every family — 24 `eff`, 6 `stmt`, 2 `stmts`, 2 `effs`, 16 `action_term`, fifty in all —
       and there is no "child i = argument i" default anywhere in this module.  The test walks
       a witness of EVERY constructor, not the corpus.                          tested (S2, S7)
   SB6 Order: `entries` is the pre-order of the program — a node before its children, children
       in `ProgPath` order — so `entries |> List.hd` is the root and a parent always precedes
       every descendant.                                                        tested (S3, S8)
   SB7 Total and exact: `of_program_opt` answers None for bytes that are not exactly one
       well-formed `eff` frame tree (a short frame, a trailing byte, an unregistered
       constructor index, an argument count the constructor does not have), and never a partial
       index.  `of_program` raises `Invalid_argument` on the same inputs.       tested (S9)
   SB8 It is a CACHE (L-IDX-0).  Identity: the program's canonical bytes.  Rebuild:
       `of_program` of those bytes — one walk, no store, no file, no lock.  Dropping the whole
       index and rebuilding it changes no answer, because the index is a function of the bytes
       and of nothing else.                                                    tested (S10)

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.6's `Subterm` (lane P7,
   2026-09-08).  Nothing named there is missing or renamed.

   D1  §1.6's `entry` has no family, and it must: a `ProgPath` addresses nodes of five mutually
       recursive families (`Node` is `eff | stmts | stmt | action | effs`, Compile.lean:51-59)
       and `at_prog_path` cannot say what it found without one.  `family` is added to `entry`.
   D2  §1.6 says `of_program : string -> t` and does not say what a malformed program does.
       `of_program` raises and `of_program_opt` is added (SB7); nothing in this estate should
       be building an index of bytes that are not a program.
   D3  `Tree` is added: the VALUE side of the index — `Node.child` (Compile.lean:65-115) and
       the family encoders of `Eff_wire`, as OCaml.  It is the second, independent computation
       SB1 is checked against, and it is `effSig`'s `children` half (M18) in the shape a
       generator will later emit.  When `src/Effect4/Program/Subterm.lean` lands, `Tree.child`
       becomes the thing G9 pins and this file's hand table is deleted.
   D4  Added beside §1.6's list: `count`, `root`, `bytes`, `slice_of`, `at_val_path`,
       `entries_at_family`, `children`, `arity`, `family_ctor_names`, `prog_of_val`,
       `val_of_prog`, `cid_of_bytes`, and `family_name` / `path_to_string` for messages. *)

(* ============================================================ families and paths *)

type family =
  | Eff
  | Stmt
  | Stmts
  | Effs
  | Action
      (** The five node families of `Effect4.Program.Node` (Compile.lean:51-59) that this wire
          carries.  `layer` is Lean's sixth and has no carrier in `Eff_types`. *)

val family_name : family -> string
val family_eq : family -> family -> bool
val families : family list

val family_ctor_names : family -> string list
(** `Eff_types.ctor_names_<t>` for the family: the alphabet the index is table-driven over
    (SB5).  24 / 6 / 2 / 2 / 16. *)

val arity : family -> int
(** The number of constructors of the family — `List.length (family_ctor_names f)`. *)

val path_to_string : int list -> string
(** "." for the root, else "0.1.0"; for messages and the receipt, never an identity. *)

(* ============================================================ the child table *)

val children : family -> int -> (int * family) list
(** [children f c] is the children of constructor [c] of family [f], in `ProgPath` order: the
    k-th element is program child k, and it is `(value argument index, the child's family)`.
    `[]` for a constructor with no addressed children.  Out-of-range constructor indices answer
    `[]`.  This is the whole table (SB5), transcribed from `Node.child`
    (src/Effect4/Program/Compile.lean:65-115); there is no fallback (M3). *)

val val_of_prog : family -> int -> int -> int option
(** [val_of_prog f ctor k] is the value-argument index of program child [k] (SB4). *)

val prog_of_val : family -> int -> int -> int option
(** The other direction: the program child index of value argument [j], or None when that
    argument is not an addressed child (a `term`, a `native_op`, a `fork_options`) (SB4). *)

(* ============================================================ the index *)

type entry = {
  prog_path : int list;  (** child indices in `Node.child` — a `ProgPath` (M5) *)
  val_path : int list;  (** argument indices in the encoded tree — a `ValPath` (M5) *)
  family : family;  (** the family of the node this entry addresses (D1) *)
  ctor : int;  (** its constructor index in that family *)
  off : int;  (** the first byte of its frame, in the whole program's bytes *)
  len : int;  (** the length of its frame *)
  cid : E4_addr.Cid.t;  (** sha256 of the slice (SB3) *)
}

type t

val of_program : string -> t
(** The program's canonical bytes — `Eff_wire.encode_program`'s output.  Raises
    `Invalid_argument` unless the bytes are exactly one well-formed program (SB7, D2). *)

val of_program_opt : string -> t option

val bytes : t -> string
(** The bytes the index was built from: its identity (SB8). *)

val entries : t -> entry list
(** Pre-order, root first (SB6). *)

val count : t -> int
val root : t -> entry
val at_prog_path : t -> int list -> entry option
val at_val_path : t -> int list -> entry option

val entries_at_family : t -> family -> entry list
(** The entries of one family, in the order of [entries]. *)

val slice : string -> entry -> string
(** `String.sub bytes entry.off entry.len` — §1.6's form, over any bytes. *)

val slice_of : t -> entry -> string
(** [slice (bytes t) e]. *)

val cid_of_bytes : string -> E4_addr.Cid.t
(** `E4_sha256.digest`, as an address.  The identity a slice carries (SB3). *)

(* ============================================================ the value side (D3) *)

module Tree : sig
  (** `Effect4.Program.Node` (src/Effect4/Program/Compile.lean:51-115) over `Eff_types`, and
      the family encoders of `Eff_wire`.  This is the second computation SB1 is checked
      against, and `effSig`'s `children`/`rebuild` half (amendment M18). *)

  type node =
    | N_eff of Eff_types.eff
    | N_stmt of Eff_types.stmt
    | N_stmts of Eff_types.stmts
    | N_effs of Eff_types.effs
    | N_action of Eff_types.action_term

  val family_of : node -> family
  val ctor_index : node -> int

  val child : node -> int -> node option
  (** `Node.child` (Compile.lean:65-115), verbatim, over the constructors this wire has. *)

  val at_ : node -> int list -> node option
  (** `Node.at_` (Compile.lean:118-120). *)

  val encode : node -> string
  (** The family's own encoder from `Eff_wire`; for `N_eff` at the root it is
      `Eff_wire.encode_program`. *)

  val of_bytes : string -> node option
  (** `Eff_wire.decode_program_exact`, as an `N_eff`. *)

  val subtree_count : node -> int
  (** The number of nodes in the subtree, counting this one: what `count` must equal. *)
end
