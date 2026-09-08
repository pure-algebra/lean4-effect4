import Lean
import OCaml5.Ml.Syntax
import OCaml5.Lcnf.Naming

/-!
# OCaml5.Lcnf.Externs — `Extract Constant` for the LCNF route

**What it is.** The table that tells the generator *not* to translate a Lean constant, a Lean
type constant or a Lean structure field, and what OCaml text to write in its place. It is the
seam of `docs/research/2026-09-08-engine-a1-state.md` §1: with a field's carrier behind a
functor parameter, every generated site that still treats it as a list is an `ocamlopt` type
error, so **the table is complete iff the generated file compiles** (§1.3).

**Depends on.** `OCaml5.Ml.Syntax` (the OCaml syntax the rows produce), `OCaml5.Lcnf.Naming`
(`stripRedArg` lives here so `Types` and `Translate` share one spelling), `Lean.Name`.

**The file format.** One row per line; `#` starts a comment; blank lines are ignored.

| row | meaning |
| --- | --- |
| `fn <lean> <arity> <head> [tok…]` | translate `<lean>` as an application of `<head>`; never emit its definition and never enqueue its callees. `<arity>` is the number of *relevant* (non-erased) arguments; the call is eta-expanded when under-applied and over-applied when over-applied, exactly as `Translate.applyBuiltin` does for a builtin. |
| `fn? <lean> …` | the same, but the row may go unused (a row kept live for a root set that does not reach it). Every `fn` row that no declaration hits is a **fatal** stale ledger. |
| `type <lean> <con>…` | spell the type constant `<lean>` as the postfix chain `<con>…` applied to its own converted arguments: `type Effect4.Machine.Dispatcher task D.t` is `(…) task D.t`. Its declaration is not emitted. |
| `field <lean-struct>.<field> <con>…` | the field's type must be spelled `τ list`; it becomes the chain applied to `τ` — and to `v` alone when `τ` is a pair `(k * v)`, which is how `List (LayerId × MemoEntry)` becomes `memo_entry L.t`. |
| `elem <lean-type> <con>…` | **every** `List <lean-type>` — in a field, a parameter annotation or a result — becomes the chain applied to it. For a carrier the compiler erases to its element list: `ScopeStore` is a trivial structure, so its mono type *is* `List ScopeEntry` and a `field` row reaches the type declaration but not the annotations. Only for an element type that appears in no other list. |
| `ops <key> <op> <head> [tok…]` | the OCaml form of one *operation* of the carrier whose chain ends in `<key>`: `ops P.t snoc P.snoc program_node_child` makes `x ++ [i]` on a value of that carrier read `P.snoc program_node_child x i`. The recognised `<op>`s are `snoc`, `append`, `to_list`, `get`, `length` and `take` (`Translate.carrierRewrite?`). |
| `carg <lean-decl> <i> <con>…` | the *i*-th OCaml parameter of `<lean-decl>` (count them in the generated signature; erased parameters count) carries the chain's carrier rather than a list. It is what an inter-procedural analysis would infer and this table states: `blockExit`'s `env` is a carrier because its callers pass one. A `carg` row also **drops the declaration's result annotation**, because the carrier can sit at a nested position no chain can spell (`Option (Prod (List Nat) (List Val))`), and OCaml infers it. |

A chain token that begins with `@` is a **literal type argument**: it replaces the argument
list the chain is applied to, so `field Effect4.Program.Point.path @node P.t` is `node P.t`
even though the field's element type is `Nat`. That is the only way to name a type declared
*inside* the functor (`node` is generated), and it is what lets the path carrier hold the
node it addresses (`docs/research/2026-09-08-engine-prof-chain.md` §5.2, gap 1).

A token that begins with `+` **appends** a type argument instead of replacing the list, and
either form may be written `T:i,j,k` — the type constant `T` applied to the arguments at
those positions *of the element type the chain is handed*. `field
Effect4.Machine.RunMachine.fibers +exit_:2,3,4,5,6 F.t` spells
`((ν,σ,β,ε,δ,ι,α,χ,κ,φ) run_fiber, (β,ε,δ,ι,α) exit_) F.t`: a carrier that is a table of
fibers **and** keeps their exits needs both types, and neither of them can be named from
outside the functor (lane G3, `docs/research/2026-09-08-engine-lane-g3-delivery.md`). An index
the element type does not have becomes a type constructor nothing declares, so a Lean change
that reorders those parameters is an `ocamlopt` error and never a silently wrong type.

`[tok…]` after `<head>` is the argument spec, left to right:

* `_` — the next relevant argument, unlabelled;
* `~name` — the next relevant argument, as `~name:`;
* anything else — a literal extra leading argument, a name that must be in scope **at the call
  site** (this is how a hand row reaches a generated helper that is emitted *after* the
  prelude: `fn Effect4.Api.load 3 sh_api_load program_compile` writes
  `sh_api_load program_compile p f c`).

With no `_`/`~name` token the relevant arguments are appended positionally after the literals,
which is the common case.

**Properties.**
* **Total.** `parse` answers `Except String Externs`; a malformed row names its line number and
  no row is silently dropped — *by construction*.
* **`_redArg` blindness.** A row written for `f` also matches `f._redArg`, because
  `reduceArity`'s twin is the constant the mono code actually calls and the two are one
  definition — *by construction* (`fn?`, `stripRedArg`).
* **No implicit arity.** A row states its arity; the emitted call is saturated for any number
  of arguments the call site passes — *by construction* (`ExternFn.apply`).
* **The signatures are bytes, not syntax.** `carrierSignatures` is the verbatim text of the
  module types the functor takes, so the design document and the generated file cannot drift —
  *by construction*.
* **A carrier is visible in the type or it is not there.** A `field`/`type`/`elem` row changes
  a type, so a site that still treats the carrier as a list is an `ocamlopt` error; the
  `ops`/`carg` rows that reach the *inline* sites are checked the same way, because a rewrite
  that fires where it should not — or fails to fire where it should — produces a value of the
  wrong type. The one thing neither says is that a `to_list` was inserted where a `carg` row
  was wanted: that is correct and slow, so `LcnfGen` prints every one of them.
-/

namespace OCaml5.Lcnf

open Lean

/-- `n._redArg` → `n`. `reduceArity` splits `f` into a wrapper and `f._redArg`; the two are one
definition, so one extern row must match both. -/
def stripRedArg : Name → Name
  | .str p "_redArg" => p
  | n => n

/-- One argument of an extern row's application. -/
inductive ExArg where
  /-- A literal extra argument: a name in scope at the call site. -/
  | lit (name : String)
  /-- The next relevant argument of the Lean call, optionally labelled. -/
  | slot (label : Option String)
deriving Inhabited, Repr, BEq

/-- One `fn` row. -/
structure ExternFn where
  /-- The number of relevant (non-erased) arguments the row is written for. -/
  arity : Nat
  /-- The OCaml expression the call is an application of. -/
  head : String
  /-- The argument spec; empty means "append every relevant argument positionally". -/
  spec : List ExArg := []
  /-- Whether an unused row is tolerated (`fn?`). -/
  optional : Bool := false
deriving Inhabited

/-- The whole table. -/
structure Externs where
  /-- Lean constant → its OCaml form. -/
  fns : Std.HashMap Name ExternFn := {}
  /-- Lean type constant → the postfix chain that spells it. -/
  tys : Std.HashMap Name (List String) := {}
  /-- `<struct>.<field>` → the postfix chain that spells the field's carrier. -/
  fields : Std.HashMap Name (List String) := {}
  /-- Lean type constant `T` → the chain that spells **every** `List T`. For a carrier the
  compiler erases to its element list (`ScopeStore` is a trivial structure, so its mono type is
  `List ScopeEntry` and a `field` row cannot reach the annotations). -/
  elems : Std.HashMap Name (List String) := {}
  /-- `<carrier key>#<op>` → its OCaml form. The key is a chain's last token (`P.t`, `E.t`). -/
  ops : Std.HashMap String ExternFn := {}
  /-- `<Struct>.<field>` → the carrier key its chain ends in: which operations a value read
  out of that field understands. -/
  fieldCarrier : Std.HashMap Name String := {}
  /-- Lean declaration → the OCaml parameter positions that carry a carrier, with the chain
  that spells each. The declaration's result annotation is dropped. -/
  cargs : Std.HashMap Name (List (Nat × List String)) := {}
  /-- The rows in file order, for the report. -/
  order : Array String := #[]

instance : Inhabited Externs := ⟨{}⟩

/-- The row for a constant, `_redArg`-blind. -/
def Externs.fn? (ex : Externs) (n : Name) : Option ExternFn :=
  match ex.fns[n]? with
  | some f => some f
  | none => ex.fns[stripRedArg n]?

/-- Whether a constant has a row. -/
def Externs.hasFn (ex : Externs) (n : Name) : Bool := (ex.fn? n).isSome

/-- One operation of a carrier, by the carrier's key. -/
def Externs.op? (ex : Externs) (carrier op : String) : Option ExternFn :=
  ex.ops[s!"{carrier}#{op}"]?

/-- The carrier a field's value understands, by `<Struct>.<field>`. -/
def Externs.fieldCarrier? (ex : Externs) (owner : Name) (field : String) : Option String :=
  ex.fieldCarrier[owner ++ Name.mkSimple field]?

/-- The carrier parameters of a declaration, `_redArg`-blind. -/
def Externs.carg? (ex : Externs) (n : Name) : Option (List (Nat × List String)) :=
  match ex.cargs[n]? with
  | some r => some r
  | none => ex.cargs[stripRedArg n]?

/-- The chain that spells the *i*-th OCaml parameter of `n`, if the table gives it one. -/
def Externs.cargChain? (ex : Externs) (n : Name) (i : Nat) : Option (List String) :=
  match ex.carg? n with
  | none => none
  | some rows => (rows.find? (·.1 == i)).map (·.2)

/-! ## Applying a row -/

/-- The `elem` chain for `<con> <args>` when `con` is `List`/`Array` and its element is an
applied type constant with a row: `List ScopeEntry` → `["M.t"]`. -/
def Externs.elemChain? (ex : Externs) (n : Name) (args : List Lean.Expr) : Option (List String) :=
  if n == ``List || n == ``Array then
    match args with
    | [a] => match a.getAppFn with
      | .const en _ => ex.elems[en]?
      | _ => none
    | _ => none
  else none

/-- The carrier key of a chain: its last constructor token. Two carriers are told apart by
it, and `ops` rows are filed under it. -/
def chainKey (chain : List String) : String :=
  ((chain.filter (fun c => !(c.startsWith "@" || c.startsWith "+"))).getLast?).getD ""

/-- Whether a chain token is a literal type argument rather than a constructor to apply. -/
def isChainLit (c : String) : Bool := c.startsWith "@" || c.startsWith "+"

/-- The `i`-th type argument of the *element type* a chain is handed. Out of range is a type
constructor nothing declares, so a stale index is an `ocamlopt` error, never a wrong type. -/
private def chainElemArg (args : List Ml.Ty) (i : Nat) : Ml.Ty :=
  let bad := Ml.Ty.con "lcnf_chain_index_out_of_range" []
  match args with
  | [.con _ eargs] => eargs[i]?.getD bad
  | _ => bad

/-- A literal chain token, without its `@`/`+`: `T` is the type constant `T`; `T:i,j,k` is `T`
applied to the element type's own arguments at those positions. -/
private def chainLit (args : List Ml.Ty) (tok : String) : Ml.Ty :=
  match (String.ofList tok.toList.tail).splitOn ":" with
  | [name] => .con name []
  | [name, idx] => .con name (((idx.splitOn ",").filterMap String.toNat?).map (chainElemArg args))
  | _ => .con "lcnf_chain_bad_token" []

/-- A postfix chain of type constructors applied to already-converted arguments:
`["task", "D.t"]` on `[τ₁, …, τ₈]` is `(τ₁, …, τ₈) task D.t`. A `@T` token replaces the
argument list with the literal type `T`, which is how a carrier is applied to a type the
generator declares *inside* the functor (`["@node", "P.t"]` is `node P.t` whatever it is
handed); a `+T` token appends one instead of replacing, and either may name the element type's
own arguments (`+exit_:2,3,4,5,6`), which is how one carrier takes two generated types. -/
def applyChain (chain : List String) (args : List Ml.Ty) : Ml.Ty :=
  let lits := chain.filterMap fun c => if c.startsWith "@" then some (chainLit args c) else none
  let more := chain.filterMap fun c => if c.startsWith "+" then some (chainLit args c) else none
  let cons := chain.filter fun c => !isChainLit c
  let args := (if lits.isEmpty then args else lits) ++ more
  match cons.foldl (fun as c => [Ml.Ty.con c as]) args with
  | [t] => t
  | ts => ts.headD Ml.Ty.unit

private def labelOf : Option String → Ml.ArgLabel
  | none => .nolabel
  | some n => .lbl n

private def isNolabel : Ml.ArgLabel → Bool
  | .nolabel => true
  | _ => false

private def isSlot : ExArg → Bool
  | .slot _ => true
  | _ => false

private def buildArgs : List ExArg → List Ml.Expr → List (Ml.ArgLabel × Ml.Expr)
  | [], as => as.map fun a => (Ml.ArgLabel.nolabel, a)
  | .lit n :: sp, as => (Ml.ArgLabel.nolabel, Ml.Expr.var n) :: buildArgs sp as
  | .slot l :: sp, a :: as => (labelOf l, a) :: buildArgs sp as
  | .slot _ :: sp, [] => buildArgs sp []

/-- The row applied to exactly its arity's worth of relevant arguments. -/
def ExternFn.build (f : ExternFn) (args : List Ml.Expr) : Ml.Expr :=
  let spec :=
    if (f.spec.filter isSlot).isEmpty then f.spec ++ List.replicate args.length (ExArg.slot none)
    else f.spec
  let pairs := buildArgs spec args
  if pairs.isEmpty then .var f.head
  else if pairs.all (fun p => isNolabel p.1) then .app (.var f.head) (pairs.map (·.2))
  else .appL (.var f.head) pairs

/-- The carrier of the *i*-th OCaml parameter of `n`, if the table says it has one. -/
def Externs.cargAt? (ex : Externs) (n : Name) (i : Nat) : Option String :=
  (ex.cargChain? n i).map chainKey

/-- A carrier chain applied to a field or parameter whose Lean type is `τ list`: the chain
takes the *element*, as `field` rows do, so `List Val` becomes `val_ E.t`. A leading `@T`
token replaces the element anyway. -/
def carrierAnnot (chain : List String) (t : Ml.Ty) : Ml.Ty :=
  match t with
  | .con "list" [elem] => applyChain chain [elem]
  | _ => applyChain chain [t]

/-- The row applied to the arguments the call site passes: saturated, eta-expanded when the
call is under-applied and applied to the rest when it is over-applied — the same three cases
`Translate.applyBuiltin` handles. -/
def ExternFn.apply (f : ExternFn) (args : List Ml.Expr) : Ml.Expr :=
  if args.length == f.arity then f.build args
  else if args.length < f.arity then
    let extra := (List.range (f.arity - args.length)).map fun i => s!"_ex{i + 1}"
    .fn extra (f.build (args ++ extra.map Ml.Expr.var))
  else .app (f.build (args.take f.arity)) (args.drop f.arity)

/-! ## Parsing -/

private def parseTok (s : String) : ExArg :=
  if s == "_" then .slot none
  else if s.startsWith "~" then .slot (some (String.ofList s.toList.tail))
  else .lit s

/-- One line's tokens: everything before `#`, split on spaces, tabs and a trailing `\r` (the
file is edited on Windows as often as not). -/
private partial def tokensOf (cs : List Char) (cur : List Char) (acc : List String) : List String :=
  let flush := if cur.isEmpty then acc else String.ofList cur.reverse :: acc
  match cs with
  | [] => flush.reverse
  | c :: rest =>
    if c == ' ' || c == '\t' || c == '\r' then tokensOf rest [] flush
    else tokensOf rest (c :: cur) acc

private def words (s : String) : List String :=
  tokensOf (s.toList.takeWhile (· != '#')) [] []

/-- Read an `--externs` file. One row per line; `#` starts a comment. -/
def Externs.parse (text : String) : Except String Externs := do
  let mut ex : Externs := {}
  let mut lineNo := 0
  for rawLine in text.splitOn "\n" do
    lineNo := lineNo + 1
    let ws := words rawLine
    if ws.isEmpty then continue
    let row := " ".intercalate ws
    match ws with
    | "type" :: name :: chain =>
      if chain.isEmpty then throw s!"externs:{lineNo}: `type` row with no target chain"
      ex := { ex with tys := ex.tys.insert name.toName chain, order := ex.order.push row }
    | "field" :: name :: chain =>
      if chain.isEmpty then throw s!"externs:{lineNo}: `field` row with no target chain"
      ex := { ex with fields := ex.fields.insert name.toName chain,
                      fieldCarrier := ex.fieldCarrier.insert name.toName (chainKey chain),
                      order := ex.order.push row }
    | "ops" :: key :: op :: head :: toks =>
      ex := { ex with
        ops := ex.ops.insert s!"{key}#{op}"
                 { arity := 0, head := head, spec := toks.map parseTok },
        order := ex.order.push row }
    | "carg" :: name :: idx :: chain =>
      if chain.isEmpty then throw s!"externs:{lineNo}: `carg` row with no target chain"
      let some i := idx.toNat? | throw s!"externs:{lineNo}: `{idx}` is not a parameter index"
      let prev := ex.cargs.getD name.toName []
      ex := { ex with cargs := ex.cargs.insert name.toName (prev ++ [(i, chain)]),
                      order := ex.order.push row }
    | "elem" :: name :: chain =>
      if chain.isEmpty then throw s!"externs:{lineNo}: `elem` row with no target chain"
      ex := { ex with elems := ex.elems.insert name.toName chain, order := ex.order.push row }
    | kind :: name :: arity :: head :: toks =>
      if kind != "fn" && kind != "fn?" then
        throw s!"externs:{lineNo}: unknown row kind `{kind}`"
      let some k := arity.toNat? | throw s!"externs:{lineNo}: `{arity}` is not an arity"
      let fnRow : ExternFn :=
        { arity := k, head := head, spec := toks.map parseTok, optional := kind == "fn?" }
      ex := { ex with fns := ex.fns.insert name.toName fnRow, order := ex.order.push row }
    | _ => throw s!"externs:{lineNo}: cannot read row `{row}`"
  return ex

/-! ## The carrier signatures

The module types the generated functor takes, as **bytes**. `docs/research/
2026-09-08-engine-a1-state.md` §1.5 prints `TABLE`, `TRACE` and `LAYERS`; `DISPATCHER` is
`docs/research/2026-09-08-engine-a3-queue-query.md` §1.1.1's `e4_buckets.mli`, so
`module D = E4_buckets` is a legal instantiation with no adapter. A1's `FIFO` is dropped: the
dispatcher is A3's whole-dispatcher carrier, not a table of buckets holding queues.
-/

/-- The verbatim text of the seven module types, emitted above the functor. -/
def carrierSignatures : String :=
"(* An int-keyed persistent table.  `set` REPLACES and never inserts (Lean's List.set and
   List.map-by-key are no-ops on an absent key); `add` inserts.  `bindings` is ascending. *)
module type TABLE = sig
  type 'a t
  val empty     : 'a t
  val find_opt  : int -> 'a t -> 'a option
  val set       : int -> 'a -> 'a t -> 'a t
  val add       : int -> 'a -> 'a t -> 'a t
  val remove    : int -> 'a t -> 'a t
  val mem       : int -> 'a t -> bool
  val cardinal  : 'a t -> int
  val map       : ('a -> 'a) -> 'a t -> 'a t
  val filter_map : (int -> 'a -> 'b option) -> 'a t -> 'b list
  val for_all   : (int -> 'a -> bool) -> 'a t -> bool
  val fold      : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val bindings  : 'a t -> (int * 'a) list
  val of_list   : (int * 'a) list -> 'a t
  val to_list   : 'a t -> 'a list
end

(* The fiber table: an int-keyed persistent table that also MAINTAINS the completed view --
   the (id, exit) pairs of the fibers whose exit is set, ascending by id, kept as the table is
   written, so `RunMachine.completedExits` (Fibers.lean:1543) is a field read and not the
   Theta(N) scan it was.  `('a, 'x) t` is a table of fibers `'a` whose exit is `'x`; the fiber
   record is declared INSIDE this functor, so every write takes the projection `~exit_of`
   rather than closing over it.  `set` REPLACES and never inserts (Lean's replace-by-key map
   is a no-op on an absent id); `add` inserts; `bindings` and `completed` are ascending.  This
   is ocaml/engine/e4_fibers_view.mli's own signature, so `module F = E4_fibers_view` needs no
   adapter.  Nothing removes a fiber -- the ordering argument that licenses the substitution
   is that no fiber is ever removed (gen-check.sh C1). *)
module type FIBERS = sig
  type ('a, 'x) t
  val empty     : ('a, 'x) t
  val find_opt  : int -> ('a, 'x) t -> 'a option
  val set       : exit_of:('a -> 'x option) -> int -> 'a -> ('a, 'x) t -> ('a, 'x) t
  val add       : exit_of:('a -> 'x option) -> int -> 'a -> ('a, 'x) t -> ('a, 'x) t
  val map       : exit_of:('a -> 'x option) -> ('a -> 'a) -> ('a, 'x) t -> ('a, 'x) t
  val for_all   : (int -> 'a -> bool) -> ('a, 'x) t -> bool
  val completed : ('a, 'x) t -> (int * 'x) list
  val cardinal  : ('a, 'x) t -> int
  val bindings  : ('a, 'x) t -> (int * 'a) list
  val to_list   : ('a, 'x) t -> 'a list
  val of_list   : exit_of:('a -> 'x option) -> (int * 'a) list -> ('a, 'x) t
end

(* An append-and-read-once event log.  `emit []` is O(1) and physically equal. *)
module type TRACE = sig
  type 'e t
  val empty   : 'e t
  val emit    : 'e list -> 'e t -> 'e t
  val to_list : 'e t -> 'e list
  val length  : 'e t -> int
end

(* A table keyed by a layer path (`LayerId = List Nat`).  `insert` KEEPS an existing
   binding: Lean appends and `find?` answers the first (Stores.lean:867, 880). *)
module type LAYERS = sig
  type 'a t
  val empty     : 'a t
  val find_opt  : int list -> 'a t -> 'a option
  val insert    : int list -> 'a -> 'a t -> 'a t
  val update    : int list -> ('a -> 'a) -> 'a t -> 'a t
  val delete    : int list -> 'a t -> 'a t
  val bindings  : 'a t -> (int list * 'a) list
end

(* The per-fiber dispatcher: priority -> FIFO, persistent.  This is
   ocaml/engine/queue/e4_buckets.mli verbatim (engine-a3 SS1.1.1), so `module D = E4_buckets`
   needs no adapter. *)
module type DISPATCHER = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val armed : 'a t -> bool
  val disarm : 'a t -> 'a t
  val enqueue : 'a t -> priority:int -> 'a -> 'a t
  val drain : 'a t -> 'a list * 'a t
  val length : 'a t -> int
  val priorities : 'a t -> int list
  val to_list : 'a t -> (int * 'a list) list
  val of_list : armed:bool -> (int * 'a list) list -> 'a t
end

(* A point's position in the program: a snoc-shared spine that CARRIES the node it addresses,
   so `Point.child` is O(1) and `resolve` never walks
   (docs/research/2026-09-08-engine-prof-chain.md SS5.1).  This is
   ocaml/engine/e4_ppath.mli's own signature.  `'n` is the generated `node` type, which is
   declared inside this functor, so `Node.child` is passed in rather than closed over. *)
module type PPATH = sig
  type 'n t
  val make : 'n -> 'n t
  val root : 'n t -> 'n
  val snoc : ('n -> int -> 'n option) -> 'n t -> int -> 'n t
  val append : ('n -> int -> 'n option) -> 'n t -> int list -> 'n t
  val node : ('n -> int -> 'n option) -> 'n t -> 'n option
  val walk : ('n -> int -> 'n option) -> 'n -> int list -> 'n option
  val to_list : 'n t -> int list
  val length : 'n t -> int
end

(* A point's environment: a snoc-shared spine with a cached length.  `get` is Lean's
   `env[i]?` (indexed from the front) and `take` is Lean's `List.take` (clamped).  This is
   ocaml/engine/e4_env.mli's own signature. *)
module type PENV = sig
  type 'a t
  val empty : 'a t
  val snoc : 'a t -> 'a -> 'a t
  val append : 'a t -> 'a list -> 'a t
  val get : 'a t -> int -> 'a option
  val length : 'a t -> int
  val take : 'a t -> int -> 'a t
  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
end"

/-- The functor's parameters, in order. -/
def carrierParams : List (String × Ml.ModTy) :=
  [("M", .path "TABLE"), ("T", .path "TRACE"), ("L", .path "LAYERS"), ("D", .path "DISPATCHER"),
   ("P", .path "PPATH"), ("E", .path "PENV"), ("F", .path "FIBERS")]

end OCaml5.Lcnf
