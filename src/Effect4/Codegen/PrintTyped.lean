import Effect4.Codegen.Print
import Effect4.Codegen.PrintEliminators
import Effect4.Codegen.EraseTypes
import Effect4.Program.Typing.Call

/-!
# Codegen.PrintTyped — the print with a call's type arguments at a join

The typed print's slice P2a (`docs/research/2026-10-07-typed-print-design.md`, the addendum).
The retained W1 and W2 controls need explicit bindings at joins
(`docs/research/2026-10-06-print-probe.md`). The printer supplies these checked bindings
as call type arguments.

**The print.** `printTypedAt` is the table-driven print (`Templates.printT`) with one more
input, the node's address. A child's address is its parent's and its index among the node
arguments (`Node.child`). Every row prints as in `printAlg`, except a call: at an address where
the annotation answers type arguments, the call carries them on its head (`withHeadTypes`).

**The annotation.** `typeArgsAt` reads the call's checked bindings where inference needs a join,
off the address table that `annotate` builds once per program (`focusAtTable`).
`PrintedJoin` detects that printing condition independently of admission.
The bindings follow the row's template variables, `.var 0` first.

**The connector.** On the existing readable fragment with lawful spelling, every successful
raw typed print erases to the ordinary print (`eraseJoinArgs_printTypedAt`,
`Laws/Codegen/PrintTyped.lean`). The named erasure retains operation-carried and row-declared
arguments. The existing reader after erasure carries read-back and reconstruction at the
erased input (`readTyped_printTypedAt`, `readTyped_exact`). Target typing and execution remain
separate evidence.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Templates

open Effect4.Program

variable {Op : Type}

/-- The carrier of the typed print: the plain carrier at each address. -/
abbrev TCarrier (fam : EffFam) : Type := List Nat → Carrier fam

/-- **A node's arguments, each child read at its address**: the node's address and the child's
index among the node arguments, counted from `j`. The other arguments are as they are. -/
def atAddress (path : List Nat) : List (ArgF Op TCarrier) → Nat → List (ArgF Op Carrier)
  | [], _ => []
  | .child fam c :: as, j => .child fam (c (path ++ [j])) :: atAddress path as (j + 1)
  | .term v :: as, j => .term v :: atAddress path as j
  | .cause v :: as, j => .cause v :: atAddress path as j
  | .op v :: as, j => .op v :: atAddress path as j
  | .nat v :: as, j => .nat v :: atAddress path as j
  | .mode v :: as, j => .mode v :: atAddress path as j
  | .bool v :: as, j => .bool v :: atAddress path as j
  | .key v :: as, j => .key v :: atAddress path as j
  | .decision v :: as, j => .decision v :: atAddress path as j
  | .optTy v :: as, j => .optTy v :: atAddress path as j
  | .forkOptions v :: as, j => .forkOptions v :: atAddress path as j
  | .optTerm v :: as, j => .optTerm v :: atAddress path as j
  | .lit v :: as, j => .lit v :: atAddress path as j
  | .path v :: as, j => .path v :: atAddress path as j
  | .decls v :: as, j => .decls v :: atAddress path as j
  | .keys v :: as, j => .keys v :: atAddress path as j

/-- **The row call with type arguments on its head**: the call that `printPerform` prints, with
the given types on the call's head, each as the type printer prints it. With no type argument
it is `printPerform`'s call. Insertion refuses where the operation or its row owns arguments.
A type with no printed form refuses the row by its spelling. -/
def printPerformAt (sig : Signature Op) (n : Nat) (op : Op) (request : Term) :
    Option (List Ty) → Except PrintRefusal TypeScript.Expr
  | none | some [] => printPerform sig n op request
  | some (ty :: tys) =>
    if (sig.typeArgsOf op).isEmpty && (sig.rowOf op).typeArgs.isEmpty then
      let call := match Effect4.Codegen.Classes.writeTys (ty :: tys) with
        | some targets =>
          (printRow n (sig.rowOf op) request).bind (withHeadTypes (sig.rowOf op).spelling targets)
        | none => .error (.typeSpelling (sig.rowOf op).spelling)
      match sig.termOf op with
      | none => call
      | some b =>
        call.bind (withFunction (sig.rowOf op).spelling
          (Effect4.Codegen.Binders.write n [0] (printTerm (n + 1) b.term)))
    else .error (.typeSpelling (sig.rowOf op).spelling)

/-- **The typed print's algebra**: the table's layer function with each child at its address,
and at a call the type arguments that the annotation answers at the call's address. -/
def typedAlg (sig : Signature Op) (ann : List Nat → Option (List Ty)) : EffAlgebra Op TCarrier :=
  { EffAlgebra.ofLayer (fun fam ctor args path => tableLayer sig fam ctor (atAddress path args 0))
    with eff_perform := fun op request path n => printPerformAt sig n op request (ann path) }

/-- The typed print of a program at an annotation, at environment length `n`. -/
def printTypedAt (sig : Signature Op) (ann : List Nat → Option (List Ty)) (n : Nat)
    (e : Eff Op) : Except PrintRefusal TypeScript.Expr :=
  cata_eff (typedAlg sig ann) e [] n

/-- The full typed printer uses the same address fold and the checked node/slot environments.
The earlier row-only `typedAlg` remains available for its existing connector and controls. -/
def typedSitesAlg (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (ctx : List Nat → Option (Effect4.Codegen.PrintEliminators.Context Op)) :
    EffAlgebra Op TCarrier :=
  EffAlgebra.ofLayer (fun fam ctor args path =>
    match ctx path with
    | some context => Effect4.Codegen.PrintEliminators.layer sig context (ann path)
        fam ctor (atAddress path args 0)
    | none => Effect4.Codegen.PrintEliminators.missing fam)

/-- All approved typed sites, using actual checked data at each address. -/
def printTypedSitesAt (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (ctx : List Nat → Option (Effect4.Codegen.PrintEliminators.Context Op))
    (n : Nat) (e : Eff Op) : Except PrintRefusal TypeScript.Expr :=
  cata_eff (typedSitesAlg sig ann ctx) e [] n


end Effect4.Codegen.Templates

namespace Effect4.Program

variable {Op : Type}

/-- The bindings in the order of the row's variables, `.var 0` first, up to the greatest bound
variable; `none` where a variable below it is not bound. -/
def Ty.Subst.ordered (σ : Ty.Subst) : Option (List Ty) :=
  (List.range (σ.foldr (fun b k => max k (b.1 + 1)) 0)).mapM fun i => List.lookup i σ

namespace PrintedJoin

/-- Whether printing needs a type argument for these bounds. Only parameters not fixed by
`seed` matter. No candidate or one candidate requires no annotation. The consumer is
`row`, which annotates newly admitted calls without restricting the checker. -/
def needed (seed : Ty.Subst) (template request : Ty) : Bool :=
  let cs := Bounds.cands .co template request
  cs.any fun c =>
    !(seed.lookup c.1).isSome &&
      match (Bounds.lowers cs c.1).map Ty.normalize with
      | [] | [_] => false
      | candidates => !(candidates.any fun candidate => candidates.all fun lower => Ty.sub lower candidate)

/-- Whether either match of a call needs printed bindings. The request's match supplies the
binder's fixed parameters. Both matches remain the checker's existing `Bounds.matchB`. -/
def row (row : Row) (request : Ty) (use : Option TermUse := none) : Bool :=
  needed [] row.request.normalize request.normalize ||
    ((Bounds.matchB [] row.request.normalize request.normalize).bind fun seed =>
      use.bind fun binder =>
        (binder.typeAt (TermUse.instParam binder.param seed)).map fun result =>
          needed seed binder.result.normalize result).getD false

/-- Whether a focused call needs explicit type arguments. Addresses outside a checked call
answer false. The consumer is `NoJoin`; this is a printer decision, never admission. -/
def at_ (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) : Bool :=
  ((focusAt s env0 p path).bind fun focus =>
    match focus.program with
    | .perform op request =>
      (termTy s focus.env request).map fun requestTy =>
        row (s.rowOf op) requestTy (s.termUse focus.env op)
    | _ => none).getD false

end PrintedJoin

/-- No call needs a join annotation at any checked address. This is the domain of the
unchanged-print connector. It makes no claim about target compiler inference. -/
def NoJoin (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : Prop :=
  (∀ path, PrintedJoin.at_ s env0 p path = false) ∧
    Effect4.Codegen.PrintEliminators.NoSiteTypes s env0 p

/-- **The type arguments a join needs at a focused call**: where the request's match needs a join
annotation (`PrintedJoin.row`), the row's bindings at the request's type (`rowBindings`, the
bindings of the call's instance, `callAt`), in the order of the row's variables. -/
def Focus.joinArgs (s : Signature Op) (focus : Focus Op) : Option (List Ty) :=
  match focus.program with
  | .perform op request =>
    (termTy s focus.env request).bind fun requestTy =>
      if PrintedJoin.row (s.rowOf op) requestTy (s.termUse focus.env op) then
        (rowBindings (s.rowOf op) requestTy (s.termUse focus.env op)).bind Ty.Subst.ordered
      else none
  | _ => none

/-- **The focus at an address, read off the address table** (`annotate`): the node there, the
environment its entry holds and the checker's answer there. No address is focused afresh. It
answers what `focusAt` answers (`focusAtTable_annotate`, `Laws/Codegen/PrintTyped.lean`). -/
def focusAtTable (entries : List Table.Entry) (p : Eff Op) (path : List Nat) :
    Option (Focus Op) :=
  (entries.find? fun entry => decide (entry.path = path)).bind fun entry =>
    match (Node.eff p).at_ path, entry.env, entry.result with
    | some (.eff q), some (.env env), some (.ok t) => some ⟨q, env, t⟩
    | _, _, _ => none

/-- **The type arguments at each address**, read off the address table: the row's checked
bindings, in the order of the row's variables, only at a call that needs them. The table is
built once per program, so no call focuses the program again. -/
def typeArgsAt (s : Signature Op) (entries : List Table.Entry) (p : Eff Op) (path : List Nat) :
    Option (List Ty) :=
  (focusAtTable entries p path).bind (Focus.joinArgs s)

/-- The typed print adds the approved site types when a checked site needs them.
The shared annotation table supplies every site context and child result, and the type
arguments of every call (`typeArgsAt`): the program is checked once.
Without site annotations, the row-only printer keeps its existing raw behavior. -/
def printTyped (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    Except PrintRefusal TypeScript.Expr :=
  let entries := annotate s env0 p
  if Effect4.Codegen.PrintEliminators.needsSitesAt s entries p then
    Effect4.Codegen.Templates.printTypedSitesAt s (typeArgsAt s entries p)
      (Effect4.Codegen.PrintEliminators.contextAtTable entries p) env0.length p
  else
    Effect4.Codegen.Templates.printTypedAt s (typeArgsAt s entries p) env0.length p

/-! ## The module that ships: its pieces printed typed, and read back after the erasure -/

/-- **The pieces of the module that ships**: a module's main program and its bodies, each at its
signature and its checked environment, by the typed print, which writes a call's type arguments
where a join needs them (decisions row 373 (11)); where the typed print refuses a piece, by the
table's fold, as every module printed before the typed print shipped. The typed print refuses a
term slot that it cannot annotate (`typed:term slot depth`), which the fold prints. The module
that ships prints its pieces so (`printModuleWith shippedPieces`). -/
def shippedPieces : PiecePrint Op := fun s env e =>
  match printTyped s env e with
  | .ok x => .ok x
  | .error _ => print s env.length e

/-- **The typed module reader**: each program piece read after the named erasure of its inserted
type arguments (`Codegen.readTyped`). It reads the module that ships (`ModuleEmission.readModule`,
`Laws/Api/ModuleReadable.lean`). -/
abbrev readModuleTyped (sig : Signature Op) (spell : String → List RowArg → Option Op)
    (call : Nat → Op) (param : Nat → Op) (rows : List Row) (decls : List TypeScript.Decl) :
    Except ReadRefusal (Eff Op) :=
  readModuleWith Effect4.Codegen.readTyped sig spell call param rows decls

end Effect4.Program
