import Effect4.Codegen.Print
import Effect4.Codegen.EraseTypes
import Effect4.Program.Typing.Call

/-!
# Codegen.PrintTyped — the print with a call's type arguments at a join

The typed print's slice P2a (`docs/research/2026-10-07-typed-print-design.md`, the addendum).
tsgo forms no join of two inference candidates (`docs/research/2026-10-06-print-probe.md`). So
where the checker binds a row's parameter to a join, the printed call must carry the row's
bindings as its type arguments.

**The print.** `printTypedAt` is the table-driven print (`Templates.printT`) with one more
input, the node's address. A child's address is its parent's and its index among the node
arguments (`Node.child`). Every row prints as in `printAlg`, except a call: at an address where
the annotation answers type arguments, the call carries them on its head (`withHeadTypes`).

**The annotation.** `typeArgsAt` answers a call's type arguments where a binding is a join: the
guarded match refuses there (`rowBindings`) and the match by bounds with no guard answers
(`rowBindingsB`). They are the bindings in the order of the row's variables, `.var 0` first.

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

end Effect4.Codegen.Templates

namespace Effect4.Program

variable {Op : Type}

/-- **The bindings of a row's use by the match by bounds with no guard**: `rowBindings` with
`Bounds.matchB` at the request and at the binder term. It answers where `rowBindings` answers,
and also where a parameter's lower bounds have no greatest member: a join. -/
def rowBindingsB (row : Row) (request : Ty) (use : Option TermUse := none) : Option Ty.Subst :=
  (Bounds.matchB [] row.request.normalize request.normalize).bind fun σ =>
    match use with
    | none => some σ
    | some u =>
      (u.typeAt (TermUse.instParam u.param σ)).bind fun r =>
        Bounds.matchB σ u.result.normalize r

/-- The bindings in the order of the row's variables, `.var 0` first, up to the greatest bound
variable; `none` where a variable below it is not bound. -/
def Ty.Subst.ordered (σ : Ty.Subst) : Option (List Ty) :=
  (List.range (σ.foldr (fun b k => max k (b.1 + 1)) 0)).mapM fun i => List.lookup i σ

/-- **The type arguments a call prints at its address**: where the address holds a call whose
guarded match refuses and whose match by bounds answers, its bindings in the order of the row's
variables. `none` elsewhere. -/
def typeArgsAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (List Ty) :=
  (focusAt s env0 p path).bind fun focus =>
    match focus.program with
    | .perform op request =>
      (termTy s focus.env request).bind fun requestTy =>
        match rowBindings (s.rowOf op) requestTy (s.termUse focus.env op) with
        | some _ => none
        | none => (rowBindingsB (s.rowOf op) requestTy (s.termUse focus.env op)).bind
            Ty.Subst.ordered
    | _ => none

/-- **The typed print of a program**: each call at a join carries its type arguments. -/
def printTyped (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printTypedAt s (typeArgsAt s env0 p) env0.length p

end Effect4.Program
