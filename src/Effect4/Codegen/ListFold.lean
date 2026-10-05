import Effect4.Codegen.Template
import Effect4.Codegen.Types
import Effect4.Program.Fold

/-!
# The list fold's printed form, and the function of binders that it holds

A list fold (decisions row 228) prints as a call of one prelude function,
`fold(list, init, (aN, aM) => body)`. The two parameters are the binders at the fold's level `n`
and at `n + 1`, so the image needs the environment's length. A stated accumulator type prints as
the call's type argument. It is printed and not read, as a loop's cursor annotation is: no reader
of types exists (B19).

`Binders` is the part a term that binds shares: the function `(a{n + b}, …) => body` over the
binder slots `bs` above level `n`, with unannotated parameters, and its exact reader. The fold
takes it at the slots `[0, 1]`. An operation's binder term (the state plan's T5) takes it at
`[0]`.

`Term.unannotated` is the part of the reader's domain that the fold adds: no fold of the term
states its accumulator's type.

The reader's size facts serve `readTerm`; the remaining laws live in
`Laws/Codegen/ListFold.lean`. This module states no target typing and no execution claim.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Binders
open TypeScript

/-- `(a{n + b}, …) => body`: a function of the binders at the slots `bs` above level `n`. Its
parameters carry no annotation and it declares no result type. -/
def write (n : Nat) (bs : List Nat) (body : Expr) : Expr :=
  .lambda (Template.params n bs) body

/-- The body of exactly that function: the parameters are the binders due at these slots, none
is annotated, and no result type is declared. -/
def read (n : Nat) (bs : List Nat) : Expr → Option Expr
  | .lambda ps body none => if ps = Template.params n bs then some body else none
  | _ => none

/-- Exact-codecs termination helper for `readTerm`: the body is inside the function. -/
theorem read_size (n : Nat) (bs : List Nat) (e body : Expr) (h : read n bs e = some body) :
    sizeOf body < sizeOf e := by
  unfold read at h
  split at h
  · split at h
    · cases h
      simp only [Expr.lambda.sizeOf_spec]
      omega
    · exact nomatch h
  · exact nomatch h

end Effect4.Codegen.Binders

namespace Effect4.Codegen.ListFold
open Effect4.Program TypeScript

/-- The fold's helper binding stays separate from program heads and from row and export names.
An atom application named `fold` still prints and reads as one: its third argument is a term,
and a term prints to no function. -/
def helperNames : List String := ["fold"]

/-- The type argument of a stated accumulator type: its target projection, and `unknown` where
it has none. The raw printer keeps a total image, as a record's raw form does; a checked entry
refuses such a program by name (`annotationRefusal`, `Codegen/Print.lean`). -/
def typeArg (ty : Ty) : TypeRef :=
  (Types.ofTy ty).getD (.name ["unknown"] [])

/-- `fold(list, init, (aN, aM) => body)` at level `n`, with a stated accumulator type as the
call's type argument: `fold<T>(…)`. -/
def write (n : Nat) (acc : Option TypeRef) (list init body : Expr) : Expr :=
  let head : Expr := match acc with
    | none => .ident "fold"
    | some target => .generic (.ident "fold") [target]
  .call head [list, init, Binders.write n [0, 1] body]

/-- The parts of the fold's image without a type argument, at level `n`: the list, the initial
value and the body under the two binders. A call of `fold` on any other argument list is no
fold. -/
def read (n : Nat) : Expr → Option (Expr × Expr × Expr)
  | .call (.ident head) [list, init, step] =>
    if head = "fold" then (Binders.read n [0, 1] step).map fun body => (list, init, body)
    else none
  | _ => none

/-- Exact-codecs termination helper for `readTerm`, serving `collection-term-print-read`:
successful structural reading makes each of the three children smaller. -/
theorem read_size (n : Nat) (e list init body : Expr) (h : read n e = some (list, init, body)) :
    sizeOf list < sizeOf e ∧ sizeOf init < sizeOf e ∧ sizeOf body < sizeOf e := by
  unfold read at h
  split at h
  · next head list' init' step =>
    split at h
    · obtain ⟨body', hbody, h⟩ := Option.map_eq_some_iff.mp h
      cases h
      have hs := Binders.read_size n [0, 1] step body hbody
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
      -- one linear goal at a time: a conjunction handed to `omega` whole reaches
      -- `Classical.choice`, and this law is a termination helper of the reader
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · exact nomatch h
  · exact nomatch h

end Effect4.Codegen.ListFold

namespace Effect4.Program

/-- One node states no accumulator type: every node but a list fold with a stated type. -/
def unannotatedNode : Term → Bool
  | .fold (some _) _ _ _ => false
  | _ => true

/-- No list fold of the term states its accumulator's type. A stated type is printed and not
read (B19; decisions row 228), so a term that states one is outside the image the reader
recovers. The generated term fold, so a node's verdict is its own check and its children's. -/
def Term.unannotated (t : Term) : Bool :=
  foldMap_term true (· && ·) t (f_term := unannotatedNode)

/-- The same of every term of an argument list. -/
def Terms.unannotated (ts : Terms) : Bool :=
  foldMap_terms true (· && ·) ts (f_term := unannotatedNode)

/-- The same of every term of a cause. -/
def CauseTerm.unannotated (c : CauseTerm) : Bool :=
  foldMap_cause true (· && ·) c (f_cause := fun node => match node with
    | .fail t | .die t => t.unannotated
    | .interrupt who => who.all (·.unannotated)
    | .both _ _ => true)

end Effect4.Program
