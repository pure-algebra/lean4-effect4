module

public import Effect4.Program.Ty

/-!
# Program.Bounds — the match of a template by bounds

**What it is.** One function matches a template against a request, for an atom's scheme, a
row's request and an operation's binder term (decisions rows 299 and 303). It replaces the
match by first occurrence and its `join` flag.

1. `cands` walks the template and the request together. At each occurrence of a parameter it
   gives one candidate: the parameter, the polarity of the occurrence, and the request's type
   there. A request that is a union is read member by member.
2. `solve` binds each parameter that the seed does not bind to the join of its lower bounds
   (`lowers`, `joinCands`). A candidate at a contravariant occurrence is no lower bound.
3. `matchB` checks the request against the template's instance at those bindings, both in
   normal form. That guard is the whole meaning of the match: it is sound by the guard
   (`matchB_sound`, `src/Effect4/Laws/Program/Bounds.lean`).

`matchArgsB` matches an argument list: every parameter is solved from every argument, and then
every argument is checked at the same, final bindings.

**The interim guard at a binder term** (`termGuard`, `matchTerm`; decisions row 299, point 10).
tsgo infers a type argument by choosing one candidate: the one that every other candidate is
below, or else the first. It forms no join of two candidates with no order. An operation's own
term is typed by Effect's declaration of the operation, so the TypeScript printer would have to
write the join as a type argument, and it does not yet. Until it does, the match of a binder
term asks that the term's type offers each parameter a greatest lower bound. The guard goes in
one line: `matchTerm` becomes `matchB`.

An atom needs no guard: its prelude declaration takes an argument's whole type, and tsgo
computes the join there (`NativeAtom.row`, `src/Effect4/Machine/Term.lean`). A row's request
needs none: where the match answers at a cell, the cell's content is the greatest lower bound.

**What it is not.**
- It is no general constraint solver. It computes no upper bound from a contravariant
  occurrence.
- It does not match under a union head or a nominal reference of a template.
  `Ty.templateAdmissible` refuses both at a signature's admission.
- It does not model tsgo's inference. The guard and the prelude's declarations keep the checker
  inside what tsgo accepts, and the truth lane tests that on finite programs.

**Depends on.** `Ty` alone: its order, its normal form and its join.

**Properties.** The laws are in `src/Effect4/Laws/Program/Bounds.lean`: sound, least and
complete in the checker's order, monotone in the arguments, and one match for one normal form.
-/

@[expose] public section

namespace Effect4.Program

namespace Bounds

abbrev Variance := Ty.Variance
abbrev Subst := Ty.Subst

/-- The variance of an occurrence under a position: the outer position's, then the inner one's. -/
def comp : Variance → Variance → Variance
  | .inv, _ => .inv
  | _, .inv => .inv
  | .co, v => v
  | .contra, .co => .contra
  | .contra, .contra => .co

/-- A candidate: a parameter, the polarity of its occurrence, and the request's type there. -/
abbrev Cand := Nat × Variance × Ty

mutual
/-- The candidates of a request for a template's parameters, in the order of the walk: the
template and the request head by head, and a request union member by member. The polarity of a
child is its parent's, composed with the variance that `Ty.sub` reads the child at: covariant, invariant at a cell, a deferred and a map's key, and the
declared variance at a nominal reference (`Ty.argVariance`). -/
def cands (v : Variance) (template request : Ty) : List Cand :=
  match template, request with
  | .var i, r => [(i, v, r)]
  | .option t, .option r => cands v t r
  | .list t, .list r => cands v t r
  | .causeOf t, .causeOf r => cands v t r
  | .refOf t, .refOf r => cands (comp v .inv) t r
  | .prod a b, .prod c d => cands v a c ++ cands v b d
  | .except a b, .except c d => cands v a c ++ cands v b d
  | .exitOf a b, .exitOf c d => cands v a c ++ cands v b d
  | .fiberOf a b, .fiberOf c d => cands v a c ++ cands v b d
  | .deferredOf a b, .deferredOf c d => cands (comp v .inv) a c ++ cands (comp v .inv) b d
  | .union a b, .union c d => cands v a c ++ cands v b d
  | .map a b, .map c d => cands (comp v .inv) a c ++ cands v b d
  | .record fs, .record gs => candsFields v fs gs
  | .tuple ts, .tuple rs => candsItems v ts rs
  | .app name ts, .app other rs => if name = other then candsArgs v name 0 ts rs else []
  | t, .union c d => cands v t c ++ cands v t d
  | _, _ => []
termination_by structural request

/-- A record's candidates by field name, in the request's field order. -/
def candsFields (v : Variance) (templates requests : List (String × Bool × Ty)) : List Cand :=
  match requests with
  | [] => []
  | (name, _, request) :: rest =>
    match templates.lookup name with
    | none => candsFields v templates rest
    | some (_, ty) => cands v ty request ++ candsFields v templates rest
termination_by structural requests

/-- A tuple's candidates by position. -/
def candsItems (v : Variance) (templates requests : List Ty) : List Cand :=
  match templates, requests with
  | ty :: rest, request :: remaining => cands v ty request ++ candsItems v rest remaining
  | _, _ => []
termination_by structural requests

/-- A nominal reference's candidates by position, each argument at its declared variance. -/
def candsArgs (v : Variance) (name : String) (k : Nat) (templates requests : List Ty) : List Cand :=
  match templates, requests with
  | ty :: rest, request :: remaining =>
    cands (comp v (Ty.argVariance name k)) ty request ++ candsArgs v name (k + 1) rest remaining
  | _, _ => []
termination_by structural requests
end

/-- The join of a parameter's candidates. One candidate is kept as it is, so a parameter that
occurs once binds to the request's own raw type. -/
def joinCands : List Ty → Ty
  | [] => .never
  | [c] => c
  | c :: rest => Ty.join c (joinCands rest)

/-- The lower bounds of a parameter: its candidates at the occurrences that are not
contravariant. -/
def lowers (cs : List Cand) (i : Nat) : List Ty :=
  cs.filterMap fun c => if c.1 = i ∧ c.2.1 ≠ .contra then some c.2.2 else none

/-- The solved bindings: the seed's, then each other parameter at the join of its lower bounds.
A parameter is entered once for each of its candidates, with one value, so `lookup` reads the
same binding at each. A parameter with no lower bound gets no binding, and `Ty.instantiate`
reads it as `never`. -/
def solve (seed : Subst) (cs : List Cand) : Subst :=
  seed ++ cs.filterMap fun c =>
    if c.2.1 = .contra ∨ (seed.lookup c.1).isSome then none
    else some (c.1, joinCands (lowers cs c.1))

/-- **The match by bounds** of a request against a template from a seed. The solved bindings
are kept where the request is below the template's instance at them, both in normal form. -/
def matchB (seed : Subst) (template request : Ty) : Option Subst :=
  let σ := solve seed (cands .co template request)
  if Ty.sub request.normalize (Ty.instantiate σ template).normalize then some σ else none

/-- The candidates of an argument list for a parameter list, argument by argument. -/
def candsList (params requests : List Ty) : List Cand :=
  (params.zip requests).flatMap fun pr => cands .co pr.1 pr.2

/-- **The match by bounds of an argument list.** Every parameter is solved from every argument,
and then every argument is checked against its parameter's instance at those bindings. A list
of another length is refused. -/
def matchArgsB (params requests : List Ty) : Option Subst :=
  if params.length = requests.length then
    let σ := solve [] (candsList params requests)
    if (params.zip requests).all fun pr =>
        Ty.sub pr.2.normalize (Ty.instantiate σ pr.1).normalize then some σ
    else none
  else none

/-! ## The interim guard at a binder term -/

/-- A candidate of the list that every candidate of the list is below, in the order of
`Ty.sub`. The callers pass normal forms. -/
def greatestOf (ls : List Ty) : Option Ty := ls.find? fun c => ls.all fun d => Ty.sub d c

/-- The candidates have a greatest one. No candidate and one candidate have one, by the shape
of the list: a symbolic type needs no fact of the order there. -/
def hasGreatest : List Ty → Bool
  | [] | [_] => true
  | ls => (greatestOf ls).isSome

/-- **The interim guard at a binder term** (decisions row 299, point 10). The request offers
each parameter that the seed does not bind lower bounds with a greatest one, in normal form.
tsgo then infers the join as its type argument: the join of candidates with a greatest one is
that candidate.

It refuses a request where two lower bounds of one parameter have no order. The match by
bounds answers there, with their join. tsgo refuses the printed call where it forms no union of
the two (`docs/research/2026-10-07-chunk-2-review-evidence/binder_joined.ts.txt`).

**What removes it.** The TypeScript printer writes the type arguments of a row call at the
join. `matchTerm` then says `matchB`. -/
def termGuard (seed : Subst) (template request : Ty) : Bool :=
  let cs := cands .co template request
  cs.all fun c => (seed.lookup c.1).isSome || hasGreatest ((lowers cs c.1).map Ty.normalize)

/-- **The match of a binder term**: the match by bounds, under the interim guard. It answers
only where `matchB` answers, with the same bindings (`matchB_of_matchTerm`,
`src/Effect4/Laws/Program/Template.lean`). -/
def matchTerm (seed : Subst) (template request : Ty) : Option Subst :=
  if termGuard seed template request then matchB seed template request else none

end Bounds

end Effect4.Program
