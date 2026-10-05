import Effect4.Laws.Program.Template

/-! Measurement for seat T3a's phase 2: the statement of `Ty.matchTemplate_complete_anchored`.

The phase-1 statement (`Statements.lean`, `CompleteAnchored`) quantifies over every normal
request. With the repaired `infer` (a request union read member by member) it is still false: a
union member whose anchor position holds `never` binds the parameter at a covariant occurrence
first, and the next member's anchor cannot rebind it. This probe:

1. evaluates that counterexample under the repaired match;
2. checks the restated goal's implication on a finite pool: every normal template of the pool that
   is admissible and anchored, every substitution of the pool, every normal request of the pool
   with no `never` outside an invariant handle's argument (`Ty.bottomFree`) that the instance
   admits, has a match;
3. counts the pool's failures without the `bottomFree` hypothesis, to show the hypothesis is the
   one the counterexample needs.

A finite probe: it tests the statement on the pool, it proves nothing about other types.
Replay: `lake env lean docs/research/2026-10-04-seat-T3a/AnchoredGoal.lean` under the shared lock. -/

open Effect4.Program

namespace T3aAnchoredGoal

def setT : Ty := .prod (.refOf (.var 0)) (.var 0)

-- 1. The counterexample: `never` at the anchor of the first member.
def neverR : Ty := .union (.prod .never (.lit "a")) (.prod (.refOf .string) (.lit "b"))
#guard neverR.normalize == neverR
#guard Ty.sub neverR.normalize (setT.instantiate [(0, .string)]).normalize
#guard Ty.matchTemplate [] setT neverR.normalize == none
#guard !Ty.bottomFree neverR

-- 2. The pool.
def leaves : List Ty := [.nat, .string, .lit "a", .lit "b", .never, .bool]
def values : List Ty := leaves ++ [.union (.lit "a") (.lit "b"), .union .nat .string, .option .nat]
def handles : List Ty :=
  values.map .refOf ++ (values.flatMap fun a => [Ty.nat, .never, .string].map (Ty.deferredOf a))
def firsts : List Ty := handles ++ [.never, .option (.refOf .string), .option .never]
def pairs : List Ty := firsts.flatMap fun a => values.map (Ty.prod a)
def singles : List Ty := handles ++ pairs
/-- Every candidate request, normalized: the singles and the unions of two pairs of a few heads. -/
def requests : List Ty :=
  (singles ++ ((pairs.take 40).flatMap fun a => (pairs.take 40).map (Ty.union a))).map Ty.normalize

def templates : List Ty := [
  .refOf (.var 0), setT, .deferredOf (.var 0) (.var 1),
  .prod (.deferredOf (.var 0) (.var 1)) (.var 0), .prod (.deferredOf (.var 0) (.var 1)) (.var 1),
  .option (.refOf (.var 0)), .prod (.option (.refOf (.var 0))) (.var 0),
  .prod (.list (.refOf (.var 0))) (.var 0)]

def substs : List Ty.Subst :=
  values.flatMap fun a => [Ty.nat, .never, .string].map fun e => [(0, a), (1, e)]

#guard templates.all fun t => t.normalize == t && t.templateAdmissible && t.anchored

/-- The goal's implication at one triple: `true` when it holds there. -/
def holds (t r : Ty) (τ : Ty.Subst) : Bool :=
  !(Ty.sub r (t.instantiate τ).normalize) || (Ty.matchTemplate [] t r).isSome

def counts (keep : Ty → Bool) : Nat × Nat :=
  templates.foldl (fun acc t => substs.foldl (fun acc τ => requests.foldl (fun (n, bad) r =>
    if keep r && Ty.sub r (t.instantiate τ).normalize then
      (n + 1, if holds t r τ then bad else bad + 1)
    else (n, bad)) acc) acc) (0, 0)

-- (checked triples, failures) with the hypothesis, then without it
#eval requests.length
#eval counts Ty.bottomFree
#eval counts fun _ => true

/-- The requests the instances themselves give, and the unions of two instances of one template:
the region where a substitution exists by construction. -/
def instanceRequests (t : Ty) : List Ty :=
  let xs := substs.map fun τ => (t.instantiate τ).normalize
  xs ++ (xs.take 30).flatMap fun a => (xs.take 30).map fun b => (Ty.union a b).normalize

def instanceCounts (keep : Ty → Bool) : Nat × Nat :=
  templates.foldl (fun acc t => substs.foldl (fun acc τ => (instanceRequests t).foldl (fun (n, bad) r =>
    if keep r && Ty.sub r (t.instantiate τ).normalize then
      (n + 1, if holds t r τ then bad else bad + 1)
    else (n, bad)) acc) acc) (0, 0)

#eval instanceCounts Ty.bottomFree
#eval instanceCounts fun _ => true

end T3aAnchoredGoal
