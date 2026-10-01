import ProbeU.Generic

/-!
# Probe U — enumerations (family (c'')): the unfold from the arity table

The hand enumerations of `Ty` (the conform rungs' `leaves`/`layer`, `rand_ty`, the metadata
samples, the assignability core) are anamorphisms: they build types constructor by constructor
from a hand list, and a constructor the list omits is silently never built (no exhaustiveness
can see an omission in a producer). The generic unfold reads the constructors from the emitted
tag list and their shapes from the view, so a new constructor is enumerated the day it is
declared. `coverage` is the instrument that measures a hand list.
-/

set_option autoImplicit false

namespace ProbeU

open Effect4.Program

/-- Every tag, in declaration order (emitted beside `TyCtor`). -/
def TyCtor.all : List TyCtor :=
  [.never, .unit, .nat, .int, .string, .bool, .handle, .option, .list, .prod, .except, .exitOf,
   .causeOf, .fiberOf, .union, .lit, .refOf, .deferredOf, .var, .unknown]

/-- A sample payload for each sort (the seed of the unfold). -/
def sampleLeaf : TyCtor → TyLeaf
  | .handle => .str "Host.Resource"
  | .lit => .str "tag"
  | .var => .nat 0
  | _ => .none

/-- How many children a tag takes (the view's shape, emitted). -/
def TyCtor.arity : TyCtor → Nat
  | .option | .list | .causeOf | .refOf => 1
  | .prod | .except | .exitOf | .fiberOf | .union | .deferredOf => 2
  | _ => 0

/-- Every type of depth at most `d` over the tags, children drawn from depth `d - 1`
(capped at `width` children choices per position to stay finite and small). -/
def enumTy (width : Nat) : Nat → List Ty
  | 0 => (TyCtor.all.filter (·.arity == 0)).map fun c => tyBuild c (sampleLeaf c) []
  | d + 1 =>
    let below := (enumTy width d).take width
    let pick : TyCtor → List Ty := fun c =>
      match c.arity with
      | 0 => [tyBuild c (sampleLeaf c) []]
      | 1 => below.map fun a => tyBuild c (sampleLeaf c) [a]
      | _ => below.flatMap fun a => below.map fun b => tyBuild c (sampleLeaf c) [a, b]
    TyCtor.all.flatMap pick

/-- Which tags a type reaches, at any depth: the generated monoid fold at the tag. -/
def tagsIn (t : Ty) : List TyCtor :=
  foldMap_ty [] (· ++ ·) t (fun s => [tyCtor s])

def coverage (ts : List Ty) : List TyCtor :=
  TyCtor.all.filter fun c => ts.any fun t => (tagsIn t).contains c

def missing (ts : List Ty) : List TyCtor :=
  TyCtor.all.filter fun c => !(coverage ts).contains c

-- The generic unfold reaches every constructor at depth one (tested).
#guard missing (enumTy 3 1) == []

end ProbeU
