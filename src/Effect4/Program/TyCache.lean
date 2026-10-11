module

public import Effect4.Program.TyFoldExtras

@[expose] public section

set_option autoImplicit false

/-!
# Checked caches of a type fold

A cache of a layer function holds entries: a source type and a candidate answer, the newest entry
first. `check` accepts entries when every child of each source stands in an earlier entry, and
each answer satisfies the layer's local equation at its own source (`localValue`). The law
`check_agreement` (`src/Effect4/Laws/Program/Folds/TyCache.lean`) then identifies every answer of
accepted entries with `cata_ty` of the same layer at its own source.

The technique adapts `rowAt_unique` of the openai/math board-game note: local equations, then
strong induction (`docs/research/2026-10-09-openai-math-probe/README.md`). An entry reads the
generated view of `Ty` (`tyCtor`, `tyArgs`, `tyKids` and `tyBuild`,
`src/Effect4/Program/TyFoldExtras.lean`), so this module keeps no constructor match of its own. A
local equation reads the payloads and the ordered child occurrences. So a field name, a flag and
the order of two children are part of each equation.

The interface has two steps. `prepare` builds the entries through the same fold, then runs `check`
once. `CheckedCache.query` reads the answer at a type that an entry holds, and refuses
any other source. `answer` does both at the root.

Placement: concept `initial-algebras-folds`, the claim `fold-cache-local-agreement`. The consumer
is slice D6 of `docs/research/2026-10-09-program-graph-design.md`, memoized folds, serving R14.

What it does not establish:

- no speed: the lookup is linear, the entries keep duplicates, and `prepare` computes the whole
  fold before it checks the entries;
- no typing judgment and no equality of the answers at two different types;
- no reuse after an edit: an accepted cache serves its own entries only;
- a layer that reads an inherited input needs that input in its source: a type alone keys a
  context-free layer only.
-/

namespace Effect4.Program.TyCache

universe u

/-- The entries of a cache: a source type and its candidate answer, the newest entry first. -/
abbrev Entries (R : Type u) := List (Ty × R)

/-- The answer of the newest entry whose source is the requested type. The source is compared by
its injective structural key (`Ty.key_injective`), so no hash and no collision premise is read. -/
def lookup {R : Type u} : Entries R → Ty → Option R
  | [], _ => none
  | (s, r) :: rest, t => if t.key = s.key then some r else lookup rest t

/-- The entries' answer at a type, and the fold of the layer where no entry holds the type. The
local equation reads it at the children of a source. Accepted entries hold every child, so their
equations never read the fold. -/
def read {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (entries : Entries R) (t : Ty) : R :=
  match lookup entries t with
  | some r => r
  | none => cata_ty (TyAlgebra.ofLayer layer) t

/-- The local equation's right side: the layer at the source's tag and arguments, each child read
from the earlier entries at its position, every payload kept. -/
def localValue {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (previous : Entries R)
    (t : Ty) : R :=
  layer (tyCtor t) ((tyArgs t).map (TyArgF.map (read layer previous)))

/-- Accept entries when each entry's children stand in the earlier entries and its answer is the
local equation's right side at its own source. -/
def check {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R) :
    Entries R → Bool
  | [] => true
  | (t, r) :: previous => check layer previous &&
      ((tyKids t).all (fun child => (lookup previous child).isSome) &&
        decide (r = localValue layer previous t))

/-- A cache bound to its layer: entries that `check` accepted for that layer. -/
structure CheckedCache {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R) where
  entries : Entries R
  accepted : check layer entries = true

/-- Run `check` once, before any query. Entries it does not accept give no cache. Empty entries
are accepted, and they answer no query. -/
def admit {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R)
    (entries : Entries R) : Option (CheckedCache layer) :=
  if accepted : check layer entries = true then some ⟨entries, accepted⟩ else none

/-- The answer at a type that an entry holds. Any other type is refused; the fold is not read. -/
def CheckedCache.query {R : Type u} [DecidableEq R] {layer : TyCtor → List (TyArgF R) → R}
    (cache : CheckedCache layer) (t : Ty) : Option R :=
  lookup cache.entries t

/-- What the building fold returns at a type: the source rebuilt from its view, its answer, and
the candidate entries, the source's own entry first. Duplicate entries are kept. -/
structure Built (R : Type u) where
  source : Ty
  value : R
  entries : Entries R

/-- The building layer reads the generated view only. Each child keeps its position in the
rebuilt source and in the layer's arguments. The children's entries precede the node's own, so
the node's entry is the newest. -/
def producerLayer {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (ctor : TyCtor)
    (args : List (TyArgF (Built R))) : Built R :=
  let source := tyBuild ctor (args.map (TyArgF.map Built.source))
  let value := layer ctor (args.map (TyArgF.map Built.value))
  let previous := (args.flatMap TyArgF.kids).flatMap Built.entries
  ⟨source, value, (source, value) :: previous⟩

/-- The candidate entries of a type, built by the generated fold of `Ty`. -/
def produce {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (t : Ty) : Built R :=
  cata_ty (TyAlgebra.ofLayer (producerLayer layer)) t

/-- Build the candidate entries of a type, then run `check` on them once. -/
def prepare {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    Option (CheckedCache layer) :=
  admit layer (produce layer t).entries

/-- Build and check the entries of a type, then read the answer at the type itself. -/
def answer {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    Option R :=
  (prepare layer t).bind (fun cache => cache.query t)

end Effect4.Program.TyCache
