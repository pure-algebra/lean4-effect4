module

public import Effect4.Program.Fold

/-!
# Program.Polarity — the variance semiring and the polarity of a template's parameter

Slice VAR-1 of `docs/research/2026-10-10-openai-math-type-systems/brief.md`. A variance is the
set of parities of the signed paths that reach an occurrence: an even path (`pos`) asks for the
relation, an odd one (`neg`) for its converse. So there are four variances: bivariant (no path),
co, contra and inv (`Var4`). Join is union and composition adds parities: a commutative idempotent
semiring (`Laws/Program/Polarity.lean`). It adapts the signed paths of the OpenAI formalization
of the β-Barendregt–Geuvers–Klop conjecture (`openai/math` at `fd4aeeb2`,
`lean/OAI/Computability/TypeSystem/Profiles.lean`, `SignedPath`).

The tree held three partial copies: the declared alphabet `Ty.Variance` (no bivariant point, no
composition), `Bounds.comp` (composition along a walk) and `Ty.valueVarsAlg` (a two-bit fold).
`Var4` is the one carrier. `Ty.Variance` stays the declared alphabet that `Ty.sub` reads at `app`,
and it embeds (`Ty.Variance.toVar4`). The bivariant point is what a phantom parameter has: no
path reaches it, so it constrains nothing.

The polarity of a parameter in a type is a fold of the generated `TyAlgebra` (`polarityAlg`).
A reading (`HeadReading`) names the variance of each head's positions that are not plainly
covariant; `HeadReading.sub` is `Ty.sub`'s. The fold establishes no subtyping fact by itself:
`Laws/Program/Polarity.lean` connects it.
-/

@[expose] public section

namespace Effect4.Program

/-- **A variance**: whether an even-parity path (`pos`) and an odd-parity path (`neg`) reach an
occurrence. `⟨false, false⟩` is bivariant, `⟨true, false⟩` co, `⟨false, true⟩` contra and
`⟨true, true⟩` inv. -/
structure Var4 where
  pos : Bool
  neg : Bool
deriving DecidableEq, Repr

namespace Var4

/-- No path: the position constrains nothing. -/
def bi : Var4 := ⟨false, false⟩
/-- Only even paths: the relation itself. -/
def co : Var4 := ⟨true, false⟩
/-- Only odd paths: the converse. -/
def contra : Var4 := ⟨false, true⟩
/-- Both parities: both directions. -/
def inv : Var4 := ⟨true, true⟩

/-- Join: the parities of either set of paths. -/
def add (a b : Var4) : Var4 := ⟨a.pos || b.pos, a.neg || b.neg⟩

/-- Composition: parities add along a path. -/
def mul (a b : Var4) : Var4 :=
  ⟨(a.pos && b.pos) || (a.neg && b.neg), (a.pos && b.neg) || (a.neg && b.pos)⟩

instance : Add Var4 := ⟨add⟩
instance : Mul Var4 := ⟨mul⟩

/-- The order: inclusion of parity sets. A larger variance is a stronger premise. -/
def le (a b : Var4) : Bool := (!a.pos || b.pos) && (!a.neg || b.neg)

/-- **The Boolean reading of a relation at a variance**: each parity asks for one direction, given
the relation's answer forwards (`xy`) and backwards (`yx`). -/
def select (v : Var4) (xy yx : Bool) : Bool := (!v.pos || xy) && (!v.neg || yx)

end Var4

/-- A declared variance as a parity set. -/
def Ty.Variance.toVar4 : Ty.Variance → Var4
  | .co => .co
  | .contra => .contra
  | .inv => .inv

/-- **A reading of the heads**: the variance of each position that a reading of the type language
does not read plainly covariantly. Every other position is covariant. -/
structure HeadReading where
  refOf : Var4
  deferredOf : Var4
  fiberOf : Var4
  mapKey : Var4
  app : String → Nat → Var4

/-- **`Ty.sub`'s reading** (`src/Effect4/Program/Ty.lean`, `sub`'s arms): a cell and a promise are
invariant (`Ref<in out A>`, `Deferred<in out A, in out E>`), a fiber covariant, a map's key
exact, and a reference's argument at its declaration's variance (`Ty.argVariance`). -/
def HeadReading.sub : HeadReading where
  refOf := .inv
  deferredOf := .inv
  fiberOf := .co
  mapKey := .inv
  app n k := (Ty.argVariance n k).toVar4

/-- The join of the polarities of a reference's arguments, each read at its position. -/
def appPolarity (at_ : Nat → Var4) : Nat → List Var4 → Var4
  | _, [] => .bi
  | k, v :: vs => at_ k * v + appPolarity at_ (k + 1) vs

/-- **The polarity algebra** of parameter `i` at a reading: a parameter is co where it stands, a
leaf is bi, a position composes with what stands in it, and siblings join. -/
def polarityAlg (r : HeadReading) (i : Nat) : TyAlgebra (fun _ => Var4) where
  ty_never := .bi
  ty_unit := .bi
  ty_nat := .bi
  ty_int := .bi
  ty_string := .bi
  ty_bool := .bi
  ty_handle _ := .bi
  ty_option a := a
  ty_list a := a
  ty_prod a b := a + b
  ty_except a b := a + b
  ty_exitOf a b := a + b
  ty_causeOf a := a
  ty_fiberOf a b := r.fiberOf * (a + b)
  ty_union a b := a + b
  ty_lit _ := .bi
  ty_refOf a := r.refOf * a
  ty_deferredOf a b := r.deferredOf * (a + b)
  ty_var j := if i = j then .co else .bi
  ty_unknown := .bi
  ty_record fs := fs.foldr (fun f acc => f.2.2 + acc) .bi
  ty_map k v := r.mapKey * k + v
  ty_tuple ts := ts.foldr (· + ·) .bi
  ty_app n ts := appPolarity (r.app n) 0 ts
  ty_null := .bi
  ty_undefined := .bi
  ty_number := .bi
  ty_bytes := .bi

/-- **The polarity of parameter `i` in a type**, at a reading: the parities of the signed paths
from the root to its occurrences. -/
def Ty.polarity (r : HeadReading) (i : Nat) (t : Ty) : Var4 := cata_ty (polarityAlg r i) t

end Effect4.Program
