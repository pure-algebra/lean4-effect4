import Effect4.Program.TyFoldExtras
import ProofGraph.Proof

/-! Research adapter for `fold-cache-local-agreement` in OPERATIONAL-PLAN.md.
Consumer: D6, reusable cached folds, serving R14. Concept: initial-algebras-folds.
Rows retain real Ty source nodes. Each new row uses only previously supplied rows.
The list stores the newest row first. No alternative Ty signature is maintained.
Agreement compares one accepted answer with the generated fold of the same layer.
It establishes neither typing admission nor a performance bound. -/
set_option autoImplicit false
namespace MathTransferProbe.TyCache
open Effect4.Program

universe u
abbrev Rows (R : Type u) := List (Ty × R)

/-- Exact structural source lookup; no hash collision premise is required. -/
def lookup {R : Type u} : Rows R → Ty → Option R
  | [], _ => none
  | (s, r) :: rest, t => if t.key = s.key then some r else lookup rest t

/-- Totalization is used in the mathematical local equation. Accepted rows have
all children present, so their local equations never need this fallback. -/
def read {R : Type u} (layer : TyCtor → List (TyArgF R) → R)
    (rows : Rows R) (t : Ty) : R :=
  match lookup rows t with
  | some r => r
  | none => cata_ty (TyAlgebra.ofLayer layer) t

/-- Payloads and ordered child occurrences come from the source's generated view. -/
def localValue {R : Type u} (layer : TyCtor → List (TyArgF R) → R)
    (previous : Rows R) (t : Ty) : R :=
  layer (tyCtor t) ((tyArgs t).map (TyArgF.map (read layer previous)))

/-- Each row uses earlier children and satisfies its exact source layer equation. -/
def Valid {R : Type u} (layer : TyCtor → List (TyArgF R) → R) : Rows R → Prop
  | [] => True
  | (t, r) :: previous => Valid layer previous ∧
      (tyKids t).all (fun child => (lookup previous child).isSome) = true ∧
      r = localValue layer previous t

/-- Executable admission of the same finite local equations. -/
def check {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) : Rows R → Bool
  | [] => true
  | (t, r) :: previous => check layer previous &&
      ((tyKids t).all (fun child => (lookup previous child).isSome) &&
        decide (r = localValue layer previous t))

/-- Helper for fold-cache-local-agreement: accepted data satisfies the contract. -/
theorem check_valid {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) (rows : Rows R)
    (accepted : check layer rows = true) : Valid layer rows := by
  induction rows with
  | nil => exact True.intro
  | cons row previous ih =>
    cases row with
    | mk t r =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨ih accepted.1, accepted.2.1, accepted.2.2⟩

/-- Helper for fold-cache-local-agreement: totalization agrees with the fold
once every stored answer does. Its fallback is evaluated only on a missing row. -/
theorem read_agrees {R : Type u} (layer : TyCtor → List (TyArgF R) → R)
    (rows : Rows R)
    (answers : ∀ t r, lookup rows t = some r →
      r = cata_ty (TyAlgebra.ofLayer layer) t) (t : Ty) :
    read layer rows t = cata_ty (TyAlgebra.ofLayer layer) t := by
  unfold read
  cases found : lookup rows t with
  | none => rfl
  | some r => exact answers t r found

/-- Proposed tool law fold-cache-local-agreement. Local equations on real source
rows determine every covered answer, including repeated children and payloads.
The decreasing dependency order is the list of rows supplied before each row. -/
theorem valid_agreement {R : Type u} (layer : TyCtor → List (TyArgF R) → R)
    (rows : Rows R) (valid : Valid layer rows) :
    ∀ t r, lookup rows t = some r →
      r = cata_ty (TyAlgebra.ofLayer layer) t := by
  induction rows with
  | nil =>
    intro t r found
    cases found
  | cons row previous ih =>
    cases row with
    | mk s value =>
      rcases valid with ⟨prior, _covered, equation⟩
      have previousAnswers := ih prior
      have total : read layer previous = cata_ty (TyAlgebra.ofLayer layer) :=
        funext (read_agrees layer previous previousAnswers)
      have head : value = cata_ty (TyAlgebra.ofLayer layer) s := by
        rw [equation, localValue, total]
        exact (cata_ofLayer_view layer s).symm
      intro t r found
      simp only [lookup] at found
      split at found
      next same =>
        have source : t = s := Ty.key_injective same
        have answer : value = r := Option.some.inj found
        rw [← answer, source]
        exact head
      next _ => exact previousAnswers t r found

/-- Accepted cache lookup is the generated fold at the exact queried source. -/
theorem check_agreement {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) (rows : Rows R)
    (accepted : check layer rows = true) (t : Ty) (r : R)
    (found : lookup rows t = some r) :
    r = cata_ty (TyAlgebra.ofLayer layer) t :=
  valid_agreement layer rows (check_valid layer rows accepted) t r found

/-- Author-facing admitted data binds the algebra and validates its rows once. -/
structure CheckedCache {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) where
  rows : Rows R
  accepted : check layer rows = true

/-- Reject invalid rows before serving any query. Empty rows are valid data. -/
def admit {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) (rows : Rows R) :
    Option (CheckedCache layer) :=
  if accepted : check layer rows = true then some ⟨rows, accepted⟩ else none

/-- A requested source absent from admitted data is refused, without fold fallback. -/
def CheckedCache.query {R : Type u} [DecidableEq R]
    {layer : TyCtor → List (TyArgF R) → R} (cache : CheckedCache layer) (root : Ty) :
    Option R := lookup cache.rows root

/-- Consumer of local agreement: every answer from admitted data is the same fold. -/
theorem CheckedCache.query_agrees {R : Type u} [DecidableEq R]
    {layer : TyCtor → List (TyArgF R) → R} (cache : CheckedCache layer)
    (root : Ty) (r : R) (answered : cache.query root = some r) :
    r = cata_ty (TyAlgebra.ofLayer layer) root :=
  check_agreement layer cache.rows cache.accepted root r answered

/-- Derived fold output: reconstructed source, its answer, and candidate cache rows.
Duplicate rows are permitted. This prototype makes no performance claim. -/
structure Built (R : Type u) where
  source : Ty
  value : R
  rows : Rows R

/-- Mechanical row production reads only the generated layer view.
Each child keeps its position when reconstructing the source and applying the layer.
Its rows precede the parent in construction, represented newest-first in the list. -/
def producerLayer {R : Type u} (layer : TyCtor → List (TyArgF R) → R)
    (ctor : TyCtor) (args : List (TyArgF (Built R))) : Built R :=
  let source := tyBuild ctor (args.map (TyArgF.map Built.source))
  let value := layer ctor (args.map (TyArgF.map Built.value))
  let previous := (args.flatMap TyArgF.kids).flatMap Built.rows
  ⟨source, value, (source, value) :: previous⟩

/-- Generate candidate answers and rows through the existing Ty fold. -/
def produce {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (source : Ty) :
    Built R := cata_ty (TyAlgebra.ofLayer (producerLayer layer)) source

/-- Author-facing preparation: mechanically produce rows, then validate once.
No theorem here promises that this candidate producer always passes admission. -/
def prepare {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) (source : Ty) :
    Option (CheckedCache layer) := admit layer (produce layer source).rows

/-- Prepare and request the source root without constructing any rows by hand. -/
def answer {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) (source : Ty) : Option R :=
  (prepare layer source).bind (fun cache => cache.query source)

/-- Consumer of local agreement: every mechanically prepared returned answer
agrees with the generated fold at the original requested source. -/
theorem answer_agrees {R : Type u} [DecidableEq R]
    (layer : TyCtor → List (TyArgF R) → R) (source : Ty) (r : R)
    (answered : answer layer source = some r) :
    r = cata_ty (TyAlgebra.ofLayer layer) source := by
  unfold answer at answered
  cases prepared : prepare layer source with
  | none =>
    simp only [prepared, Option.bind_none] at answered
    cases answered
  | some cache =>
    simp only [prepared, Option.bind_some] at answered
    exact cache.query_agrees source r answered

/-- Reconstruction uses the existing generated identity algebra, not a new match. -/
theorem reconstruction_fold (t : Ty) :
    cata_ty (TyAlgebra.ofLayer tyBuild) t = t := by
  change cata_ty TyAlgebra.id t = t
  exact cata_id_ty t

/-- Consumer of check_agreement: accepted reconstruction returns the source. -/
theorem reconstructs (rows : Rows Ty) (accepted : check tyBuild rows = true)
    (t r : Ty) (found : lookup rows t = some r) : r = t :=
  (check_agreement tyBuild rows accepted t r found).trans (reconstruction_fold t)

/-- Mechanical reconstruction returns the exact requested source when it answers. -/
theorem answer_reconstructs (source r : Ty)
    (answered : answer tyBuild source = some r) : r = source :=
  (answer_agrees tyBuild source r answered).trans (reconstruction_fold source)

/-- A reusable scalar summary; child occurrences contribute independently. -/
def countLayer (_ : TyCtor) (args : List (TyArgF Nat)) : Nat :=
  1 + (args.flatMap TyArgF.kids).sum

def repeated : Ty := .prod .nat .nat
def recordSource : Ty := .record [("left", false, .nat)]
def recordRenamed : Ty := .record [("right", false, .nat)]
def recordOptional : Ty := .record [("left", true, .nat)]

-- One cached child is consumed twice, in its two source positions.
#guard check countLayer [(repeated, 3), (.nat, 1)]
#guard !check countLayer [(repeated, 2), (.nat, 1)]
#guard check tyBuild [(repeated, repeated), (.nat, .nat)]
#guard !check tyBuild [(repeated, .prod .nat .bool), (.nat, .nat)]
-- A missing child is refused even when fallback would calculate the right answer.
#guard !check countLayer [(repeated, 3)]
#guard !check tyBuild [(repeated, repeated)]
-- A correct summary cannot certify unchanged names or flags. Reconstruction can.
#guard check countLayer [(recordSource, 2), (.nat, 1)]
#guard check countLayer [(recordRenamed, 2), (.nat, 1)]
#guard check countLayer [(recordOptional, 2), (.nat, 1)]
#guard check tyBuild [(recordSource, recordSource), (.nat, .nat)]
#guard !check tyBuild [(recordSource, recordRenamed), (.nat, .nat)]
#guard !check tyBuild [(recordSource, recordOptional), (.nat, .nat)]
#guard (lookup [(recordRenamed, recordRenamed), (.nat, .nat)] recordSource).isNone

-- Callers validate once and query; an absent requested source stays unanswered.
#guard (admit countLayer [(repeated, 3), (.nat, 1)]).isSome
#guard ((admit countLayer [(repeated, 3), (.nat, 1)]).bind
  (fun cache => cache.query repeated)) == some 3
#guard (admit countLayer ([] : Rows Nat)).isSome
#guard ((admit countLayer ([] : Rows Nat)).bind
  (fun cache => cache.query .nat)).isNone
#guard ((admit tyBuild [(recordRenamed, recordRenamed), (.nat, .nat)]).bind
  (fun cache => cache.query recordSource)).isNone

-- Algebra identity is part of admission. Answers for another layer do not transfer.
def countTwoLayer (_ : TyCtor) (args : List (TyArgF Nat)) : Nat :=
  2 + (args.flatMap TyArgF.kids).sum
#guard (admit countTwoLayer [(repeated, 3), (.nat, 1)]).isNone
#guard (admit countTwoLayer [(repeated, 6), (.nat, 2)]).isSome

-- Reconstruction retains ordered child occurrences, not merely a dependency set.
def orderedSource : Ty := .prod .nat .bool
def orderedSwapped : Ty := .prod .bool .nat
#guard (admit tyBuild
  [(orderedSource, orderedSource), (.nat, .nat), (.bool, .bool)]).isSome
#guard (admit tyBuild
  [(orderedSource, orderedSwapped), (.nat, .nat), (.bool, .bool)]).isNone

-- Mechanical preparation handles nested containers and repeated source children.
def nested : Ty := .record
  [("payload", false, .tuple [.nat, .prod .nat .bool]),
   ("optional", true, .list .nat)]
#guard (prepare countLayer nested).isSome
#guard answer countLayer nested == some 8
#guard answer countTwoLayer nested == some 16
#guard decide (answer tyBuild nested = some nested)
#guard decide (answer tyBuild recordRenamed = some recordRenamed)
#guard decide (answer tyBuild recordOptional = some recordOptional)
#guard decide (answer tyBuild orderedSource = some orderedSource)
#guard decide (answer tyBuild orderedSwapped = some orderedSwapped)
#guard answer countLayer repeated == some 3
#guard (produce countLayer repeated).rows.length == 3
#guard ((prepare countLayer nested).bind (fun cache => cache.query (.tuple []))).isNone

-- This reader obtains agreement through the automatic author-facing operation.
example : (8 : Nat) = cata_ty (TyAlgebra.ofLayer countLayer) nested :=
  answer_agrees countLayer nested 8 (by decide)

-- Readers apply the universal law at the actual generated type layer.
example : (3 : Nat) = cata_ty (TyAlgebra.ofLayer countLayer) repeated :=
  check_agreement countLayer [(repeated, 3), (.nat, 1)] (by decide)
    repeated 3 (by decide)

example : recordSource = recordSource :=
  reconstructs [(recordSource, recordSource), (.nat, .nat)] (by decide)
    recordSource recordSource (by decide)

-- Exact axiom evidence is collected by the project's cycle-aware audit.
def checkedTyCache : ProofGraph.ProofRef := checked_theorem% check_agreement
run_elab do
  let env ← Lean.getEnv
  for name in [``check_agreement, ``CheckedCache.query_agrees, ``reconstructs, ``answer_agrees, ``answer_reconstructs] do
    let some reached := ProofGraph.exactAxioms env name
      | throwError "axiom walk exhausted its budget"
    Lean.logInfo m!"{name} exact axioms: {reached}"

end MathTransferProbe.TyCache
