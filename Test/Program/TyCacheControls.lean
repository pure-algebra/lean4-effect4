import Effect4.Laws.Program.Folds.TyCache

/-!
# Controls of the checked type-fold cache

The battery of `fold-cache-local-agreement` (`src/Effect4/Program/TyCache.lean`,
`src/Effect4/Laws/Program/Folds/TyCache.lean`). Each line is a reader of a law at real entries,
a control that shows where `check` refuses, or a finite evaluation that no theorem covers
(decisions row 301). The controls port the research probe's
(`docs/research/2026-10-09-openai-math-probe/TyCache.lean`).

Two layers stand beside the identity layer `tyBuild`. `countLayer` counts nodes, each child
occurrence apart, so a child stored once counts twice. `countTwoLayer` counts with another
weight. A count is a summary: equal counts do not certify equal types, and the controls show it.
-/

namespace Test.Program.TyCacheControls

open Effect4.Program Effect4.Program.TyCache

/-- A node count: one for the node, plus each child occurrence's count. -/
def countLayer (_ : TyCtor) (args : List (TyArgF Nat)) : Nat :=
  1 + (args.flatMap TyArgF.kids).sum

/-- The same shape with another weight per node. -/
def countTwoLayer (_ : TyCtor) (args : List (TyArgF Nat)) : Nat :=
  2 + (args.flatMap TyArgF.kids).sum

def repeated : Ty := .prod .nat .nat
def recordSource : Ty := .record [("left", false, .nat)]
def recordRenamed : Ty := .record [("right", false, .nat)]
def recordOptional : Ty := .record [("left", true, .nat)]
def orderedSource : Ty := .prod .nat .bool
def orderedSwapped : Ty := .prod .bool .nat
def nested : Ty := .record
  [("payload", false, .tuple [.nat, .prod .nat .bool]), ("optional", true, .list .nat)]

/-! ## Readers: the laws at real entries -/

-- `check_agreement` at accepted entries: one stored child consumed at two positions.
example : (3 : Nat) = cata_ty (TyAlgebra.ofLayer countLayer) repeated :=
  check_agreement countLayer [(repeated, 3), (.nat, 1)] (by decide) repeated 3 (by decide)

-- `reconstructs` at accepted entries of the identity layer.
example : ∀ r, lookup [(recordSource, recordSource), (.nat, .nat)] recordSource = some r →
    r = recordSource :=
  fun r found => reconstructs [(recordSource, recordSource), (.nat, .nat)] (by decide)
    recordSource r found

-- `answer_eq` at a nested type: the fold's value 8 is a finite evaluation of the kernel.
example : answer countLayer nested = some 8 :=
  (answer_eq countLayer nested).trans (by decide)

-- `answer_eq` at the identity layer returns the type itself, names, flags and order kept.
example : answer tyBuild nested = some nested :=
  (answer_eq tyBuild nested).trans (congrArg some (reconstruction_fold nested))

/-! ## Controls: where `check` refuses -/

-- green: the stored child counts at both positions of `prod`; red: an answer that counts it once
#guard check countLayer [(repeated, 3), (.nat, 1)]
#guard !check countLayer [(repeated, 2), (.nat, 1)]

-- red: a missing child is refused, even where the fold's fallback would give the right answer
#guard !check countLayer [(repeated, 3)]
#guard !check tyBuild [(repeated, repeated)]

-- green: a count accepts a renamed record and a flipped flag at their own sources, so a count
-- certifies no name and no flag
#guard check countLayer [(recordRenamed, 2), (.nat, 1)]
#guard check countLayer [(recordOptional, 2), (.nat, 1)]

-- red: the identity layer refuses a renamed field, a flipped flag and swapped children
#guard check tyBuild [(recordSource, recordSource), (.nat, .nat)]
#guard !check tyBuild [(recordSource, recordRenamed), (.nat, .nat)]
#guard !check tyBuild [(recordSource, recordOptional), (.nat, .nat)]
#guard check tyBuild [(orderedSource, orderedSource), (.nat, .nat), (.bool, .bool)]
#guard !check tyBuild [(orderedSource, orderedSwapped), (.nat, .nat), (.bool, .bool)]

-- red: the layer is part of acceptance; a count of `countLayer` is no count of `countTwoLayer`
#guard (admit countTwoLayer [(repeated, 3), (.nat, 1)]).isNone
#guard (admit countTwoLayer [(repeated, 6), (.nat, 2)]).isSome

-- red: a query at a type that no entry holds is refused, never computed by the fold
#guard ((admit tyBuild [(recordRenamed, recordRenamed), (.nat, .nat)]).bind
  (fun cache => cache.query recordSource)).isNone
#guard ((admit countLayer ([] : Entries Nat)).bind (fun cache => cache.query .nat)).isNone
#guard ((prepare countLayer nested).bind (fun cache => cache.query (.tuple []))).isNone

/-! ## Finite evaluations -/

-- the building fold keeps duplicate entries: `repeated` and its child twice
#guard (produce countLayer repeated).entries.length == 3

end Test.Program.TyCacheControls
