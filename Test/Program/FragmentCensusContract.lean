import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.FragmentLoopedRows
import Effect4.Laws.Program.Folds.Straight
import Effect4.Laws.Program.Folds.Looped
import Effect4.Laws.Program.Folds.DenoteRows
import Effect4.Program.LayerView
import Effect4.Program.Authoring

/-!
# Fragment census — which constructors each proved fragment admits

`Straight`, `Looped`, `StraightRows` and `LoopedRows` use one generator classification table.
The generated predicates name every constructor. Unknown constructors refuse generation.
This battery compares its samples with the generated family's constructor inventory.
Each constructor therefore needs both an explicit classification and a sample.

Children are the straight leaf `succeed unit`, so a composite form is admitted exactly when the
fragment admits its head.
-/

set_option autoImplicit false

namespace Test.Program.FragmentCensusContract

open Effect4 Effect4.Program Effect4.Program.Denote

private def u : NativeEff := .succeed (.lit .unit)
private def t : Term := .lit .unit

/-- One program per constructor, in the alphabet's order. -/
def samples : List (String × NativeEff) :=
  [ ("succeed", u), ("fail", .fail t), ("failCause", .failCause (.fail t)), ("sync", .sync t)
  , ("suspend", .suspend u), ("perform", .perform .refMake t), ("bind", .bind u u)
  , ("gen", .gen .nil), ("catchCause", .catchCause u u), ("matchCause", .matchCause u u u)
  , ("onExit", .onExit u u), ("exit", .exit u), ("uninterruptible", .uninterruptible u)
  , ("interruptible", .interruptible u), ("yieldNow", .yieldNow 0)
  , ("awaitFiber", .awaitFiber t .joinEffect), ("withFiber", .withFiber .getId)
  , ("scoped", .scoped u), ("acquireRelease", .acquireRelease u u)
  , ("provideLayer", .provideLayer (.effectDiscard u) false u)
  , ("service", .service ⟨⟨0⟩, ⟨0⟩⟩), ("provideService", .provideService ⟨⟨0⟩, ⟨0⟩⟩ t u)
  , ("catchIf", .catchIf t u u), ("select", .select t .bool u u)
  , ("iterate", .iterate none t t t t u), ("restore", .restore t u)
  , ("defs", .defs [] .nil u), ("invoke", .invoke 0 t .nil) ]

-- every constructor has a sample, and nothing else does
#guard samples.map Prod.fst = Effect4.Program.ctorNames .eff

/-- The names a fragment admits at the head. -/
def admitted (fragment : NativeEff → Bool) : List String :=
  (samples.filter fun s => fragment s.2).map Prod.fst

-- `run_eq_meaning`'s fragment
#guard admitted Straight =
  ["succeed", "fail", "failCause", "sync", "suspend", "perform", "bind", "catchCause",
   "matchCause", "onExit", "exit", "select"]

-- the loop agreement's fragment: `Straight`, and the loop
#guard admitted Looped =
  ["succeed", "fail", "failCause", "sync", "suspend", "perform", "bind", "catchCause",
   "matchCause", "onExit", "exit", "select", "iterate"]

-- Forms outside the loop agreement fragment. A
-- restore site is outside both fragments, as the two masks are: the straight meaning has no
-- fiber flag (decisions rows 244 to 246; `Test/Program/MaskContract.lean` runs it)
#guard (samples.filter fun s => !Looped s.2).map Prod.fst =
  ["gen", "uninterruptible", "interruptible", "yieldNow", "awaitFiber", "withFiber", "scoped",
   "acquireRelease", "provideLayer", "service", "provideService", "catchIf", "restore", "defs",
   "invoke"]

-- Row-aware classification adds conditional handlers, without adding loops.
#guard admitted (StraightRows []) =
  ["succeed", "fail", "failCause", "sync", "suspend", "perform", "bind", "catchCause",
   "matchCause", "onExit", "exit", "catchIf", "select"]

-- H8's machine half: the loop and `catchIf` together, and a call of any host row
#guard admitted LoopedRows =
  ["succeed", "fail", "failCause", "sync", "suspend", "perform", "bind", "catchCause",
   "matchCause", "onExit", "exit", "catchIf", "select", "iterate"]

private def data : Row := (Authoring.Row.host "data" .unit .nat .never "fragment control").row
private def handle : Row := (Authoring.Row.host "handle" .unit NativeOp.kvTy .never "fragment control").row

#guard StraightRows [data] (.perform (.external 0) t)
#guard !StraightRows [handle] (.perform (.external 0) t)
#guard !StraightRows [data] (.perform (.external 1) t)
#guard !Straight (.perform (.external 0) t)
#guard !Looped (.perform (.external 0) t)
#guard LoopedRows (.perform (.external 7) t)
#guard !StraightRows [data] (.perform .deferredAwait t)
#guard !StraightRows [data] (.perform (.call 0) t)

/-- Put a rejected child in every visited position, including handler and finalizer positions. -/
private def rejectedChildren : List NativeEff :=
  let no : NativeEff := .yieldNow 0
  [.suspend no, .exit no,
   .bind no u, .bind u no,
   .select t .bool no u, .select t .bool u no,
   .catchCause no u, .catchCause u no,
   .matchCause no u u, .matchCause u no u, .matchCause u u no,
   .onExit no u, .onExit u no]

#guard rejectedChildren.all (fun e =>
  !Straight e && !Looped e && !StraightRows [data] e && !LoopedRows e)
#guard !Looped (.iterate none t t t t (.yieldNow 0))
#guard !LoopedRows (.iterate none t t t t (.yieldNow 0))
#guard !LoopedRows (.catchIf t u (.yieldNow 0))
#guard !StraightRows [data] (.catchIf t (.yieldNow 0) u)
#guard !StraightRows [data] (.catchIf t u (.yieldNow 0))

-- Readers: the generated predicate connects to the existing algebra at concrete programs.
example : Straight (.onExit u u) = cata_eff Straight.alg (.onExit u u) := Straight.eq_cata _
example : Looped (.iterate none t t t t u) = cata_eff Looped.alg (.iterate none t t t t u) :=
  Looped.eq_cata _
example : StraightRows [data] (.perform (.external 0) t) =
    cata_eff (StraightRows.alg [data]) (.perform (.external 0) t) := StraightRows.eq_cata _ _

end Test.Program.FragmentCensusContract
