import Effect4.Laws.Program.DenoteB

/-!
# Fragment census — which constructors each proved fragment admits

`Straight` (the fragment `run_eq_meaning` covers) and `Looped` (the fragment the loop agreement
covers) are defined by matches with a default arm, so a new constructor falls outside both
without anyone deciding so. This battery makes that decision loud. It holds one sample per
constructor of `Eff`, guarded against the alphabet's own name list (`Effect4.Program.constructorNames`), and
pins the names each fragment admits at the head. Adding a constructor turns the first guard red
until it has a sample; the sample then lands in or out of each list, and the author says which.

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
  , ("iterate", .iterate none t t t t u) ]

-- every constructor has a sample, and nothing else does
#guard samples.map Prod.fst = Effect4.Program.constructorNames

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

-- the twelve constructors with no proved agreement between the machine and the meaning
#guard (samples.filter fun s => !Looped s.2).map Prod.fst =
  ["gen", "uninterruptible", "interruptible", "yieldNow", "awaitFiber", "withFiber", "scoped",
   "acquireRelease", "provideLayer", "service", "provideService", "catchIf"]

end Test.Program.FragmentCensusContract
