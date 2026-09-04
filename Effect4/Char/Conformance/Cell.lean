import Effect4.Char.Conformance.Surface
import Effect4.Char.Conformance.Compose

/-!
# Conformance.Cell: the worked instance and the anti-vacuity kit

Owner: the one-slot cell, a two-state machine with three verbs, run through the
whole substrate so that every law in the other modules has a witness that it is
not vacuous. `put` accepts an item into the empty slot, `take` hands the held
item out (the answer is in the label), `clear` drops it (a failure label). Two
mutants: one keeps the item after `take` (a duplicate delivery), one lets `put`
overwrite (a loss). The enumeration kills both without a single authored test.

This module declares no component of the Effect runtime and is never imported
by one; it is the substrate's own test. The Queue is instantiated by lane A's
modules, and the recipe is in `workshop/Char/10-conformance/06-three-function-surface.md`.

Every `theorem` here is `by decide` over the machine alone (no hashing); every
`#guard` that mentions a digest evaluates in the interpreter.
-/

set_option autoImplicit false

namespace Effect4.Char.Cell

open Effect4.Store
open Effect4.Char

/-- The alphabet. -/
inductive Label where
  | put (item : Nat)
  | take (item : Nat)
  | clear
deriving DecidableEq, Repr, Inhabited

instance : Canonical Label := ⟨fun l =>
  match l with
  | .put i => encode ((0 : Nat), i)
  | .take i => encode ((1 : Nat), i)
  | .clear => encode ((2 : Nat), (0 : Nat))⟩

/-- The state: the slot. -/
abbrev State := Option Nat

/-- The model. -/
def cell : Machine State Label where
  init := none
  step := fun s l =>
    match s, l with
    | none, .put i => some (some i)
    | some i, .take j => if i = j then some none else none
    | some _, .clear => some none
    | _, _ => none

/-- The reading: one client, the slot is the residue. -/
def reading : Reading State Label Unit where
  accepts := fun l => match l with | .put i => some ((), i) | _ => none
  emits := fun l => match l with | .take i => [((), i)] | _ => []
  residue := fun s _ => s.toList

/-- Mutant: `take` delivers and keeps the item. Attacks single delivery. -/
def dupMachine : Machine State Label where
  init := none
  step := fun s l =>
    match s, l with
    | none, .put i => some (some i)
    | some i, .take j => if i = j then some (some i) else none
    | some _, .clear => some none
    | _, _ => none

/-- Mutant: `put` on a full slot overwrites. Attacks no-loss. -/
def lossyMachine : Machine State Label where
  init := none
  step := fun s l =>
    match s, l with
    | _, .put i => some (some i)
    | some i, .take j => if i = j then some none else none
    | some _, .clear => some none
    | _, _ => none

def dup : Mutant State Label :=
  ⟨"CELL-M1", "CELL-single", "take hands the item out exactly once", dupMachine⟩

def lossy : Mutant State Label :=
  ⟨"CELL-M2", "CELL-noLoss", "put on a full slot is refused, never an overwrite", lossyMachine⟩

/-- The finite alphabet to enumerate over. -/
def alpha : List Label := [.put 1, .put 2, .take 1, .take 2, .clear]

/-- Four authored tests. The fourth exists because the first three did not
separate `lossy`: an overwrite is only visible when a full slot is offered a
second item, and no positive test does that. The enumeration found it first. -/
def suite : Suite Label Unit :=
  [ { name := "put-take", labels := [.put 1, .take 1], residue := [((), [])] }
  , { name := "put-holds", labels := [.put 2], residue := [((), [2])] }
  , { name := "take-empty-refused", labels := [.take 1], accept := false }
  , { name := "put-full-refused", labels := [.put 1, .put 2], accept := false } ]

def target : Target :=
  { component := "cell"
    model := digestOf "cell-model"
    implementation :=
      { package := "effect", version := "4.0.0-rc.112", pins := [digestOf "cell-pin"],
        driver := "runSync", host := "absent" }
    failure := { name := "F-none", excluded := ["clear"], escapes := [] } }

/-- The whole characterization at depth 3. -/
def vs : VectorSet Label Unit := characterize cell reading [()] alpha suite [dup, lossy] 3

/-! ### The suite and the mutants, as Core reads them -/

theorem suite_passes : Suite.run cell reading suite = true := by decide
theorem dup_killed : Mutant.killed reading suite dup = true := by decide
theorem dup_survives_some : Mutant.survivesSome reading suite dup = true := by decide
theorem lossy_killed : Mutant.killed reading suite lossy = true := by decide
theorem lossy_survives_some : Mutant.survivesSome reading suite lossy = true := by decide

/-! ### The enumeration alone, with no authored test, kills both mutants -/

theorem enumeration_kills_dup :
    VectorSet.kills dupMachine reading [()] (enumerate cell reading [()] alpha 2) = true := by
  decide

theorem refusals_kill_lossy :
    VectorSet.kills lossyMachine reading [()] (enumerateRefused cell reading [()] alpha 1) = true := by
  decide

/-- The accepted enumeration alone does not kill the lossy mutant: the refusals
are what separate a machine that accepts too much. The anti-vacuity witness
that `enumerate` and `enumerateRefused` are different sets with different power. -/
theorem enumeration_alone_spares_lossy :
    VectorSet.kills lossyMachine reading [()] (enumerate cell reading [()] alpha 3) = false := by
  decide

/-- The enumeration budget, decided by the kernel: accepted words up to each depth. -/
theorem wordsUpTo_sizes :
    (List.range 6).map (fun k => (wordsUpTo cell alpha k).length) = [1, 3, 7, 15, 31, 63] := by
  decide

/-- Completeness, on the instance: `[put 1, take 1, put 2]` is accepted, over the
alphabet, of length 3, so it is enumerated at depth 3. -/
theorem complete_example :
    [Label.put 1, .take 1, .put 2] ∈ wordsUpTo cell alpha 3 :=
  mem_wordsUpTo_of_accepts cell alpha 3 _ (by decide) (by decide) (by decide)

/-! ### Receipts over the whole characterization -/

#guard VectorSet.soundB cell reading [()] vs
#guard vs.factCount = 60
#guard VectorSet.kills dupMachine reading [()] vs
#guard VectorSet.kills lossyMachine reading [()] vs
#guard GSet.nodupL vs.elems

-- Extension: depth 4 holds everything depth 3 held; a self-join adds nothing.
#guard GSet.subB vs (extend vs (characterize cell reading [()] alpha suite [dup, lossy] 4))
#guard (extend vs vs).size = vs.size

-- A doctest whose ratified expectation the model reproduces is silent; one it
-- does not reproduce is a finding row, and its vector is still the model's fact.
#guard (doctestFindings cell reading [()]
  [{ span := "cell.ts:1-3", word := [.put 1, .take 1], expectAccept := true,
     expectReadings := [⟨(), [1], [1], []⟩], ratifiedBy := "owner" }]) = []
#guard (doctestFindings cell reading [()]
  [{ span := "cell.ts:4-6", word := [.put 1, .take 1], expectAccept := true,
     expectReadings := [⟨(), [1], [1], [1]⟩], ratifiedBy := "owner" }]) = ["cell.ts:4-6"]
#guard VectorSet.soundB cell reading [()] (fromDoctests cell reading [()]
  [{ span := "cell.ts:4-6", word := [.put 1, .take 1], expectAccept := true,
     expectReadings := [⟨(), [1], [1], [1]⟩], ratifiedBy := "owner" }])

/-- Self-replay: every receipt holds, and consuming again adds nothing. -/
def selfReceipts : Receipts := consume target (replayAgainst cell reading [()]) GSet.empty vs
#guard selfReceipts.verdict
#guard selfReceipts.size = 60
#guard (consume target (replayAgainst cell reading [()]) selfReceipts vs).size = 60

/-- Replay against the duplicate mutant as if it were the implementation: the
verdict is `false`, the failures are exactly the ten separating vectors, and none
of them is evidence. -/
def dupReceipts : Receipts := consume target (replayAgainst dupMachine reading [()]) GSet.empty vs
#guard dupReceipts.verdict = false
#guard dupReceipts.failures.length = 10
#guard (dupReceipts.failures.map Receipt.asFixtureEvidence).all Option.isNone
#guard (selfReceipts.elems.map Receipt.asFixtureEvidence).all Option.isSome

/-! ### Composition: the cell beside a second cell -/

/-- The cell's set, injected into the cell-times-cell product: every fact lifts. -/
def vsProd : VectorSet (Label ⊕ Label) (Unit ⊕ Unit) := injectL vs
#guard vsProd.factCount = 60
#guard VectorSet.soundB (cell.prod cell) (reading.prod reading) [Sum.inl ()] vsProd

/-! ### Phase 1, as a record -/

def characterized : Characterized :=
  Characterized.ofParts target vs selfReceipts
    [⟨"CELL-single", some .replayed⟩, ⟨"CELL-noLoss", some .replayed⟩]

#guard characterized.component = "cell"
#guard characterized.claims.map (·.rung.spelling) = ["replayed", "replayed"]
#guard (vs.toFixture target).traces.length = 60
#guard (vs.toFixture target).schema = 3
#guard (vs.toFixture target).producer = "Effect4.Char"

end Effect4.Char.Cell
