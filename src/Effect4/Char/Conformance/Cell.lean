import Effect4.Char.Derived
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
modules, and the recipe is in `docs/research/2026-09-05-workshop-char/10-conformance/06-three-function-surface.md`.

Every `theorem` here is `by decide` over the machine alone (no hashing); every
`#guard` that mentions an address evaluates in the interpreter, where a node
address costs one pass over the genesis (`Store/Node.lean`, `specFor`).

This module sits **below** `Char/Derived.lean`: it needs `Content Target`
and `Content Implementation` to address its own target, and those are derived
there. Its alphabet `Label` is therefore the one monomorphic carrier of the room
whose instance cannot be generated — the generated file would have to import this
module to see it, and this module imports the generated file — so `Label`'s
instance is hand, written exactly as `Effect4Gen` writes a sum with one argument
per case (`Store/PinDerived.lean:26-68`, `Program/Derived.lean:29-67`).
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

end Effect4.Char.Cell

/-! ## `Canonical Label`, in the generator's shape -/

namespace Effect4.Store

namespace CharCellLabelC

def shapeDoc : ShapeDoc :=
  ⟨.sum "Label"
     [("put", [("item", (shape _root_.Nat).root)]),
      ("take", [("item", (shape _root_.Nat).root)]),
      ("clear", [])],
   (shape _root_.Nat).defs⟩

def toVal : _root_.Effect4.Char.Cell.Label → Val
  | .put a0 => .ctor 0 [Canonical.toVal a0]
  | .take a0 => .ctor 1 [Canonical.toVal a0]
  | .clear => .ctor 2 []

def ofVal : Val → Option (_root_.Effect4.Char.Cell.Label)
  | .ctor 0 [v0] => (Canonical.ofVal (α := _root_.Nat) v0).map .put
  | .ctor 1 [v0] => (Canonical.ofVal (α := _root_.Nat) v0).map .take
  | .ctor 2 [] => some .clear
  | _ => none

set_option linter.unusedSimpArgs false in
theorem ofVal_toVal (a : _root_.Effect4.Char.Cell.Label) : ofVal (toVal a) = some a := by
  cases a <;> simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.Cell.Label} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | (rename_i w
       obtain ⟨x, hx, hj⟩ := Option.map_eq_some_iff.mp h
       subst hj
       simp only [toVal]
       rw [Canonical.ofVal_exact hx])
    | exact nomatch h

theorem lift_Nat (x : _root_.Nat) :
    acceptsIn shapeDoc.defs (shape _root_.Nat).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => hp) _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.Cell.Label) : shapeDoc.accepts (toVal a) = true := by
  cases a with
  | «put» a0 =>
    exact accepts_sum _ _ _ 0 "put" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_Nat a0) (acceptsFields_nil _))
  | «take» a0 =>
    exact accepts_sum _ _ _ 1 "take" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_Nat a0) (acceptsFields_nil _))
  | «clear» =>
    exact accepts_sum _ _ _ 2 "clear" [] [] rfl (acceptsFields_nil _)

instance instCanonical : Canonical (_root_.Effect4.Char.Cell.Label) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end CharCellLabelC

end Effect4.Store

namespace Effect4.Char.Cell

open Effect4.Store
open Effect4.Char

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

/-- The cell's implementation pin set. Its `pins` are stand-in span digests: the cell has no
pinned source, so they are payload digests of two strings, as the old `digestOf "cell-pin"`
was. -/
def impl : Implementation :=
  { package := "effect", version := "4.0.0-rc.112", pins := [Canonical.digest "cell-pin"],
    driver := "runSync", host := "absent" }

/-- The cell has no manifest node, so `model` is a stand-in reference over the payload digest
of a string — exactly what the old `digestOf "cell-model"` was, now typed as what it points
at. `implementation` is a real address: `impl` is a value this module holds. -/
def target : Target :=
  { component := "cell"
    model := ⟨Canonical.digest "cell-model"⟩
    implementation := address impl
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
#guard characterized.vectors.kind = .vector
#guard (vs.toFixture target).traces.length = 60
#guard (vs.toFixture target).schema = 3
#guard (vs.toFixture target).producer = "Effect4.Char"

/-! ### The kinds, as landed -/

#guard Content.kind Manifest = .component
#guard Content.kind Implementation = .source

/-! ## `Evidence` as content: the laws, run (moved here from `Char/Evidence.lean` at the landing,
because the instance is generated into `Char/Derived.lean`, which this module imports) -/

private def samplePin : Evidence := .pin ⟨zeroDigest⟩ "guard-name"

private def sampleFixture : Evidence := .fixture ⟨.vector, zeroDigest⟩ ⟨zeroDigest⟩

private def sampleThm : Evidence := .thm "t" "[propext]" zeroDigest

#guard Canonical.decode (α := Evidence) (Canonical.encode samplePin) = some samplePin
#guard Canonical.decode (α := Evidence) (Canonical.encode sampleFixture) = some sampleFixture
#guard Canonical.decode (α := Evidence) (Canonical.encode sampleThm) = some sampleThm
#guard Canonical.decode (α := Evidence) (Canonical.encode (Evidence.assumed "p")) =
  some (Evidence.assumed "p")
#guard Canonical.decode (α := Evidence) (Canonical.encode sampleThm ++ [0]) = none
#guard Canonical.decode (α := Evidence) (Canonical.encode sampleFixture).dropLast = none
#guard (Canonical.shape Evidence).accepts (Canonical.toVal samplePin)
#guard Content.kind Evidence = .annotation
#guard samplePin.rung = some .pinned
#guard sampleFixture.rung = some .replayed
#guard sampleThm.rung = some .proved
#guard [Content.kind Receipt, Content.kind Claim, Content.kind Evidence, Content.kind Target,
    Content.kind Characterized].all fun k => k = .annotation
#guard [Content.kind (VectorSet Label Unit), Content.kind (Vector Label Unit),
    Content.kind (Fact Label Unit)].all fun k => k = .vector

/-! ## Receipts -/

#print axioms cell
#print axioms reading
#print axioms dupMachine
#print axioms lossyMachine
#print axioms dup
#print axioms lossy
#print axioms alpha
#print axioms suite
#print axioms impl
#print axioms target
#print axioms vs
#print axioms suite_passes
#print axioms dup_killed
#print axioms dup_survives_some
#print axioms lossy_killed
#print axioms lossy_survives_some
#print axioms enumeration_kills_dup
#print axioms refusals_kill_lossy
#print axioms enumeration_alone_spares_lossy
#print axioms wordsUpTo_sizes
#print axioms complete_example
#print axioms selfReceipts
#print axioms dupReceipts
#print axioms vsProd
#print axioms characterized
#print axioms Effect4.Store.CharCellLabelC.toVal
#print axioms Effect4.Store.CharCellLabelC.ofVal
#print axioms Effect4.Store.CharCellLabelC.ofVal_toVal
#print axioms Effect4.Store.CharCellLabelC.ofVal_exact
#print axioms Effect4.Store.CharCellLabelC.fits
#print axioms Effect4.Store.CharCellLabelC.instCanonical

end Effect4.Char.Cell
