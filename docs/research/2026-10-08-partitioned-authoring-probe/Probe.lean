import docs.research.«2026-10-08-partitioned-authoring-probe».Model
import Effect4.Laws.Author

/-!
Research prototype; no library import reaches this file.
Placement precedes obligations in README.md beside this file.
Value equations serve proposed partitioned-semaphore-bookkeeping, translation-simulation, R10.
Their actual consumers are the source reading laws below.
Typing laws serve step-language-typed, store-typing, R4, at these four concrete Steps.
No theorem claims registration, identity validity, wrapper execution, scheduling, or host agreement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Research.PartitionedAuthoring
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules


open Model (Counts)
/-- Read the field signature from the generated schema; do not restate its order. -/
abbrev fields := match Counts.modeledTy with | .record fs => fs | _ => []
abbrev countsTy := Counts.modeledTy

def capacityF : FieldRef fields .nat := field_ref% "capacity"
def availableF : FieldRef fields .nat := field_ref% "available"
def waitingF : FieldRef fields .nat := field_ref% "waiting"

namespace Data
step_context% InitialInputs (capacity : .nat)
step_context% CellInputs (cell : countsTy)
step_context% RequestInputs (requested : .nat, cell : countsTy)

/-- Supply construction fields by name against the generated schema. -/
def initial : Step InitialInputs.types countsTy := step_inputs% InitialInputs =>
  record_step% { waiting := .nat 0, capacity := capacity, available := capacity }

def available : Step CellInputs.types .nat := step_inputs% CellInputs => .get cell availableF

def tryTake : Step RequestInputs.types (.prod .bool countsTy) := step_inputs% RequestInputs =>
  .ite (.isZero requested) (.pair (.bool true) cell)
    (.ite (.or (.lt (.get cell capacityF) requested) (.lt (.get cell availableF) requested))
      (.pair (.bool false) cell)
      (.pair (.bool true) (.set cell availableF (.sub (.get cell availableF) requested))))

def reserve : Step RequestInputs.types (.prod .nat countsTy) := step_inputs% RequestInputs =>
  let needed := Step.sub requested (.get cell availableF)
  .pair needed (.set (.set cell availableF (.nat 0)) waitingF (.add (.get cell waitingF) needed))
end Data

/-- Use the deriving command's connector, rather than author a carrier tuple. -/
abbrev encoded (s : Counts) := Counts.modeledToC s
abbrev requests (s : Counts) (n : Nat) : Inputs Leaves.refused Data.RequestInputs.types :=
  (n, (encoded s, ()))

def initialStep (capacity : TermSrc) := Data.initial.term (input_sources% (Data.InitialInputs) {capacity := capacity})
def availableStep (cell : TermSrc) := Data.available.term (input_sources% (Data.CellInputs) {cell := cell})
def tryTakeStep (requested cell : TermSrc) := Data.tryTake.term
  (input_sources% (Data.RequestInputs) {cell := cell, requested := requested})
def reserveStep (requested cell : TermSrc) := Data.reserve.term
  (input_sources% (Data.RequestInputs) {requested := requested, cell := cell})

/-- Helper of partitioned-semaphore-bookkeeping; initial_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initial_eval (capacity : Nat) :
    Data.initial.eval (Γ := Data.InitialInputs.types) Leaves.refused (capacity, ()) = encoded (Model.initial capacity) := rfl

/-- Helper of partitioned-semaphore-bookkeeping; available_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem available_eval (s : Counts) :
    Data.available.eval (Γ := Data.CellInputs.types) Leaves.refused (encoded s, ()) = Model.available s := rfl

/-- Helper of partitioned-semaphore-bookkeeping; tryTake_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem tryTake_eval (s : Counts) (n : Nat) :
    Data.tryTake.eval Leaves.refused (requests s n) =
      ((Model.tryTake s n).1, encoded (Model.tryTake s n).2) := by
  cases s with
  | mk capacity available waiting =>
    cases n with
    | zero => rfl
    | succ n =>
      change (if decide (capacity < n + 1) || decide (available < n + 1) then
        (false, encoded ⟨capacity, available, waiting⟩)
        else (true, encoded ⟨capacity, available - (n + 1), waiting⟩)) = _
      unfold Model.tryTake
      split <;> rfl

/-- Helper of partitioned-semaphore-bookkeeping; reserve_reads consumes this conditional equation.
The branch premise remains explicit, although the scalar arithmetic equation needs no premise. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem reserve_eval (s : Counts) (n : Nat) (_insufficient : s.available < n)
    (_capacity : n ≤ s.capacity) :
    Data.reserve.eval Leaves.refused (requests s n) =
      ((Model.reserve s n).1, encoded (Model.reserve s n).2) := rfl

section Reading
variable {env : Env} {path : List Nat} {vals : List Effect4.Store.Val}

/-- The construction source reads the independent model's derived image. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initial_reads (capacity : Nat) {source : TermSrc}
    (h : Reads source env path vals (.nat capacity)) :
    Reads (initialStep source) env path vals ((Modeled.image Counts).toVal (Model.initial capacity)) := by
  have reading := Step.sound (Γ := Data.InitialInputs.types) Leaves.refused (capacity, ()) (Input.reads_cons h Input.reads_nil) Data.initial rfl
  rw [initial_eval] at reading
  exact reading

/-- The availability source reads the model's scalar reply. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem available_reads (s : Counts) {source : TermSrc}
    (h : Reads source env path vals ((Modeled.image Counts).toVal s)) :
    Reads (availableStep source) env path vals (.nat (Model.available s)) := by
  have reading := Step.sound (Γ := Data.CellInputs.types) Leaves.refused (encoded s, ()) (Input.reads_cons h Input.reads_nil) Data.available rfl
  rw [available_eval] at reading
  exact reading

/-- The attempted take reads the model's reply and final scalar record. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem tryTake_reads (s : Counts) (n : Nat) {amount source : TermSrc}
    (hn : Reads amount env path vals (.nat n))
    (hs : Reads source env path vals ((Modeled.image Counts).toVal s)) :
    Reads (tryTakeStep amount source) env path vals
      ((Effect4.Store.Image.tuple2 Effect4.Store.Image.bool (Modeled.image Counts)).toVal (Model.tryTake s n)) := by
  have reading := Step.sound Leaves.refused (requests s n)
    (Input.reads_cons hn (Input.reads_cons hs Input.reads_nil)) Data.tryTake rfl
  rw [tryTake_eval] at reading
  exact reading

/-- Only the source's waiting branch consumes this reservation connector. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem reserve_reads (s : Counts) (n : Nat) {amount source : TermSrc}
    (hn : Reads amount env path vals (.nat n))
    (hs : Reads source env path vals ((Modeled.image Counts).toVal s))
    (insufficient : s.available < n) (capacity : n ≤ s.capacity) :
    Reads (reserveStep amount source) env path vals
      ((Effect4.Store.Image.tuple2 Effect4.Store.Image.nat (Modeled.image Counts)).toVal (Model.reserve s n)) := by
  have reading := Step.sound Leaves.refused (requests s n)
    (Input.reads_cons hn (Input.reads_cons hs Input.reads_nil)) Data.reserve rfl
  rw [reserve_eval s n insufficient capacity] at reading
  exact reading
end Reading

section Typing
variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
  {env : Env} {path : List Nat} {types : List Ty}
include atoms
/-- Consumer of step-language-typed, R4, at this construction. -/
@[semantics "store-typing" (requirement := R4)]
theorem initial_types {source : TermSrc} (h : TypesEach sig source env path types .nat) :
    TypesEach sig (initialStep source) env path types countsTy :=
  Step.typed_of_normal sig atoms (Input.types_cons h Input.types_nil) Data.initial rfl

/-- Consumer of step-language-typed, R4, at this scalar read. -/
@[semantics "store-typing" (requirement := R4)]
theorem available_types {source : TermSrc} (h : TypesEach sig source env path types countsTy) :
    TypesEach sig (availableStep source) env path types .nat :=
  Step.typed_of_normal sig atoms (Input.types_cons h Input.types_nil) Data.available rfl

/-- Consumer of step-language-typed, R4, at this attempted take. -/
@[semantics "store-typing" (requirement := R4)]
theorem tryTake_types {amount source : TermSrc} (hn : TypesEach sig amount env path types .nat)
    (hs : TypesEach sig source env path types countsTy) :
    TypesEach sig (tryTakeStep amount source) env path types (.prod .bool countsTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons hn (Input.types_cons hs Input.types_nil)) Data.tryTake rfl

/-- Consumer of step-language-typed, R4, at this branch arithmetic. -/
@[semantics "store-typing" (requirement := R4)]
theorem reserve_types {amount source : TermSrc} (hn : TypesEach sig amount env path types .nat)
    (hs : TypesEach sig source env path types countsTy) :
    TypesEach sig (reserveStep amount source) env path types (.prod .nat countsTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons hn (Input.types_cons hs Input.types_nil)) Data.reserve rfl
end Typing

-- Reader: the deriving command supplies both inverses at the actual record.
example (s : Counts) : Counts.modeledOfC (encoded s) = s := Counts.modeled_of_to s
example (c : Carrier countsTy) : encoded (Counts.modeledOfC c) = c := Counts.modeled_to_of c

-- Reader: compose the actual generated construction and take source laws at one real input.
example (env : Env) (path : List Nat) (vals : List Effect4.Store.Val) :
    Reads (tryTakeStep (nat 3) (initialStep (nat 5))) env path vals
      ((Effect4.Store.Image.tuple2 Effect4.Store.Image.bool (Modeled.image Counts)).toVal
        (Model.tryTake (Model.initial 5) 3)) :=
  tryTake_reads (Model.initial 5) 3 (reads_nat 3 env path vals)
    (initial_reads 5 (reads_nat 5 env path vals))

-- Decode only for the probe's finite controls; stored Steps retain typed first-order data.
def initialValue (capacity : Nat) : Counts :=
  Counts.modeledOfC (Data.initial.eval (Γ := Data.InitialInputs.types) Leaves.refused (capacity, ()))
def takeValue (s : Counts) (n : Nat) : Bool × Counts :=
  let value := Data.tryTake.eval Leaves.refused (requests s n)
  (value.1, Counts.modeledOfC value.2)
def reserveValue (s : Counts) (n : Nat) : Nat × Counts :=
  let value := Data.reserve.eval Leaves.refused (requests s n)
  (value.1, Counts.modeledOfC value.2)

-- Finite positive controls compare saved Steps with independently computed records.
#guard initialValue 5 == Model.initial 5
#guard takeValue ⟨5, 4, 2⟩ 3 == (true, ⟨5, 1, 2⟩)
#guard reserveValue ⟨5, 2, 3⟩ 4 == (2, ⟨5, 0, 5⟩)
-- Control: omitted capacity checking falsely accepts this malformed state.
#guard (takeValue ⟨2, 5, 0⟩ 3).1 == false
-- Control: reservation records only the unmet amount, not the whole request.
#guard (reserveValue ⟨5, 2, 3⟩ 4).2 != (⟨5, 0, 7⟩ : Counts)
-- Control: applying branch arithmetic outside its branch changes a state that should take immediately.
#guard (reserveValue ⟨5, 4, 0⟩ 2).2 != (Model.tryTake ⟨5, 4, 0⟩ 2).2

-- Control: field typing rejects a Boolean in the available counter.
/--
error: Application type mismatch: The argument
  Step.bool true
has type
  Step ?m.6 Ty.bool
but is expected to have type
  Step [countsTy] Ty.nat
in the application
  cell.set availableF (Step.bool true)
-/
#guard_msgs (error) in
example : Step Data.CellInputs.types countsTy := step_inputs% Data.CellInputs =>
  .set cell availableF (.bool true)

end Research.PartitionedAuthoring
