import Effect4.Target.TypeScript.StructuredLower
import Effect4.Semantics.Denotation

/-!
# Target.TypeScript.SkeletonSemantics

Owner: the denotation of the control skeleton, and the agreement of the two
lowered forms with the flow denotation (plan packet D3 of
`docs/research/2026-09-03-reification-plan.md`).
-/

set_option autoImplicit false

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

namespace Skel

/-! ## 1. The machine -/

/-- The state a skeleton runs in. -/
structure Machine where
  /-- The value of every slot. -/
  vals : Slot → Val
  /-- The value of every dispatch index variable. -/
  index : String → Nat
  /-- The block whose body is being run, set by `enterBlock`. -/
  block : BlockId

namespace Machine

def setVal (m : Machine) (slot : Slot) (value : Val) : Machine :=
  { m with vals := fun s => if s = slot then value else m.vals s }

def setIndex (m : Machine) (var : String) (value : Nat) : Machine :=
  { m with index := fun v => if v = var then value else m.index v }

def enter (m : Machine) (block : BlockId) : Machine := { m with block := block }

end Machine

/-- How a statement list finished. -/
inductive Outcome where
  | fell (m : Machine)
  | continueLoop (m : Machine)
  | continueLabel (label : String) (m : Machine)
  | breakLabel (label : String) (m : Machine)
  | finished (result : RunResult)

/-! ## 2. The simple nodes -/

/-- The nodes that only move values: no effect, no control, no failure. -/
def simple? (m : Machine) : Skeleton → Option Machine
  | .acquireService _ => some m
  | .declare _ _ => some m
  | .assign target source => some (m.setVal target (m.vals source))
  | .letTemp index source => some (m.setVal (.temp index) (m.vals source))
  | .letBlockIndex var target => some (m.setIndex var target.value)
  | .enterBlock block => some (m.enter block)
  | _ => none

/-- Fold a run of simple nodes. -/
def runSimple (m : Machine) : List Skeleton → Option Machine
  | [] => some m
  | node :: rest => (simple? m node).bind fun m' => runSimple m' rest

/-- The body of a dispatch case. -/
def caseBody? : List (Nat × List Skeleton) → Nat → Option (List Skeleton)
  | [], _ => none
  | (index, body) :: rest, wanted => if index = wanted then some body else caseBody? rest wanted

/-! ## 3. The measure -/

mutual

/-- A structural measure with every leaf at `1`; used only for termination. -/
def size : Skeleton → Nat
  | .dispatchLoop _ cases => sizeCases cases + 2
  | .loop _ body => sizeList body + 2
  | .labelled _ body => sizeList body + 2
  | .decide _ _ onTrue onFalse => sizeList onTrue + sizeList onFalse + 2
  | .enterScoped _ body => sizeList body + 2
  | _ => 2
  termination_by structural node => node

def sizeList : List Skeleton → Nat
  | [] => 0
  | node :: rest => size node + sizeList rest
  termination_by structural nodes => nodes

def sizeCases : List (Nat × List Skeleton) → Nat
  | [] => 0
  | (_, body) :: rest => sizeList body + sizeCases rest
  termination_by structural cases => cases

end

theorem two_le_size (node : Skeleton) : 2 ≤ size node := by
  cases node <;> simp [size]


/-! ## 4. The denotation

`⟦·⟧` of the plan. A skeleton runs in the machine of §1 and performs exactly
the operations `Effect4.Flow.denoteFuel` performs: the left summand for a
family operation, a pure atom *and a literal* alike — `plan` does not read the
target table, so all three block terminators are the same `perform` of the
algebra and the difference between them is a spelling (`render`) and a tracing
policy (`FlowService.pure`), never a different program — and the right summand
for a decision, whose branch the tape fixes before the operation is performed.

Fuel counts loop iterations only: one `dispatchLoop` iteration is one block,
so the fuel of `dispatchRun` is the fuel of `denoteFuel`, unit for unit
(§6, T3). Statement lists are structural, so nothing inside a block body
spends any.

The three region nodes (`enterScoped`, `acquire`, `leave`) have no denotation
here: regions are a scope summand of `FullSig` that packet D2 owns and this
module does not import. They stop the machine at a `stuck` frontier of the
block last entered, which is what `enterBlock` is carried for.
-/

variable {Ty : Type} (alphabet : FlowAlphabet Ty)

mutual

/-- Run a statement list to its first control transfer. -/
def execList (fuel : Nat) (m : Machine) (tape : Tape) :
    List Skeleton → Program (FullSig alphabet) (Outcome × Tape)
  | [] => .pure (.fell m, tape)
  | node :: rest =>
      match simple? m node with
      | some m' => execList fuel m' tape rest
      | none => execControl fuel m tape node rest
  termination_by nodes => (fuel, 2 * sizeList nodes + 1)
  decreasing_by
    · exact Prod.Lex.right _ (by have := two_le_size node; simp only [sizeList]; omega)
    · exact Prod.Lex.right _ (by simp only [sizeList]; omega)

/-- Run one node that is not a simple move, then the statements after it. -/
def execControl (fuel : Nat) (m : Machine) (tape : Tape) (node : Skeleton)
    (rest : List Skeleton) : Program (FullSig alphabet) (Outcome × Tape) :=
  match node with
  | .perform answer operation _ request =>
      performOp fuel m tape answer operation request rest
  | .atom answer operation _ request =>
      performOp fuel m tape answer operation request rest
  | .literal answer operation request _ =>
      performOp fuel m tape answer operation request rest
  | .decide answer site onTrue onFalse =>
      match tape.read site with
      | .exhausted => .pure (.finished (.frontier (.unansweredDecision site)), tape)
      | .mismatch expected actual => .pure (.finished (.refused expected actual), tape)
      | .answered branch more =>
          .vis (.inr (site, branch)) fun _ =>
            Program.bind
              (execList fuel (m.setVal answer (.bool branch)) more
                (if branch then onTrue else onFalse))
              (afterFell fuel rest)
  | .labelled label body =>
      Program.bind (execList fuel m tape body) (afterBlock fuel label rest)
  | .loop label body =>
      Program.bind (loopRun fuel m tape label body) (afterFell fuel rest)
  | .dispatchLoop var cases =>
      Program.bind (dispatchRun fuel m tape var cases)
        fun result => .pure (.finished result.1, result.2)
  | .breakTo label => .pure (.breakLabel label m, tape)
  | .continueTo label => .pure (.continueLabel label m, tape)
  | .gotoBlock var target => .pure (.continueLoop (m.setIndex var target.value), tape)
  | .ret value => .pure (.finished (.done (m.vals value)), tape)
  | _ => .pure (.finished (.frontier (.stuck m.block)), tape)
  termination_by (fuel, 2 * (size node + sizeList rest))
  decreasing_by
    all_goals
      refine Prod.Lex.right _ ?_
      simp only [size]
      first
        | omega
        | (split <;> omega)

/-- One operation of the flow alphabet: the same `Sig` operation `denoteFuel`
performs, whatever the target spelling of the node was. -/
def performOp (fuel : Nat) (m : Machine) (tape : Tape) (answer : Slot)
    (operation : OperationId) (request : Slot) (rest : List Skeleton) :
    Program (FullSig alphabet) (Outcome × Tape) :=
  match alphabet.lookup operation with
  | none => .pure (.finished (.frontier (.stuck m.block)), tape)
  | some op =>
      .vis (.inl ⟨op, m.vals request⟩) fun answered : Val =>
        execList fuel (m.setVal answer answered) tape rest
  termination_by (fuel, 2 * sizeList rest + 2)
  decreasing_by exact Prod.Lex.right _ (by omega)

/-- Continue with the statements after a construct that fell through. -/
def afterFell (fuel : Nat) (rest : List Skeleton) :
    Outcome × Tape → Program (FullSig alphabet) (Outcome × Tape)
  | (.fell m, tape) => execList fuel m tape rest
  | (outcome, tape) => .pure (outcome, tape)
  termination_by (fuel, 2 * sizeList rest + 2)
  decreasing_by exact Prod.Lex.right _ (by omega)

/-- Continue after a labelled block: its own `break` lands here. -/
def afterBlock (fuel : Nat) (label : String) (rest : List Skeleton) :
    Outcome × Tape → Program (FullSig alphabet) (Outcome × Tape)
  | (.fell m, tape) => execList fuel m tape rest
  | (.breakLabel found m, tape) =>
      if found = label then execList fuel m tape rest
      else .pure (.breakLabel found m, tape)
  | (outcome, tape) => .pure (outcome, tape)
  termination_by (fuel, 2 * sizeList rest + 2)
  decreasing_by
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.right _ (by omega)

/-- `label: while (true) { body }`. -/
def loopRun : Nat → Machine → Tape → String → List Skeleton →
    Program (FullSig alphabet) (Outcome × Tape)
  | 0, m, tape, _, _ => .pure (.finished (.frontier (.fuel m.block)), tape)
  | fuel + 1, m, tape, label, body =>
      Program.bind (execList fuel m tape body) (loopCatch fuel label body)
  termination_by fuel => (fuel, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)

/-- What one pass through a loop body does to the loop. -/
def loopCatch (fuel : Nat) (label : String) (body : List Skeleton) :
    Outcome × Tape → Program (FullSig alphabet) (Outcome × Tape)
  | (.fell m, tape) => loopRun fuel m tape label body
  | (.continueLoop m, tape) => loopRun fuel m tape label body
  | (.continueLabel found m, tape) =>
      if found = label then loopRun fuel m tape label body
      else .pure (.continueLabel found m, tape)
  | (.breakLabel found m, tape) =>
      if found = label then .pure (.fell m, tape) else .pure (.breakLabel found m, tape)
  | (.finished result, tape) => .pure (.finished result, tape)
  termination_by (fuel, 1)
  decreasing_by
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.right _ (by omega)

/-- `while (true) { switch (var) { ... } }`: one iteration is one block. -/
def dispatchRun : Nat → Machine → Tape → String → List (Nat × List Skeleton) →
    Program (FullSig alphabet) (RunResult × Tape)
  | 0, m, tape, var, _ => .pure (.frontier (.fuel ⟨m.index var⟩), tape)
  | fuel + 1, m, tape, var, cases =>
      match caseBody? cases (m.index var) with
      | none => .pure (.frontier (.stuck ⟨m.index var⟩), tape)
      | some body =>
          Program.bind (execList fuel m tape body) (dispatchCatch fuel var cases)
  termination_by fuel => (fuel, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)

/-- What one case body does to the dispatch loop. -/
def dispatchCatch (fuel : Nat) (var : String) (cases : List (Nat × List Skeleton)) :
    Outcome × Tape → Program (FullSig alphabet) (RunResult × Tape)
  | (.fell m, tape) => dispatchRun fuel m tape var cases
  | (.continueLoop m, tape) => dispatchRun fuel m tape var cases
  | (.continueLabel _ m, tape) => .pure (.frontier (.stuck m.block), tape)
  | (.breakLabel _ m, tape) => .pure (.frontier (.stuck m.block), tape)
  | (.finished result, tape) => .pure (result, tape)
  termination_by (fuel, 1)
  decreasing_by
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.right _ (by omega)

end

/-! ## 5. Unfolding -/

theorem execList_nil (fuel : Nat) (m : Machine) (tape : Tape) :
    execList alphabet fuel m tape [] = .pure (.fell m, tape) := by
  rw [execList]

theorem execList_cons (fuel : Nat) (m : Machine) (tape : Tape) (node : Skeleton)
    (rest : List Skeleton) :
    execList alphabet fuel m tape (node :: rest) =
      match simple? m node with
      | some m' => execList alphabet fuel m' tape rest
      | none => execControl alphabet fuel m tape node rest := by
  rw [execList]

theorem execList_cons_simple (fuel : Nat) (m m' : Machine) (tape : Tape) (node : Skeleton)
    (rest : List Skeleton) (moved : simple? m node = some m') :
    execList alphabet fuel m tape (node :: rest) = execList alphabet fuel m' tape rest := by
  rw [execList_cons, moved]

/-! ## 6. Runs of simple nodes -/

theorem runSimple_append : ∀ (pre : List Skeleton) (m m' : Machine),
    runSimple m pre = some m' → ∀ rest, runSimple m (pre ++ rest) = runSimple m' rest
  | [], m, m', folded, rest => by
      simp only [runSimple, Option.some.injEq] at folded
      subst folded; rfl
  | node :: pre, m, m', folded, rest => by
      simp only [runSimple] at folded
      cases moved : simple? m node with
      | none => rw [moved] at folded; exact absurd folded (by simp)
      | some m₁ =>
          rw [moved] at folded
          simp only [Option.bind_some] at folded
          rw [List.cons_append]
          simp only [runSimple, moved, Option.bind_some]
          exact runSimple_append pre m₁ m' folded rest

theorem execList_append_simple (fuel : Nat) (tape : Tape) : ∀ (pre : List Skeleton) (m m' : Machine),
    runSimple m pre = some m' →
      ∀ rest, execList alphabet fuel m tape (pre ++ rest) = execList alphabet fuel m' tape rest
  | [], m, m', folded, rest => by
      simp only [runSimple, Option.some.injEq] at folded
      subst folded; rfl
  | node :: pre, m, m', folded, rest => by
      simp only [runSimple] at folded
      cases moved : simple? m node with
      | none => rw [moved] at folded; exact absurd folded (by simp)
      | some m₁ =>
          rw [moved] at folded
          simp only [Option.bind_some] at folded
          rw [List.cons_append, execList_cons_simple alphabet fuel m m₁ tape node _ moved]
          exact execList_append_simple fuel tape pre m₁ m' folded rest

/-! ## 7. The parallel move

`Lowering.paramMove` is written with `(List.range values.length).zip values`; the
three lemmas below need it as an indexed walk, so it is restated once as one
and the restatement is proved. -/

/-- An indexed map from an offset. -/
def mapFrom {β : Type} (f : Nat → Slot → β) : Nat → List Slot → List β
  | _, [] => []
  | k, value :: values => f k value :: mapFrom f (k + 1) values

private theorem zip_range_mapFrom {β : Type} (f : Nat → Slot → β) :
    ∀ (values : List Slot) (k : Nat),
      (((List.range values.length).map (· + k)).zip values).map (fun p => f p.1 p.2)
        = mapFrom f k values
  | [], k => rfl
  | value :: values, k => by
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.zip_cons_cons, Nat.zero_add, mapFrom,
        List.cons.injEq, true_and]
      rw [show ((fun x => x + k) ∘ (fun x => x + 1)) = (fun i => i + (k + 1)) from
        funext fun i => by simp only [Function.comp_apply]; omega]
      exact zip_range_mapFrom f values (k + 1)

private theorem zip_range_map_zero {β : Type} (f : Nat → Slot → β) (values : List Slot) :
    (((List.range values.length).zip values).map (fun p => f p.1 p.2)) = mapFrom f 0 values := by
  have : (List.range values.length).map (· + 0) = List.range values.length := by
    simp
  rw [← this]
  exact zip_range_mapFrom f values 0

/-- Read every source into its temporary. -/
def temps (k : Nat) (values : List Slot) : List Skeleton :=
  mapFrom (fun index value => Skeleton.letTemp index value) k values

/-- Write every temporary into its parameter. -/
def moves (target : BlockId) (k : Nat) (values : List Slot) : List Skeleton :=
  mapFrom (fun index _ => Skeleton.assign (.param target index) (.temp index)) k values

/-- Write every source into its parameter. -/
def direct (target : BlockId) (k : Nat) (values : List Slot) : List Skeleton :=
  mapFrom (fun index value => Skeleton.assign (.param target index) value) k values

theorem paramMove_eq (source target : BlockId) (values : List Slot) :
    Lowering.paramMove source target values =
      if source = target then temps 0 values ++ moves target 0 values
      else direct target 0 values := by
  unfold Lowering.paramMove temps moves direct
  by_cases same : source = target
  · simp only [if_pos same]
    rw [zip_range_map_zero (fun index value => Skeleton.letTemp index value),
      zip_range_map_zero (fun index _ => Skeleton.assign (.param target index) (.temp index))]
  · simp only [if_neg same]
    rw [zip_range_map_zero (fun index value => Skeleton.assign (.param target index) value)]

/-- A slot named by one block: the only shapes a `paramMove` reads. -/
def ownedBy (block : BlockId) : Slot → Prop
  | .param owner _ => owner = block
  | .answer owner => owner = block
  | .decision owner => owner = block
  | _ => False

theorem ownedBy_noTemp {block : BlockId} {slot : Slot} (owned : ownedBy block slot) :
    ∀ j, slot ≠ Slot.temp j := by
  cases slot <;> simp only [ownedBy] at owned ⊢ <;> intro j <;> simp

theorem ownedBy_ne_param {block target : BlockId} {slot : Slot} (owned : ownedBy block slot)
    (ne : block ≠ target) : ∀ j, slot ≠ Slot.param target j := by
  cases slot <;> simp only [ownedBy] at owned <;> intro j <;> simp_all

theorem setVal_other (m : Machine) (slot other : Slot) (value : Val) (ne : other ≠ slot) :
    (m.setVal slot value).vals other = m.vals other := by
  simp [Machine.setVal, ne]

theorem setVal_self (m : Machine) (slot : Slot) (value : Val) :
    (m.setVal slot value).vals slot = value := by
  simp [Machine.setVal]

theorem temps_cons (k : Nat) (value : Slot) (values : List Slot) :
    temps k (value :: values) = Skeleton.letTemp k value :: temps (k + 1) values := rfl

theorem moves_cons (target : BlockId) (k : Nat) (value : Slot) (values : List Slot) :
    moves target k (value :: values) =
      Skeleton.assign (.param target k) (.temp k) :: moves target (k + 1) values := rfl

theorem direct_cons (target : BlockId) (k : Nat) (value : Slot) (values : List Slot) :
    direct target k (value :: values) =
      Skeleton.assign (.param target k) value :: direct target (k + 1) values := rfl

theorem runSimple_temps : ∀ (values : List Slot) (k : Nat) (m : Machine),
    (∀ v ∈ values, ∀ j, v ≠ Slot.temp j) →
    ∃ m', runSimple m (temps k values) = some m'
      ∧ (∀ i, (h : i < values.length) → m'.vals (.temp (k + i)) = m.vals values[i])
      ∧ (∀ s, (∀ j, k ≤ j → s ≠ Slot.temp j) → m'.vals s = m.vals s)
      ∧ m'.index = m.index ∧ m'.block = m.block
  | [], k, m, _ => ⟨m, rfl, by intro i h; simp at h, fun _ _ => rfl, rfl, rfl⟩
  | value :: values, k, m, fresh => by
      have m0 : Machine := m.setVal (.temp k) (m.vals value)
      obtain ⟨m', folded, reads, keeps, idx, blk⟩ :=
        runSimple_temps values (k + 1) (m.setVal (.temp k) (m.vals value))
          (fun v mem => fresh v (List.mem_cons_of_mem _ mem))
      refine ⟨m', ?_, ?_, ?_, ?_, ?_⟩
      · rw [temps_cons]
        simp only [runSimple, simple?, Option.bind_some]
        exact folded
      · intro i lt
        cases i with
        | zero =>
            have := keeps (Slot.temp k) (by intro j le; simp; omega)
            simpa [setVal_self] using this
        | succ i =>
            have lt' : i < values.length := by simpa using lt
            have := reads i lt'
            rw [show k + (i + 1) = (k + 1) + i from by omega]
            rw [this, setVal_other _ _ _ _ (fresh values[i] (List.mem_cons_of_mem _
              (List.getElem_mem lt')) k)]
            simp
      · intro s notTemp
        rw [keeps s (fun j le => notTemp j (by omega)),
          setVal_other _ _ _ _ (notTemp k (Nat.le_refl _))]
      · rw [idx]; rfl
      · rw [blk]; rfl

theorem runSimple_moves (target : BlockId) : ∀ (values : List Slot) (k : Nat) (m : Machine),
    ∃ m', runSimple m (moves target k values) = some m'
      ∧ (∀ i, i < values.length → m'.vals (.param target (k + i)) = m.vals (.temp (k + i)))
      ∧ (∀ s, (∀ j, k ≤ j → s ≠ Slot.param target j) → m'.vals s = m.vals s)
      ∧ m'.index = m.index ∧ m'.block = m.block
  | [], k, m => ⟨m, rfl, by intro i h; simp at h, fun _ _ => rfl, rfl, rfl⟩
  | value :: values, k, m => by
      obtain ⟨m', folded, reads, keeps, idx, blk⟩ :=
        runSimple_moves target values (k + 1)
          (m.setVal (.param target k) (m.vals (.temp k)))
      refine ⟨m', ?_, ?_, ?_, ?_, ?_⟩
      · rw [moves_cons]
        simp only [runSimple, simple?, Option.bind_some]
        exact folded
      · intro i lt
        cases i with
        | zero =>
            have := keeps (Slot.param target k) (by intro j le; simp; omega)
            simp only [Nat.add_zero] at this ⊢
            rw [this, setVal_self]
        | succ i =>
            have lt' : i < values.length := by simpa using lt
            have := reads i lt'
            rw [show k + (i + 1) = (k + 1) + i from by omega]
            rw [this, setVal_other _ _ _ _ (by simp)]
      · intro s notParam
        rw [keeps s (fun j le => notParam j (by omega)),
          setVal_other _ _ _ _ (notParam k (Nat.le_refl _))]
      · rw [idx]; rfl
      · rw [blk]; rfl

theorem runSimple_direct (target : BlockId) : ∀ (values : List Slot) (k : Nat) (m : Machine),
    (∀ v ∈ values, ∀ j, v ≠ Slot.param target j) →
    ∃ m', runSimple m (direct target k values) = some m'
      ∧ (∀ i, (h : i < values.length) → m'.vals (.param target (k + i)) = m.vals values[i])
      ∧ (∀ s, (∀ j, k ≤ j → s ≠ Slot.param target j) → m'.vals s = m.vals s)
      ∧ m'.index = m.index ∧ m'.block = m.block
  | [], k, m, _ => ⟨m, rfl, by intro i h; simp at h, fun _ _ => rfl, rfl, rfl⟩
  | value :: values, k, m, fresh => by
      obtain ⟨m', folded, reads, keeps, idx, blk⟩ :=
        runSimple_direct target values (k + 1) (m.setVal (.param target k) (m.vals value))
          (fun v mem => fresh v (List.mem_cons_of_mem _ mem))
      refine ⟨m', ?_, ?_, ?_, ?_, ?_⟩
      · rw [direct_cons]
        simp only [runSimple, simple?, Option.bind_some]
        exact folded
      · intro i lt
        cases i with
        | zero =>
            have := keeps (Slot.param target k) (by intro j le; simp; omega)
            simp only [Nat.add_zero] at this ⊢
            rw [this, setVal_self]
            simp
        | succ i =>
            have lt' : i < values.length := by simpa using lt
            have := reads i lt'
            rw [show k + (i + 1) = (k + 1) + i from by omega]
            rw [this, setVal_other _ _ _ _ (fresh values[i] (List.mem_cons_of_mem _
              (List.getElem_mem lt')) k)]
            simp
      · intro s notParam
        rw [keeps s (fun j le => notParam j (by omega)),
          setVal_other _ _ _ _ (notParam k (Nat.le_refl _))]
      · rw [idx]; rfl
      · rw [blk]; rfl

theorem runSimple_paramMove (source target : BlockId) (values : List Slot) (m : Machine)
    (owned : ∀ v ∈ values, ownedBy source v) :
    ∃ m', runSimple m (Lowering.paramMove source target values) = some m'
      ∧ (∀ i, (h : i < values.length) → m'.vals (.param target i) = m.vals values[i])
      ∧ (∀ s, (∀ j, s ≠ Slot.param target j) → (∀ j, s ≠ Slot.temp j) → m'.vals s = m.vals s)
      ∧ m'.index = m.index ∧ m'.block = m.block := by
  rw [paramMove_eq]
  by_cases same : source = target
  · rw [if_pos same]
    obtain ⟨m₁, folded₁, reads₁, keeps₁, idx₁, blk₁⟩ :=
      runSimple_temps values 0 m (fun v mem => ownedBy_noTemp (owned v mem))
    obtain ⟨m₂, folded₂, reads₂, keeps₂, idx₂, blk₂⟩ := runSimple_moves target values 0 m₁
    refine ⟨m₂, runSimple_append _ _ _ folded₁ _ ▸ folded₂, ?_, ?_, ?_, ?_⟩
    · intro i lt
      have step := reads₂ i lt
      simp only [Nat.zero_add] at step reads₁ ⊢
      rw [step, reads₁ i lt]
    · intro s notParam notTemp
      rw [keeps₂ s (fun j _ => notParam j), keeps₁ s (fun j _ => notTemp j)]
    · rw [idx₂, idx₁]
    · rw [blk₂, blk₁]
  · rw [if_neg same]
    obtain ⟨m', folded, reads, keeps, idx, blk⟩ :=
      runSimple_direct target values 0 m
        (fun v mem => ownedBy_ne_param (owned v mem) same)
    refine ⟨m', folded, ?_, ?_, idx, blk⟩
    · intro i lt; simpa using reads i lt
    · intro s notParam _; exact keeps s (fun j _ => notParam j)

/-! ## 8. The environment invariant -/

/-- The machine holds a block's positional environment. -/
def Holds (m : Machine) (block : BlockId) (env : Env) : Prop :=
  ∀ i, (h : i < env.length) → m.vals (.param block i) = env[i]

/-! ## 9. Unfolding the control nodes -/

theorem execControl_gotoBlock (fuel : Nat) (m : Machine) (tape : Tape) (var : String)
    (target : BlockId) (rest : List Skeleton) :
    execControl alphabet fuel m tape (.gotoBlock var target) rest =
      .pure (.continueLoop (m.setIndex var target.value), tape) := by
  rw [execControl]

theorem execControl_ret (fuel : Nat) (m : Machine) (tape : Tape) (value : Slot)
    (rest : List Skeleton) :
    execControl alphabet fuel m tape (.ret value) rest =
      .pure (.finished (.done (m.vals value)), tape) := by
  rw [execControl]

theorem execControl_perform (fuel : Nat) (m : Machine) (tape : Tape) (answer : Slot)
    (operation : OperationId) (spec : OpSpec) (request : Slot) (rest : List Skeleton) :
    execControl alphabet fuel m tape (.perform answer operation spec request) rest =
      performOp alphabet fuel m tape answer operation request rest := by
  rw [execControl]

theorem execControl_atom (fuel : Nat) (m : Machine) (tape : Tape) (answer : Slot)
    (operation : OperationId) (spec : OpSpec) (request : Slot) (rest : List Skeleton) :
    execControl alphabet fuel m tape (.atom answer operation spec request) rest =
      performOp alphabet fuel m tape answer operation request rest := by
  rw [execControl]

theorem execControl_literal (fuel : Nat) (m : Machine) (tape : Tape) (answer : Slot)
    (operation : OperationId) (request : Slot) (value : Val) (rest : List Skeleton) :
    execControl alphabet fuel m tape (.literal answer operation request value) rest =
      performOp alphabet fuel m tape answer operation request rest := by
  rw [execControl]

theorem execControl_decide (fuel : Nat) (m : Machine) (tape : Tape) (answer : Slot)
    (site : DecisionId) (onTrue onFalse rest : List Skeleton) :
    execControl alphabet fuel m tape (.decide answer site onTrue onFalse) rest =
      (match tape.read site with
       | .exhausted => .pure (.finished (.frontier (.unansweredDecision site)), tape)
       | .mismatch expected actual => .pure (.finished (.refused expected actual), tape)
       | .answered branch more =>
           .vis (.inr (site, branch)) fun _ =>
             Program.bind
               (execList alphabet fuel (m.setVal answer (.bool branch)) more
                 (if branch then onTrue else onFalse))
               (afterFell alphabet fuel rest)) := by
  rw [execControl]

theorem performOp_eq (fuel : Nat) (m : Machine) (tape : Tape) (answer : Slot)
    (operation : OperationId) (request : Slot) (rest : List Skeleton) :
    performOp alphabet fuel m tape answer operation request rest =
      match alphabet.lookup operation with
      | none => .pure (.finished (.frontier (.stuck m.block)), tape)
      | some op =>
          .vis (.inl ⟨op, m.vals request⟩) fun answered : Val =>
            execList alphabet fuel (m.setVal answer answered) tape rest := by
  rw [performOp]

theorem afterFell_fell (fuel : Nat) (rest : List Skeleton) (m : Machine) (tape : Tape) :
    afterFell alphabet fuel rest (.fell m, tape) = execList alphabet fuel m tape rest := by
  rw [afterFell]

theorem afterFell_continueLoop (fuel : Nat) (rest : List Skeleton) (m : Machine) (tape : Tape) :
    afterFell alphabet fuel rest (.continueLoop m, tape) = .pure (.continueLoop m, tape) := by
  rw [afterFell]
  intro _ h
  exact Outcome.noConfusion h

theorem afterFell_finished (fuel : Nat) (rest : List Skeleton) (result : RunResult) (tape : Tape) :
    afterFell alphabet fuel rest (.finished result, tape) = .pure (.finished result, tape) := by
  rw [afterFell]
  intro _ h
  exact Outcome.noConfusion h

theorem dispatchRun_zero (m : Machine) (tape : Tape) (var : String)
    (cases : List (Nat × List Skeleton)) :
    dispatchRun alphabet 0 m tape var cases = .pure (.frontier (.fuel ⟨m.index var⟩), tape) := by
  rw [dispatchRun]

theorem dispatchRun_succ (fuel : Nat) (m : Machine) (tape : Tape) (var : String)
    (cases : List (Nat × List Skeleton)) :
    dispatchRun alphabet (fuel + 1) m tape var cases =
      match caseBody? cases (m.index var) with
      | none => .pure (.frontier (.stuck ⟨m.index var⟩), tape)
      | some body =>
          Program.bind (execList alphabet fuel m tape body) (dispatchCatch alphabet fuel var cases) := by
  rw [dispatchRun]

theorem dispatchCatch_continueLoop (fuel : Nat) (var : String)
    (cases : List (Nat × List Skeleton)) (m : Machine) (tape : Tape) :
    dispatchCatch alphabet fuel var cases (.continueLoop m, tape) =
      dispatchRun alphabet fuel m tape var cases := by
  rw [dispatchCatch]

theorem dispatchCatch_finished (fuel : Nat) (var : String)
    (cases : List (Nat × List Skeleton)) (result : RunResult) (tape : Tape) :
    dispatchCatch alphabet fuel var cases (.finished result, tape) = .pure (result, tape) := by
  rw [dispatchCatch]

/-! ## 10. Reading an argument list -/

theorem readArgs_getElem? : ∀ (args : List Var) (env : Env) (values : List Val),
    readArgs env args = some values →
      values.length = args.length ∧
        ∀ i : Nat, values[i]? = (args[i]?).bind fun v : Var => env[v.index]?
  | [], env, values, read => by
      simp only [readArgs, Option.some.injEq] at read
      subst read
      exact ⟨rfl, by intro i; simp⟩
  | v :: vs, env, values, read => by
      simp only [readArgs] at read
      cases head : env[v.index]? with
      | none => rw [head] at read; simp at read
      | some value =>
          cases tail : readArgs env vs with
          | none => rw [head, tail] at read; simp at read
          | some rest =>
              rw [head, tail] at read
              simp only [Option.some.injEq] at read
              subst read
              obtain ⟨len, reads⟩ := readArgs_getElem? vs env rest tail
              refine ⟨by simp [len], ?_⟩
              intro i
              cases i with
              | zero => simpa using head.symm
              | succ i => simpa using reads i

theorem enter_vals (m : Machine) (block : BlockId) : (m.enter block).vals = m.vals := rfl

theorem setIndex_vals (m : Machine) (var : String) (value : Nat) :
    (m.setIndex var value).vals = m.vals := rfl

theorem setIndex_same (m : Machine) (var : String) (value : Nat) :
    (m.setIndex var value).index var = value := by simp [Machine.setIndex]

/-! ## 11. A move and a dispatch transfer -/

theorem execControl_dispatchLoop (fuel : Nat) (m : Machine) (tape : Tape) (var : String)
    (cases : List (Nat × List Skeleton)) (rest : List Skeleton) :
    execControl alphabet fuel m tape (.dispatchLoop var cases) rest
      = Program.bind (dispatchRun alphabet fuel m tape var cases)
          fun result => .pure (.finished result.1, result.2) := by
  rw [execControl]

theorem execList_cons_control (fuel : Nat) (m : Machine) (tape : Tape) (node : Skeleton)
    (rest : List Skeleton) (control : simple? m node = none) :
    execList alphabet fuel m tape (node :: rest) = execControl alphabet fuel m tape node rest := by
  rw [execList_cons, control]

theorem holds_of_getElem? {m : Machine} {block : BlockId} {env : Env} {i : Nat} {v : Val}
    (holds : Holds m block env) (read : env[i]? = some v) : m.vals (.param block i) = v := by
  obtain ⟨lt, eq⟩ := List.getElem?_eq_some_iff.mp read
  rw [holds i lt, eq]

/-- The machine a dispatch-form transfer leaves behind: the parallel move, then
the new block index. It is named rather than existentially quantified because a
`perform`'s continuation has to be a function this module can write down, and
`Exists.choose` would put `Classical.choice` in the axiom report. -/
def movedMachine (source target : BlockId) (slots : List Slot) (m : Machine) : Machine :=
  ((runSimple m (Lowering.paramMove source target slots)).getD m).setIndex "block" target.value

theorem execList_move_goto (fuel : Nat) (m : Machine) (tape : Tape)
    (source target : BlockId) (slots : List Slot) (vals : List Val)
    (owned : ∀ s ∈ slots, ownedBy source s)
    (len : slots.length = vals.length)
    (agree : ∀ (i : Nat) (s : Slot) (v : Val), slots[i]? = some s → vals[i]? = some v →
      m.vals s = v) :
    execList alphabet fuel m tape
        (Lowering.paramMove source target slots ++ Lowering.goto target)
      = .pure (.continueLoop (movedMachine source target slots m), tape)
      ∧ (movedMachine source target slots m).index "block" = target.value
      ∧ Holds (movedMachine source target slots m) target vals := by
  obtain ⟨m₂, folded, reads, _, _, _⟩ := runSimple_paramMove source target slots m owned
  have named : movedMachine source target slots m = m₂.setIndex "block" target.value := by
    simp [movedMachine, folded]
  rw [named]
  refine ⟨?_, setIndex_same _ _ _, ?_⟩
  · rw [execList_append_simple alphabet fuel tape _ m m₂ folded]
    show execList alphabet fuel m₂ tape [Skeleton.gotoBlock "block" target] = _
    rw [execList_cons_control alphabet fuel m₂ tape (Skeleton.gotoBlock "block" target) [] rfl,
      execControl_gotoBlock]
  · intro i lt
    rw [setIndex_vals]
    have lt' : i < slots.length := by omega
    rw [reads i lt']
    exact agree i slots[i] vals[i] (List.getElem?_eq_getElem lt') (List.getElem?_eq_getElem lt)

/-! ## 12. Inverting `plan`

Six inversion lemmas, stated over an arbitrary `FlowAlphabet` so that the
alphabet's `lookup` stays opaque: the lowering's alphabet is a table, and
unfolding it turns `lookup` into a `dite` no equation can be rewritten into. -/

section Inversion

variable {Ty : Type} {alphabet : FlowAlphabet Ty} {block : RawBlock Ty} {env : Env} {tape : Tape}

theorem plan_ret_inv {value : Val} (planned : plan alphabet block env tape = .ret value) :
    ∃ v : Var, block.term = .ret v ∧ env[v.index]? = some value := by
  cases hterm : block.term with
  | ret v =>
      cases read : env[v.index]? with
      | none => simp [plan, hterm, read] at planned
      | some w =>
          simp only [plan, hterm, read, Plan.ret.injEq] at planned
          exact ⟨v, rfl, by rw [read, planned]⟩
  | jump target args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation request target args =>
      cases known : alphabet.lookup operation <;> cases got : env[request.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned

theorem plan_jump_inv {target : BlockId} {env' : Env}
    (planned : plan alphabet block env tape = .jump target env') :
    ∃ args, block.term = .jump target args ∧ readArgs env args = some env' := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          simp only [plan, hterm, read, Plan.jump.injEq] at planned
          obtain ⟨rfl, rfl⟩ := planned
          exact ⟨args, rfl, read⟩
  | perform operation request target args =>
      cases known : alphabet.lookup operation <;> cases got : env[request.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned

theorem plan_perform_inv {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
    (planned : plan alphabet block env tape = .perform op request target env') :
    ∃ (operation : OperationId) (requestVar : Var) (args : List Var),
      block.term = .perform operation requestVar target args
        ∧ alphabet.lookup operation = some op
        ∧ env[requestVar.index]? = some request
        ∧ readArgs env args = some env' := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation with
      | none =>
          cases got : env[requestVar.index]? <;> cases read : readArgs env args <;>
            simp [plan, hterm, known, got, read] at planned
      | some found =>
          cases got : env[requestVar.index]? with
          | none =>
              cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
          | some requested =>
              cases read : readArgs env args with
              | none => simp [plan, hterm, known, got, read] at planned
              | some values =>
                  simp only [plan, hterm, known, got, read, Plan.perform.injEq] at planned
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := planned
                  exact ⟨operation, requestVar, args, rfl, known, got, read⟩
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned

theorem plan_choose_inv {site : DecisionId} {branch : Bool} {target : BlockId} {env' : Env}
    {rest : Tape}
    (planned : plan alphabet block env tape = .choose site branch target env' rest) :
    ∃ (left right : BlockId) (args : List Var),
      block.term = .choose site left right args
        ∧ readArgs env args = some env'
        ∧ tape.read site = .answered branch rest
        ∧ target = (if branch then left else right) := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              simp only [plan, hterm, read, answered, Plan.choose.injEq] at planned
              obtain ⟨rfl, rfl, eqTarget, rfl, rfl⟩ := planned
              exact ⟨left, right, args, rfl, read, answered, eqTarget.symm⟩

theorem plan_exhausted_inv {site : DecisionId}
    (planned : plan alphabet block env tape = .exhausted site) :
    ∃ (left right : BlockId) (args : List Var),
      block.term = .choose site left right args ∧ tape.read site = .exhausted := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted =>
              simp only [plan, hterm, read, answered, Plan.exhausted.injEq] at planned
              subst planned
              exact ⟨left, right, args, rfl, answered⟩
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more => simp [plan, hterm, read, answered] at planned

theorem plan_mismatch_inv {expected actual : DecisionId}
    (planned : plan alphabet block env tape = .mismatch expected actual) :
    ∃ (site : DecisionId) (left right : BlockId) (args : List Var),
      block.term = .choose site left right args
        ∧ tape.read site = .mismatch expected actual := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch e a =>
              simp only [plan, hterm, read, answered, Plan.mismatch.injEq] at planned
              obtain ⟨rfl, rfl⟩ := planned
              exact ⟨decision, left, right, args, rfl, answered⟩
          | answered chosen more => simp [plan, hterm, read, answered] at planned

end Inversion

/-! ## 13. One block of the dispatch form -/

/-- Every slot a block's move reads is one of that block's own. -/
theorem ownedBy_argSlots (block : BlockId) (args : List Var) :
    ∀ s ∈ args.map fun v : Var => Slot.param block v.index, ownedBy block s := by
  intro s mem
  simp only [List.mem_map] at mem
  obtain ⟨v, _, rfl⟩ := mem
  exact rfl

/-- The move of a `jump` or a `choose` reads the block's parameters and finds
exactly the values `readArgs` read. -/
theorem argSlots_agree {m : Machine} {block : BlockId} {env : Env} (holds : Holds m block env)
    {args : List Var} {values : List Val} (read : readArgs env args = some values) :
    (args.map fun v : Var => Slot.param block v.index).length = values.length
      ∧ ∀ (i : Nat) (s : Slot) (v : Val),
          (args.map fun v : Var => Slot.param block v.index)[i]? = some s →
          values[i]? = some v → m.vals s = v := by
  obtain ⟨len, reads⟩ := readArgs_getElem? args env values read
  refine ⟨by simp [len], ?_⟩
  intro i s v slotAt valAt
  rw [List.getElem?_map] at slotAt
  cases named : args[i]? with
  | none => rw [named] at slotAt; simp at slotAt
  | some a =>
      rw [named] at slotAt
      simp only [Option.map_some, Option.some.injEq] at slotAt
      subst slotAt
      refine holds_of_getElem? holds ?_
      have step := reads i
      rw [valAt, named] at step
      simpa using step.symm

set_option maxHeartbeats 1000000 in
/-- Running the dispatch-form body of one block is exactly what `plan` says that
block does, with the machine carrying the environment across the move. -/
theorem execList_skeletonBlock (table : List OpSpec) (fuel : Nat) (m : Machine) (tape : Tape)
    (block : RawBlock String) (env : Env) (body : List Skeleton)
    (built : Flow.skeletonBlock table block = some body)
    (holds : Holds m block.id env) :
    (∀ value, plan (tableAlphabet ⟨0⟩ table) block env tape = .ret value →
        execList (tableAlphabet ⟨0⟩ table) fuel m tape body
          = .pure (.finished (.done value), tape))
      ∧ (∀ target env', plan (tableAlphabet ⟨0⟩ table) block env tape = .jump target env' →
        ∃ m', execList (tableAlphabet ⟨0⟩ table) fuel m tape body = .pure (.continueLoop m', tape)
          ∧ m'.index "block" = target.value ∧ Holds m' target env')
      ∧ (∀ op request target env',
          plan (tableAlphabet ⟨0⟩ table) block env tape = .perform op request target env' →
        ∃ next : Val → Machine,
          execList (tableAlphabet ⟨0⟩ table) fuel m tape body
            = .vis (.inl ⟨op, request⟩) (fun answered : Val =>
                .pure (.continueLoop (next answered), tape))
          ∧ ∀ answered, (next answered).index "block" = target.value
              ∧ Holds (next answered) target (env' ++ [answered]))
      ∧ (∀ site branch target env' rest,
          plan (tableAlphabet ⟨0⟩ table) block env tape = .choose site branch target env' rest →
        ∃ m', execList (tableAlphabet ⟨0⟩ table) fuel m tape body
            = .vis (.inr (site, branch)) (fun _ => .pure (.continueLoop m', rest))
          ∧ m'.index "block" = target.value ∧ Holds m' target env')
      ∧ (∀ site, plan (tableAlphabet ⟨0⟩ table) block env tape = .exhausted site →
        execList (tableAlphabet ⟨0⟩ table) fuel m tape body
          = .pure (.finished (.frontier (.unansweredDecision site)), tape))
      ∧ (∀ expected actual,
          plan (tableAlphabet ⟨0⟩ table) block env tape = .mismatch expected actual →
        execList (tableAlphabet ⟨0⟩ table) fuel m tape body
          = .pure (.finished (.refused expected actual), tape)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro value planned
    obtain ⟨v, hterm, read⟩ := plan_ret_inv planned
    simp only [Flow.skeletonBlock, Flow.skeletonBlockWith, hterm, Option.some.injEq] at built
    subst built
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
      execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl]
    show execControl _ fuel (m.enter block.id) tape
      (Skeleton.ret (.param block.id v.index)) [] = _
    rw [execControl_ret, enter_vals, holds_of_getElem? holds read]
  · intro target env' planned
    obtain ⟨args, hterm, read⟩ := plan_jump_inv planned
    simp only [Flow.skeletonBlock, Flow.skeletonBlockWith, hterm, Flow.dispatchTransfer,
      Option.map_some, Option.some.injEq] at built
    subst built
    obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
    obtain ⟨ran, idx, hold⟩ :=
      execList_move_goto (tableAlphabet ⟨0⟩ table) fuel (m.enter block.id) tape
        block.id target (args.map fun v : Var => Slot.param block.id v.index) env'
        (ownedBy_argSlots block.id args) len
        (by intro i s v slotAt valAt; rw [enter_vals]; exact agree i s v slotAt valAt)
    refine ⟨_, ?_, idx, hold⟩
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl]
    exact ran
  · intro op request target env' planned
    obtain ⟨operation, requestVar, args, hterm, known, got, read⟩ := plan_perform_inv planned
    simp only [Flow.skeletonBlock, Flow.skeletonBlockWith, hterm, Flow.dispatchTransfer] at built
    have shape : ∃ head : Skeleton,
        (∀ m' : Machine, simple? m' head = none)
          ∧ (∀ (fuel' : Nat) (m' : Machine) (tape' : Tape) (rest' : List Skeleton),
            execControl (tableAlphabet ⟨0⟩ table) fuel' m' tape' head rest'
              = performOp (tableAlphabet ⟨0⟩ table) fuel' m' tape' (.answer block.id) operation
                  (.param block.id requestVar.index) rest')
          ∧ body = Skeleton.enterBlock block.id :: head ::
              (Lowering.paramMove block.id target
                  ((args.map fun v : Var => Slot.param block.id v.index)
                    ++ [Slot.answer block.id]) ++ Lowering.goto target) := by
      cases spec : Flow.spec? table operation with
      | none => simp [spec] at built
      | some row =>
          simp only [spec, Option.bind_eq_bind, Option.bind_some] at built
          cases kind : row.kind with
          | family =>
              simp only [kind, Option.some.injEq] at built
              exact ⟨_, fun _ => rfl, fun _ _ _ _ => execControl_perform _ _ _ _ _ _ _ _ _,
                built.symm⟩
          | atom =>
              simp only [kind, Option.some.injEq] at built
              exact ⟨_, fun _ => rfl, fun _ _ _ _ => execControl_atom _ _ _ _ _ _ _ _ _,
                built.symm⟩
          | lit constant =>
              simp only [kind] at built
              cases spelled : Flow.literal? constant with
              | none => simp [spelled] at built
              | some expr =>
                  simp only [spelled, Option.map_some, Option.bind_some, Option.some.injEq] at built
                  exact ⟨_, fun _ => rfl, fun _ _ _ _ => execControl_literal _ _ _ _ _ _ _ _ _,
                    built.symm⟩
    obtain ⟨head, headSimple, headRun, rfl⟩ := shape
    obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
    obtain ⟨lenRead, _⟩ := readArgs_getElem? args env env' read
    have moved : ∀ answered : Val,
        execList (tableAlphabet ⟨0⟩ table) fuel
            ((m.enter block.id).setVal (.answer block.id) answered) tape
            (Lowering.paramMove block.id target
              ((args.map fun v : Var => Slot.param block.id v.index)
                ++ [Slot.answer block.id]) ++ Lowering.goto target)
          = .pure (.continueLoop (movedMachine block.id target
              ((args.map fun v : Var => Slot.param block.id v.index) ++ [Slot.answer block.id])
              ((m.enter block.id).setVal (.answer block.id) answered)), tape)
        ∧ (movedMachine block.id target
              ((args.map fun v : Var => Slot.param block.id v.index) ++ [Slot.answer block.id])
              ((m.enter block.id).setVal (.answer block.id) answered)).index "block" = target.value
        ∧ Holds (movedMachine block.id target
              ((args.map fun v : Var => Slot.param block.id v.index) ++ [Slot.answer block.id])
              ((m.enter block.id).setVal (.answer block.id) answered))
            target (env' ++ [answered]) := by
      intro answered
      refine execList_move_goto (tableAlphabet ⟨0⟩ table) fuel _ tape block.id target _
        (env' ++ [answered]) ?_ ?_ ?_
      · intro s mem
        simp only [List.mem_append, List.mem_singleton] at mem
        rcases mem with inArgs | rfl
        · exact ownedBy_argSlots block.id args s inArgs
        · exact rfl
      · simp [len]
      · intro i s v slotAt valAt
        by_cases small : i < args.length
        · rw [List.getElem?_append_left (by simpa using small)] at slotAt
          rw [List.getElem?_append_left (by omega)] at valAt
          have sMem : s ∈ args.map fun v : Var => Slot.param block.id v.index :=
            List.mem_of_getElem? slotAt
          simp only [List.mem_map] at sMem
          obtain ⟨a, _, rfl⟩ := sMem
          rw [setVal_other _ _ _ _ (by simp), enter_vals]
          exact agree i _ v slotAt valAt
        · have inRange : i < ((args.map fun v : Var => Slot.param block.id v.index)
              ++ [Slot.answer block.id]).length :=
            (List.getElem?_eq_some_iff.mp slotAt).1
          simp only [List.length_append, List.length_map, List.length_singleton] at inRange
          have same : i = args.length := by omega
          subst same
          rw [List.getElem?_append_right (by simp)] at slotAt
          rw [List.getElem?_append_right (by omega)] at valAt
          simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero,
            Option.some.injEq] at slotAt
          rw [show args.length - env'.length = 0 from by omega] at valAt
          simp only [List.getElem?_cons_zero, Option.some.injEq] at valAt
          subst slotAt
          subst valAt
          exact setVal_self _ _ _
    refine ⟨fun answered => movedMachine block.id target
        ((args.map fun v : Var => Slot.param block.id v.index) ++ [Slot.answer block.id])
        ((m.enter block.id).setVal (.answer block.id) answered), ?_,
      fun answered => ⟨(moved answered).2.1, (moved answered).2.2⟩⟩
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
      execList_cons_control _ fuel (m.enter block.id) tape head _ (headSimple (m.enter block.id)),
      headRun fuel (m.enter block.id) tape _, performOp_eq, known, enter_vals,
      holds_of_getElem? holds got]
    dsimp only
    congr 1
    funext answered
    exact (moved answered).1
  · intro site branch target env' rest planned
    obtain ⟨left, right, args, hterm, read, answered, eqTarget⟩ := plan_choose_inv planned
    subst eqTarget
    simp only [Flow.skeletonBlock, Flow.skeletonBlockWith, hterm, Flow.dispatchTransfer,
      Lowering.chooseIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
    subst built
    obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
    have branchRun : ∀ side : BlockId,
        execList (tableAlphabet ⟨0⟩ table) fuel
            ((m.enter block.id).setVal (.decision block.id) (.bool branch)) rest
            (Lowering.paramMove block.id side
              (args.map fun v : Var => Slot.param block.id v.index) ++ Lowering.goto side)
          = .pure (.continueLoop (movedMachine block.id side
              (args.map fun v : Var => Slot.param block.id v.index)
              ((m.enter block.id).setVal (.decision block.id) (.bool branch))), rest)
        ∧ (movedMachine block.id side
              (args.map fun v : Var => Slot.param block.id v.index)
              ((m.enter block.id).setVal (.decision block.id) (.bool branch))).index "block"
            = side.value
        ∧ Holds (movedMachine block.id side
              (args.map fun v : Var => Slot.param block.id v.index)
              ((m.enter block.id).setVal (.decision block.id) (.bool branch))) side env' := by
      intro side
      refine execList_move_goto (tableAlphabet ⟨0⟩ table) fuel _ rest block.id side _ env'
        (ownedBy_argSlots block.id args) len ?_
      intro i s v slotAt valAt
      have sMem : s ∈ args.map fun v : Var => Slot.param block.id v.index :=
        List.mem_of_getElem? slotAt
      simp only [List.mem_map] at sMem
      obtain ⟨a, _, rfl⟩ := sMem
      rw [setVal_other _ _ _ _ (by simp), enter_vals]
      exact agree i _ v slotAt valAt
    obtain ⟨ran, idx, hold⟩ := branchRun (if branch then left else right)
    refine ⟨_, ?_, idx, hold⟩
    have selected : (if branch then
          Lowering.paramMove block.id left
              (args.map fun v : Var => Slot.param block.id v.index) ++ Lowering.goto left
        else Lowering.paramMove block.id right
              (args.map fun v : Var => Slot.param block.id v.index) ++ Lowering.goto right)
        = Lowering.paramMove block.id (if branch then left else right)
            (args.map fun v : Var => Slot.param block.id v.index)
            ++ Lowering.goto (if branch then left else right) := by
      cases branch <;> rfl
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
      execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
      execControl_decide, answered]
    dsimp only
    congr 1
    funext _
    rw [selected, ran]
    exact afterFell_continueLoop _ fuel [] _ rest
  · intro site planned
    obtain ⟨left, right, args, hterm, answered⟩ := plan_exhausted_inv planned
    simp only [Flow.skeletonBlock, Flow.skeletonBlockWith, hterm, Flow.dispatchTransfer,
      Lowering.chooseIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
    subst built
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
      execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
      execControl_decide, answered]
  · intro expected actual planned
    obtain ⟨site, left, right, args, hterm, answered⟩ := plan_mismatch_inv planned
    simp only [Flow.skeletonBlock, Flow.skeletonBlockWith, hterm, Flow.dispatchTransfer,
      Lowering.chooseIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
    subst built
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
      execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
      execControl_decide, answered]

/-! ## 14. The whole dispatch form -/

/-- The run result a finished skeleton reports. A skeleton that falls out of
its own control (an unbound `break`, a `continue` with no loop) has left the
program: that is a `stuck` frontier of the block last entered. -/
def Outcome.result : Outcome → RunResult
  | .finished result => result
  | .fell m => .frontier (.stuck m.block)
  | .continueLoop m => .frontier (.stuck m.block)
  | .continueLabel _ m => .frontier (.stuck m.block)
  | .breakLabel _ m => .frontier (.stuck m.block)

/-- The machine a lowered program starts in: the parameter binder holds the
input, every other slot is `unit`, every index is `0`. -/
def start (binder : String) (input : Val) : Machine where
  vals := fun s => if s = .input binder then input else .unit
  index := fun _ => 0
  block := ⟨0⟩

/-- `⟦·⟧` of the plan: the denotation of a lowered statement list. -/
def denoteNodes (fuel : Nat) (binder : String) (nodes : List Skeleton) (tape : Tape) (input : Val) :
    Program (FullSig alphabet) (RunResult × Tape) :=
  Program.bind (execList alphabet fuel (start binder input) tape nodes)
    fun result => .pure (result.1.result, result.2)

theorem bind_pure (program : Program (FullSig alphabet) (RunResult × Tape)) :
    Program.bind program (fun result => .pure (result.1, result.2)) = program :=
  Program.bind_pure_right program

theorem bind_vis_inl {A B : Type} (op : alphabet.Op) (request : Val)
    (next : Val → Program (FullSig alphabet) A) (last : A → Program (FullSig alphabet) B) :
    Program.bind (.vis (Sum.inl ⟨op, request⟩) next) last
      = .vis (Sum.inl ⟨op, request⟩) fun answer : Val => Program.bind (next answer) last := rfl

theorem bind_vis_inr {A B : Type} (site : DecisionId) (branch : Bool)
    (next : (FullSig alphabet).Answer (Sum.inr (site, branch)) → Program (FullSig alphabet) A)
    (last : A → Program (FullSig alphabet) B) :
    Program.bind (.vis (Sum.inr (site, branch)) next) last
      = .vis (Sum.inr (site, branch)) fun answer => Program.bind (next answer) last := rfl

theorem start_input (binder : String) (input : Val) :
    (start binder input).vals (.input binder) = input := by
  simp [start]

/-! ### The prefix of simple nodes -/

/-- A node that never inspects the machine folds it unchanged. -/
theorem runSimple_fixed : ∀ (nodes : List Skeleton) (m : Machine),
    (∀ node ∈ nodes, ∀ m' : Machine, simple? m' node = some m') → runSimple m nodes = some m
  | [], m, _ => rfl
  | node :: rest, m, fixed => by
      rw [runSimple, fixed node List.mem_cons_self m]
      simp only [Option.bind_some]
      exact runSimple_fixed rest m fun n mem => fixed n (List.mem_cons_of_mem _ mem)

theorem runSimple_acquisitions (rows : ServiceRow) (table : List OpSpec) (raw : RawFlow String)
    (m : Machine) : runSimple m (Flow.acquisitions rows table raw) = some m := by
  refine runSimple_fixed _ m ?_
  intro node mem
  unfold Flow.acquisitions at mem
  have shape : ∃ row : ServiceRow, node = Skeleton.acquireService row := by
    rcases List.mem_append.mp mem with inFamily | inDecisions
    · split at inFamily
      · exact ⟨rows, by simpa using inFamily⟩
      · simp at inFamily
    · split at inDecisions
      · exact ⟨decisionsRows, by simpa using inDecisions⟩
      · simp at inDecisions
  obtain ⟨row, rfl⟩ := shape
  intro m'
  rfl

theorem runSimple_declarations (blocks : List (RawBlock String)) (m : Machine) :
    runSimple m (Flow.declarations blocks) = some m := by
  refine runSimple_fixed _ m ?_
  intro node mem
  simp only [Flow.declarations, List.mem_flatMap, List.mem_map] at mem
  obtain ⟨_, _, _, _, rfl⟩ := mem
  intro m'
  rfl

/-! ### The case table -/

/-- What a successful `mapM` over the block table leaves in the switch: the case
for a block index is the lowered body of the block that index resolves to. Both
`List.find?` and `caseBody?` take the first match and both walk the declaration
list in order, so no uniqueness of block identities is needed. -/
theorem caseBody?_of_mapM (table : List OpSpec)
    (lower : RawBlock String → Option (Nat × List Skeleton))
    (spec : ∀ b, lower b = (Flow.skeletonBlock table b).map (Lowering.blockCase b.id)) :
    ∀ (blocks : List (RawBlock String)) (cases : List (Nat × List Skeleton)),
      blocks.mapM lower = some cases →
      ∀ (index : Nat) (current : RawBlock String),
        blocks.find? (fun block => block.id = ⟨index⟩) = some current →
        ∃ body, Flow.skeletonBlock table current = some body ∧ caseBody? cases index = some body
  | [], cases, built, index, current, found => by simp at found
  | block :: blocks, cases, built, index, current, found => by
      rw [List.mapM_cons, spec block] at built
      cases lowered : Flow.skeletonBlock table block with
      | none => rw [lowered] at built; simp at built
      | some body =>
          rw [lowered] at built
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some] at built
          cases rest : blocks.mapM lower with
          | none => rw [rest] at built; simp at built
          | some more =>
              rw [rest] at built
              simp only [Option.bind_some] at built
              have casesEq : Lowering.blockCase block.id body :: more = cases :=
                Option.some.inj built
              subst casesEq
              by_cases here : block.id = (⟨index⟩ : BlockId)
              · rw [List.find?_cons_of_pos (by simp [here])] at found
                obtain rfl : current = block := (Option.some.inj found).symm
                refine ⟨body, lowered, ?_⟩
                simp [caseBody?, Lowering.blockCase, here]
              · rw [List.find?_cons_of_neg (by simp [here])] at found
                obtain ⟨inner, loweredInner, case⟩ :=
                  caseBody?_of_mapM table lower spec blocks more rest index current found
                refine ⟨inner, loweredInner, ?_⟩
                have ne : ¬ block.id.value = index := fun eq => here (by rw [← eq])
                simp [caseBody?, Lowering.blockCase, ne, case]

/-! ### T3 -/

set_option maxHeartbeats 1000000 in
/-- The core of T3: one turn of the dispatch loop is one block of the flow, so
the loop's fuel is `denoteFuel`'s fuel, unit for unit. -/
theorem dispatchRun_denoteFuel (table : List OpSpec) (raw : RawFlow String)
    (wf : FlowWF (tableAlphabet ⟨0⟩ table) raw) (cases : List (Nat × List Skeleton))
    (built : ∀ (index : Nat) (current : RawBlock String),
      lookupBlock raw ⟨index⟩ = some current →
        ∃ body, Flow.skeletonBlock table current = some body ∧ caseBody? cases index = some body) :
    ∀ (fuel : Nat) (m : Machine) (tape : Tape) (block : BlockId) (env : Env)
      (current : RawBlock String),
      lookupBlock raw block = some current → env.length = current.params.length →
      m.index "block" = block.value → Holds m block env →
      dispatchRun (tableAlphabet ⟨0⟩ table) fuel m tape "block" cases
        = denoteFuel fuel raw block env tape := by
  intro fuel
  induction fuel with
  | zero =>
      intro m tape block env current _ _ indexed _
      rw [dispatchRun_zero, indexed, denoteFuel]
  | succ fuel ih =>
      intro m tape block env current found sized indexed holds
      have mem : current ∈ raw.blocks := List.mem_of_find?_eq_some found
      obtain ⟨body, lowered, case⟩ := built block.value current found
      obtain ⟨onRet, onJump, onPerform, onChoose, onExhausted, onMismatch⟩ :=
        execList_skeletonBlock table fuel m tape current env body lowered
          (by rw [lookupBlock_id found]; exact holds)
      have plannedSized := plan_checked wf mem sized tape
      rw [dispatchRun_succ, indexed, case, denoteFuel, found]
      dsimp only
      generalize planEq : plan (tableAlphabet ⟨0⟩ table) current env tape = p at plannedSized
      cases plannedSized with
      | ret value =>
          rw [onRet value planEq]
          show dispatchCatch (tableAlphabet ⟨0⟩ table) fuel "block" cases
              (Outcome.finished (RunResult.done value), tape)
            = Program.pure (RunResult.done value, tape)
          exact dispatchCatch_finished _ fuel "block" cases (.done value) tape
      | exhausted site =>
          rw [onExhausted site planEq]
          show dispatchCatch (tableAlphabet ⟨0⟩ table) fuel "block" cases
              (Outcome.finished (RunResult.frontier (Frontier.unansweredDecision site)), tape)
            = Program.pure (RunResult.frontier (Frontier.unansweredDecision site), tape)
          exact dispatchCatch_finished _ fuel "block" cases _ tape
      | mismatch expected actual =>
          rw [onMismatch expected actual planEq]
          show dispatchCatch (tableAlphabet ⟨0⟩ table) fuel "block" cases
              (Outcome.finished (RunResult.refused expected actual), tape)
            = Program.pure (RunResult.refused expected actual, tape)
          exact dispatchCatch_finished _ fuel "block" cases _ tape
      | jump targetBlock foundTarget sizedTarget =>
          rename_i target env'
          obtain ⟨m', ran, indexed', holds'⟩ := onJump target env' planEq
          rw [ran]
          show dispatchCatch (tableAlphabet ⟨0⟩ table) fuel "block" cases
              (Outcome.continueLoop m', tape) = denoteFuel fuel raw target env' tape
          rw [dispatchCatch_continueLoop]
          exact ih m' tape target env' targetBlock foundTarget sizedTarget indexed' holds'
      | perform targetBlock foundTarget sizedTarget =>
          rename_i op request target env'
          obtain ⟨next, ran, steps⟩ := onPerform op request target env' planEq
          rw [ran, bind_vis_inl]
          refine congrArg (@Program.vis (FullSig (tableAlphabet ⟨0⟩ table)) (RunResult × Tape)
            (Sum.inl ⟨op, request⟩)) (funext fun answered => ?_)
          show dispatchCatch (tableAlphabet ⟨0⟩ table) fuel "block" cases
              (Outcome.continueLoop (next answered), tape) = _
          rw [dispatchCatch_continueLoop]
          exact ih (next answered) tape target (env' ++ [answered]) targetBlock foundTarget
            (by simp [← sizedTarget]) (steps answered).1 (steps answered).2
      | choose targetBlock foundTarget sizedTarget =>
          rename_i site branch target env' rest
          obtain ⟨m', ran, indexed', holds'⟩ := onChoose site branch target env' rest planEq
          rw [ran, bind_vis_inr]
          refine congrArg (@Program.vis (FullSig (tableAlphabet ⟨0⟩ table)) (RunResult × Tape)
            (Sum.inr (site, branch))) (funext fun _ => ?_)
          show dispatchCatch (tableAlphabet ⟨0⟩ table) fuel "block" cases
              (Outcome.continueLoop m', rest) = _
          rw [dispatchCatch_continueLoop]
          exact ih m' rest target env' targetBlock foundTarget sizedTarget indexed' holds'

/-- The dispatch form's prefix moves the input into the entry block's first
parameter and sets the block index; nothing else in it inspects the machine. -/
theorem execList_dispatchPrefix (rows : ServiceRow) (table : List OpSpec) (raw : RawFlow String)
    (fuel : Nat) (tape : Tape) (binder : String) (input : Val)
    (cases : List (Nat × List Skeleton)) :
    execList (tableAlphabet ⟨0⟩ table) fuel (start binder input) tape
        (Flow.acquisitions rows table raw ++ Flow.declarations raw.blocks ++
          [ Skeleton.assign (.param raw.entry 0) (.input binder)
          , Skeleton.letBlockIndex "block" raw.entry
          , Lowering.dispatchLoop cases ])
      = Program.bind (dispatchRun (tableAlphabet ⟨0⟩ table) fuel
          (((start binder input).setVal (.param raw.entry 0) input).setIndex "block" raw.entry.value)
          tape "block" cases)
          fun result => .pure (.finished result.1, result.2) := by
  rw [execList_append_simple _ fuel tape _ (start binder input) (start binder input)
    (by rw [runSimple_append _ _ _ (runSimple_acquisitions rows table raw (start binder input))]
        exact runSimple_declarations raw.blocks _)]
  rw [execList_cons_simple _ fuel _ ((start binder input).setVal (.param raw.entry 0) input) tape
    _ _ (by
      show some ((start binder input).setVal (Slot.param raw.entry 0)
        ((start binder input).vals (Slot.input binder))) = _
      rw [start_input])]
  rw [execList_cons_simple _ fuel _
    (((start binder input).setVal (.param raw.entry 0) input).setIndex "block" raw.entry.value)
    tape _ _ (by rfl)]
  rw [execList_cons_control _ fuel _ tape (Lowering.dispatchLoop cases) [] rfl]
  exact execControl_dispatchLoop _ fuel _ tape "block" cases []

end Skel

/-! ## 15. `⟦·⟧` and T3 -/

open Skel in
/-- `⟦·⟧` of plan packet D3: the denotation of a lowered statement list, at a
fuel, against a decision tape, into the same `Program (FullSig …)` the flow
denotation of `Effect4/Semantics/Denotation.lean` lands in. -/
def Skeleton.denote {Ty : Type} (alphabet : FlowAlphabet Ty) (fuel : Nat) (binder : String)
    (nodes : List Skeleton) (tape : Tape) (input : Val) :
    Program (FullSig alphabet) (RunResult × Tape) :=
  Skel.denoteNodes alphabet fuel binder nodes tape input

open Skel in
/-- **T3.** The dispatch-form skeleton of a checked flow denotes the flow.

The fuel is the one `fuelFor` allots, and by `Effect4.Flow.denoteFuel_eq_denote`
that fuel is not binding: the right-hand side is the fuel-free `Flow.denote`. -/
theorem skeletonDispatch_denote (rows : ServiceRow) (program : FlowProgram) (tape : Tape)
    (input : Val) {nodes : List Skeleton}
    (built : Flow.skeletonDispatch rows program = some nodes) :
    Skeleton.denote (tableAlphabet ⟨0⟩ program.table)
        (fuelFor program.flow.erase tape) program.param.1 nodes tape input
      = Effect4.Flow.denote program.flow tape input := by
  have wf : FlowWF (tableAlphabet ⟨0⟩ program.table) program.flow.erase := erase_wf program.flow
  simp only [Flow.skeletonDispatch, Option.bind_eq_bind] at built
  obtain ⟨cases, lowered, shaped⟩ := Option.bind_eq_some_iff.mp built
  obtain rfl : Flow.acquisitions rows program.table program.flow.erase
      ++ Flow.declarations program.flow.erase.blocks
      ++ [ Skeleton.assign (.param program.flow.erase.entry 0) (.input program.param.1)
         , Skeleton.letBlockIndex "block" program.flow.erase.entry
         , Lowering.dispatchLoop cases ] = nodes := Option.some.inj shaped
  have entry := wf.entry
  unfold EntryWF at entry
  cases found : lookupBlock program.flow.erase program.flow.erase.entry with
  | none => rw [found] at entry; exact entry.elim
  | some current =>
      rw [found] at entry
      have sized : ([input] : Env).length = current.params.length := by rw [entry]; rfl
      rw [Skeleton.denote, denoteNodes,
        execList_dispatchPrefix rows program.table program.flow.erase _ tape program.param.1
          input cases, Program.bind_assoc]
      show Program.bind (dispatchRun (tableAlphabet ⟨0⟩ program.table)
          (fuelFor program.flow.erase tape)
          (((start program.param.1 input).setVal (.param program.flow.erase.entry 0) input).setIndex
            "block" program.flow.erase.entry.value) tape "block" cases)
          (fun result => Program.pure (result.1, result.2)) = _
      rw [Program.bind_pure_right]
      rw [dispatchRun_denoteFuel program.table program.flow.erase wf cases
        (fun index cur resolved =>
          caseBody?_of_mapM program.table
            (fun block => (Flow.skeletonBlock program.table block).bind fun body =>
              pure (Lowering.blockCase block.id body))
            (fun b => by cases Flow.skeletonBlock program.table b <;> rfl)
            program.flow.erase.blocks cases lowered index cur resolved)
        (fuelFor program.flow.erase tape) _ tape program.flow.erase.entry [input] current found
        sized (setIndex_same _ _ _) ?_]
      · exact denoteFuel_eq_denote program.flow tape input (Nat.le_refl _)
      · intro i lt
        simp only [List.length_singleton] at lt
        obtain rfl : i = 0 := by omega
        rw [setIndex_vals, setVal_self]
        rfl

end Effect4.Target.EffectV4
