import Effect4.Machine.Exit

/-!
# Runtime.Scope.lean

Owner: Scopes, finalizer registration, and close semantics.

This module implements the first-order `Scope` state machine of
`effect@4.0.0-rc.112`: the two-value finalizer-strategy label, the five-arm
scope state whose three `open*` constructors are the three inhabited shapes of
rc.112's one `Open` record, the keyed insertion-ordered finalizer table with
`Map.set`/`Map.delete` semantics, registration and registration-after-close,
removal, the state-first LIFO idempotent close with its three result arms, fork
linkage at the shape level, and the scope-side clauses of `scoped` and
`acquireRelease`.

A finalizer is a nominal `φ`, never a stored Lean closure: `docs/DESIGN-BASIS.md`
DB-02 forbids closures in canonical program content. What a finalizer *does* is
supplied to the closing operations as the argument
`run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α`, so a `Scope` keeps decidable
equality and kernel-reducible ground receipts. `Effect4.Exit` and
`Effect4.Cause` are reused unchanged; this module mints no second exit or cause
carrier and imports only `Effect4.Semantics.Exit`.

Pinned source: `vendor/effect-4.0.0-rc.112/src/Scope.ts` 99-187 and
`internal/effect.ts` 3769-3922 and 3937-3987. The frozen surface is
`test/contracts/scope.contract.md`, held by the battery
`Test/Runtime/ScopeContract.lean` and the axiom report
`Test/Runtime/ScopeAxiomReport.lean`. The proof graph is
`docs/SCOPE-DAG.md`.
-/

namespace Effect4

universe u v

/-- rc.112's `"sequential" | "parallel"` close label. It carries no scheduler
payload: `docs/SCOPE-DAG.md` separation 7 records why. -/
inductive FinalizerStrategy
  /-- Finalizers are awaited one after another. -/
  | sequential
  /-- Finalizers are forked immediately and awaited together. -/
  | parallel
deriving DecidableEq, Repr

namespace FinalizerStrategy

/-- Every strategy label, in declaration order. census: scope.make -/
def all : List FinalizerStrategy := [sequential, parallel]

/-- The strategy enumeration lists no label twice. census: scope.make -/
theorem all_nodup : all.Nodup := by decide

/-- The strategy enumeration is complete. census: scope.make -/
theorem mem_all (strategy : FinalizerStrategy) : strategy ∈ all := by
  cases strategy <;> decide

/-- There is no third close strategy. census: scope.close-parallel -/
theorem cases_receipt (strategy : FinalizerStrategy) :
    strategy = sequential \/ strategy = parallel := by
  cases strategy
  · exact Or.inl rfl
  · exact Or.inr rfl

end FinalizerStrategy

/-- The scope state machine. rc.112's `Empty | Open | Closed`, with the three
inhabited shapes of the one `Open` record split into three constructors so the
record's XOR invariant is unconstructible-otherwise rather than checked.
`openEmpty` and `openMap []` are deliberately not identified. -/
inductive ScopeState (κ φ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- A fresh scope, before any registration: the only pre-`Open` state. -/
  | empty
  /-- An `Open` scope whose inline slot was cleared and which has no map. -/
  | openEmpty
  /-- An `Open` scope holding exactly one inline finalizer under its key. -/
  | openInline (key : κ) (finalizer : φ)
  /-- An `Open` scope holding a keyed insertion-ordered finalizer map. -/
  | openMap (entries : List (κ × φ))
  /-- A closed scope, carrying the exit it was closed with. -/
  | closed (exit : Exit β ε δ ι α)
deriving DecidableEq

/-- A scope: its close strategy and its state. rc.112's type-id brands and the
`Closeable` close method are host tagging and are not modelled. -/
structure Scope (κ φ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  /-- The label chosen at `scopeMakeUnsafe`. -/
  strategy : FinalizerStrategy
  /-- The current state of the scope's lifetime. -/
  state : ScopeState κ φ β ε δ ι α
deriving DecidableEq

variable {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}

namespace ScopeState

/-- The materialised registration order of a state. census: scope.states -/
def entries : ScopeState κ φ β ε δ ι α -> List (κ × φ)
  | empty => []
  | openEmpty => []
  | openInline key finalizer => [(key, finalizer)]
  | openMap table => table
  | closed _ => []

/-- Whether the state is one of the three `Open` shapes. census: scope.states -/
def isOpen : ScopeState κ φ β ε δ ι α -> Bool
  | empty => false
  | openEmpty => true
  | openInline _ _ => true
  | openMap _ => true
  | closed _ => false

/-- Whether the state is `Closed`. census: scope.states -/
def isClosed : ScopeState κ φ β ε δ ι α -> Bool
  | closed _ => true
  | empty => false
  | openEmpty => false
  | openInline _ _ => false
  | openMap _ => false

/-- The exit a closed state was closed with. census: scope.states -/
def closingExit? : ScopeState κ φ β ε δ ι α -> Option (Exit β ε δ ι α)
  | closed exit => some exit
  | empty => none
  | openEmpty => none
  | openInline _ _ => none
  | openMap _ => none

/-- There is no sixth scope state. census: scope.states -/
theorem cases_receipt (state : ScopeState κ φ β ε δ ι α) :
    state = empty \/
      state = openEmpty \/
        (exists key finalizer, state = openInline key finalizer) \/
          (exists table, state = openMap table) \/
            (exists exit, state = closed exit) := by
  cases state with
  | empty => exact Or.inl rfl
  | openEmpty => exact Or.inr (Or.inl rfl)
  | openInline key finalizer => exact Or.inr (Or.inr (Or.inl ⟨key, finalizer, rfl⟩))
  | openMap table => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨table, rfl⟩)))
  | closed exit => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨exit, rfl⟩)))

/-- A fresh scope has registered nothing. census: scope.states -/
theorem entries_empty : (empty : ScopeState κ φ β ε δ ι α).entries = [] := rfl

/-- A cleared inline slot has registered nothing. census: scope.states -/
theorem entries_openEmpty : (openEmpty : ScopeState κ φ β ε δ ι α).entries = [] := rfl

/-- An inline slot is one registration. census: scope.states -/
theorem entries_openInline (key : κ) (finalizer : φ) :
    (openInline key finalizer : ScopeState κ φ β ε δ ι α).entries = [(key, finalizer)] := rfl

/-- A map is its own insertion-ordered registration list. census: scope.states -/
theorem entries_openMap (table : List (κ × φ)) :
    (openMap table : ScopeState κ φ β ε δ ι α).entries = table := rfl

/-- A closed state has no registration left. census: scope.states -/
theorem entries_closed (exit : Exit β ε δ ι α) :
    (closed exit : ScopeState κ φ β ε δ ι α).entries = [] := rfl

/-- `Empty` is not `Open`. census: scope.states -/
theorem isOpen_empty : (empty : ScopeState κ φ β ε δ ι α).isOpen = false := rfl

/-- A cleared inline slot is still `Open`. census: scope.states -/
theorem isOpen_openEmpty : (openEmpty : ScopeState κ φ β ε δ ι α).isOpen = true := rfl

/-- An inline slot is `Open`. census: scope.states -/
theorem isOpen_openInline (key : κ) (finalizer : φ) :
    (openInline key finalizer : ScopeState κ φ β ε δ ι α).isOpen = true := rfl

/-- A map is `Open`. census: scope.states -/
theorem isOpen_openMap (table : List (κ × φ)) :
    (openMap table : ScopeState κ φ β ε δ ι α).isOpen = true := rfl

/-- `Closed` is not `Open`. census: scope.states -/
theorem isOpen_closed (exit : Exit β ε δ ι α) :
    (closed exit : ScopeState κ φ β ε δ ι α).isOpen = false := rfl

/-- Exactly the `closed` states report closed. census: scope.states -/
theorem isClosed_eq (state : ScopeState κ φ β ε δ ι α) :
    state.isClosed = true <-> exists exit, state = closed exit := by
  constructor
  · intro h
    cases state with
    | closed exit => exact ⟨exit, rfl⟩
    | empty => exact Bool.noConfusion h
    | openEmpty => exact Bool.noConfusion h
    | openInline _ _ => exact Bool.noConfusion h
    | openMap _ => exact Bool.noConfusion h
  · intro h
    obtain ⟨exit, hexit⟩ := h
    rw [hexit]
    rfl

/-- A closed state carries the exit it was closed with. census: scope.states -/
theorem closingExit_closed (exit : Exit β ε δ ι α) :
    (closed exit : ScopeState κ φ β ε δ ι α).closingExit? = some exit := rfl

/-- Only a closed state carries a closing exit. census: scope.states -/
theorem closingExit_of_not_closed (state : ScopeState κ φ β ε δ ι α)
    (h : state.isClosed = false) : state.closingExit? = none := by
  cases state with
  | empty => rfl
  | openEmpty => rfl
  | openInline _ _ => rfl
  | openMap _ => rfl
  | closed _ => exact Bool.noConfusion h

/-- A cleared inline slot is not the empty map: the next add lands inline in the
first case and in the map in the second. census: scope.states -/
theorem openEmpty_ne_openMap_nil :
    (openEmpty : ScopeState κ φ β ε δ ι α) ≠ openMap [] := by
  intro h
  nomatch h

/-- A non-`Open` state has registered nothing. -/
private theorem entries_of_not_isOpen (state : ScopeState κ φ β ε δ ι α)
    (h : state.isOpen = false) : state.entries = [] := by
  cases state with
  | empty => rfl
  | closed _ => rfl
  | openEmpty => exact Bool.noConfusion h
  | openInline _ _ => exact Bool.noConfusion h
  | openMap _ => exact Bool.noConfusion h

/-- A closed state has registered nothing. -/
private theorem entries_of_isClosed (state : ScopeState κ φ β ε δ ι α)
    (h : state.isClosed = true) : state.entries = [] := by
  cases state with
  | closed _ => rfl
  | empty => exact Bool.noConfusion h
  | openEmpty => exact Bool.noConfusion h
  | openInline _ _ => exact Bool.noConfusion h
  | openMap _ => exact Bool.noConfusion h

end ScopeState

namespace Scope

/-- rc.112 `scopeMakeUnsafe`: a new scope starts `Empty`. census: scope.make -/
def make (strategy : FinalizerStrategy) : Scope κ φ β ε δ ι α where
  strategy := strategy
  state := ScopeState.empty

/-- rc.112 `scopeMakeUnsafe()` with no argument: the sequential default.
census: scope.make -/
def makeDefault : Scope κ φ β ε δ ι α := make FinalizerStrategy.sequential

/-- The scope's materialised registration order. census: scope.states -/
def finalizers (self : Scope κ φ β ε δ ι α) : List (κ × φ) := self.state.entries

/-- The registered finalizer keys, in registration order. census: scope.states -/
def finalizerKeys (self : Scope κ φ β ε δ ι α) : List κ := self.finalizers.map Prod.fst

/-- rc.112 `scopeFinalizerCountUnsafe`. census: scope.states -/
def finalizerCount (self : Scope κ φ β ε δ ι α) : Nat := self.finalizers.length

/-- Whether the scope is in one of the three `Open` shapes. census: scope.states -/
def isOpen (self : Scope κ φ β ε δ ι α) : Bool := self.state.isOpen

/-- Whether the scope has closed. census: scope.states -/
def isClosed (self : Scope κ φ β ε δ ι α) : Bool := self.state.isClosed

/-- The exit a closed scope was closed with. census: scope.states -/
def closingExit? (self : Scope κ φ β ε δ ι α) : Option (Exit β ε δ ι α) :=
  self.state.closingExit?

/-- A scope reported not closed is not `Closed`. -/
private theorem not_isClosed {self : Scope κ φ β ε δ ι α} (h : self.isClosed = false) :
    ¬ (self.isClosed = true) := by
  intro hTrue
  rw [h] at hTrue
  exact Bool.noConfusion hTrue

/-- A new scope carries the strategy it was made with. census: scope.make -/
theorem make_strategy (strategy : FinalizerStrategy) :
    (make strategy : Scope κ φ β ε δ ι α).strategy = strategy := rfl

/-- A new scope starts `Empty`. census: scope.make -/
theorem make_state (strategy : FinalizerStrategy) :
    (make strategy : Scope κ φ β ε δ ι α).state = ScopeState.empty := rfl

/-- A new scope has registered nothing. census: scope.make -/
theorem make_finalizers (strategy : FinalizerStrategy) :
    (make strategy : Scope κ φ β ε δ ι α).finalizers = [] := rfl

/-- The default scope is the sequential one. census: scope.make -/
theorem makeDefault_eq :
    (makeDefault : Scope κ φ β ε δ ι α) = make FinalizerStrategy.sequential := rfl

/-- The default strategy is sequential. census: scope.make -/
theorem makeDefault_strategy :
    (makeDefault : Scope κ φ β ε δ ι α).strategy = FinalizerStrategy.sequential := rfl

/-- A scope's registrations are its state's. census: scope.states -/
theorem finalizers_eq (self : Scope κ φ β ε δ ι α) : self.finalizers = self.state.entries := rfl

/-- The keys are the registrations' first components. census: scope.states -/
theorem finalizerKeys_eq (self : Scope κ φ β ε δ ι α) :
    self.finalizerKeys = self.finalizers.map Prod.fst := rfl

/-- The count is the registration list's length. census: scope.states -/
theorem finalizerCount_eq (self : Scope κ φ β ε δ ι α) :
    self.finalizerCount = self.finalizers.length := rfl

/-- rc.112 `scopeFinalizerCountUnsafe` answers zero for every non-`Open` scope.
census: scope.states -/
theorem finalizerCount_not_open (self : Scope κ φ β ε δ ι α) (h : self.isOpen = false) :
    self.finalizerCount = 0 := by
  show self.state.entries.length = 0
  rw [ScopeState.entries_of_not_isOpen self.state h]
  rfl

/-- The rc.112 `{}` key freshness is refused, not modelled: an Effect4 key is a
value, so no minting function can distinguish two structurally equal keys.
Sibling of `Effect4.Reason.host_memory_refused`; boundary
`SCOPE-FB-KEY-IDENTITY`. census: scope.add-finalizer -/
theorem key_freshness_refused {γ : Type u} (mint : γ -> κ) (left right : γ)
    (h : left = right) : mint left = mint right :=
  congrArg mint h

/-! ### The keyed insertion-ordered finalizer table -/

/-- JavaScript `Map.prototype.set`: an existing key keeps its slot and only its
value changes; a new key is appended. census: scope.add-finalizer -/
def tableInsert [DecidableEq κ] (table : List (κ × φ)) (key : κ) (finalizer : φ) :
    List (κ × φ) :=
  if table.any (fun entry => decide (entry.fst = key)) then
    table.map (fun entry => if entry.fst = key then (key, finalizer) else entry)
  else
    table ++ [(key, finalizer)]

/-- JavaScript `Map.prototype.delete`. census: scope.remove-finalizer -/
def tableRemove [DecidableEq κ] (table : List (κ × φ)) (key : κ) : List (κ × φ) :=
  table.filter (fun entry => decide (entry.fst ≠ key))

/-- A registered key is found by the `any` scan. -/
private theorem any_of_mem_keys [DecidableEq κ] {table : List (κ × φ)} {key : κ}
    (h : key ∈ table.map Prod.fst) :
    table.any (fun entry => decide (entry.fst = key)) = true := by
  obtain ⟨entry, hmem, heq⟩ := List.mem_map.mp h
  exact List.any_eq_true.mpr ⟨entry, hmem, decide_eq_true heq⟩

/-- An unregistered key is not found by the `any` scan. -/
private theorem any_of_not_mem_keys [DecidableEq κ] {table : List (κ × φ)} {key : κ}
    (h : key ∉ table.map Prod.fst) :
    table.any (fun entry => decide (entry.fst = key)) = false := by
  rw [Bool.eq_false_iff]
  intro hany
  obtain ⟨entry, hmem, hp⟩ := List.any_eq_true.mp hany
  exact h (List.mem_map.mpr ⟨entry, hmem, of_decide_eq_true hp⟩)

/-- In-place replacement does not move a key. -/
private theorem map_fst_replace [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (finalizer : φ) :
    (table.map (fun entry => if entry.fst = key then (key, finalizer) else entry)).map
        Prod.fst =
      table.map Prod.fst := by
  induction table with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]
    by_cases hhead : head.fst = key
    · rw [if_pos hhead, hhead]
    · rw [if_neg hhead]

/-- A new key is appended. census: scope.add-finalizer -/
theorem tableInsert_new [DecidableEq κ] (table : List (κ × φ)) (key : κ) (finalizer : φ)
    (h : key ∉ table.map Prod.fst) :
    tableInsert table key finalizer = table ++ [(key, finalizer)] := by
  show (if table.any (fun entry => decide (entry.fst = key)) then _ else _) = _
  rw [any_of_not_mem_keys h]
  rfl

/-- An existing key keeps its slot and only its value changes.
census: scope.add-finalizer -/
theorem tableInsert_existing [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (finalizer : φ) (h : key ∈ table.map Prod.fst) :
    tableInsert table key finalizer =
      table.map (fun entry => if entry.fst = key then (key, finalizer) else entry) := by
  show (if table.any (fun entry => decide (entry.fst = key)) then _ else _) = _
  rw [any_of_mem_keys h]
  rfl

/-- Replacing a stored value preserves the key list exactly.
census: scope.add-finalizer -/
theorem tableInsert_keys_of_mem [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (finalizer : φ) (h : key ∈ table.map Prod.fst) :
    (tableInsert table key finalizer).map Prod.fst = table.map Prod.fst := by
  rw [tableInsert_existing table key finalizer h, map_fst_replace]

/-- The inserted key is registered. -/
private theorem tableInsert_mem_keys [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (finalizer : φ) : key ∈ (tableInsert table key finalizer).map Prod.fst := by
  by_cases hmem : key ∈ table.map Prod.fst
  · rw [tableInsert_keys_of_mem table key finalizer hmem]
    exact hmem
  · rw [tableInsert_new table key finalizer hmem, List.map_append]
    exact List.mem_append_right _ (List.mem_singleton_self key)

/-- A one-key list is duplicate-free. -/
private theorem nodup_singleton {γ : Type u} (value : γ) : ([value] : List γ).Nodup :=
  List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- A duplicate-free key list stays duplicate-free. census: scope.add-finalizer -/
theorem tableInsert_nodup [DecidableEq κ] (table : List (κ × φ)) (key : κ) (finalizer : φ)
    (h : (table.map Prod.fst).Nodup) :
    ((tableInsert table key finalizer).map Prod.fst).Nodup := by
  by_cases hmem : key ∈ table.map Prod.fst
  · rw [tableInsert_keys_of_mem table key finalizer hmem]
    exact h
  · rw [tableInsert_new table key finalizer hmem, List.map_append]
    show (table.map Prod.fst ++ [key]).Nodup
    refine List.nodup_append.mpr ⟨h, nodup_singleton key, ?_⟩
    intro left hleft right hright hcontra
    rw [List.mem_singleton] at hright
    exact hmem (by rw [← hright, ← hcontra]; exact hleft)

/-- Removal is the `Map.delete` filter. census: scope.remove-finalizer -/
theorem tableRemove_eq [DecidableEq κ] (table : List (κ × φ)) (key : κ) :
    tableRemove table key = table.filter (fun entry => decide (entry.fst ≠ key)) := rfl

/-- The removed key is gone. census: scope.remove-finalizer -/
theorem tableRemove_keys [DecidableEq κ] (table : List (κ × φ)) (key : κ) :
    key ∉ (tableRemove table key).map Prod.fst := by
  intro hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  have hkeep := (List.mem_filter.mp hentry).right
  simp only [decide_eq_true_eq] at hkeep
  exact hkeep heq

/-- Removal preserves key duplicate-freedom. census: scope.remove-finalizer -/
theorem tableRemove_nodup [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (h : (table.map Prod.fst).Nodup) :
    ((tableRemove table key).map Prod.fst).Nodup :=
  List.Pairwise.sublist (List.Sublist.map Prod.fst List.filter_sublist) h

/-- Removing an unregistered key changes nothing. -/
private theorem tableRemove_of_not_mem [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (h : key ∉ table.map Prod.fst) :
    table.filter (fun entry => decide (entry.fst ≠ key)) = table := by
  induction table with
  | nil => rfl
  | cons head tail ih =>
    have hhead : head.fst ≠ key := by
      intro heq
      exact h (List.mem_map.mpr ⟨head, List.mem_cons_self, heq⟩)
    have htail : key ∉ tail.map Prod.fst := by
      intro hmem
      exact h (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hmem)
    rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hhead), ih htail]

/-- Removing a freshly appended key restores the table. -/
private theorem tableRemove_append_self [DecidableEq κ] (table : List (κ × φ)) (key : κ)
    (finalizer : φ) (h : key ∉ table.map Prod.fst) :
    tableRemove (table ++ [(key, finalizer)]) key = table := by
  show List.filter (fun entry => decide (entry.fst ≠ key)) (table ++ [(key, finalizer)]) = _
  rw [List.filter_append, tableRemove_of_not_mem table key h,
    List.filter_cons_of_neg (by
      intro hcontra
      simp only [decide_eq_true_eq] at hcontra
      exact hcontra rfl)]
  rw [List.filter_nil, List.append_nil]

/-! ### Registration -/

/-- rc.112 `scopeAddFinalizerUnsafe` at the state level: the first add takes the
inline slot, the second promotes both into a map, and a `Closed` state has no
arm at all. -/
private def addState [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) : ScopeState κ φ β ε δ ι α :=
  match state with
  | .empty => .openInline key finalizer
  | .openEmpty => .openInline key finalizer
  | .openInline existingKey existing =>
    .openMap (tableInsert [(existingKey, existing)] key finalizer)
  | .openMap table => .openMap (tableInsert table key finalizer)
  | .closed exit => .closed exit

/-- rc.112 `scopeAddFinalizerUnsafe`. census: scope.add-finalizer -/
def addUnsafe [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ) :
    Scope κ φ β ε δ ι α where
  strategy := self.strategy
  state := addState self.state key finalizer

/-- Registration does not change the close strategy. census: scope.add-finalizer -/
theorem addUnsafe_strategy [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) : (self.addUnsafe key finalizer).strategy = self.strategy := rfl

/-- The first add stores an inline finalizer and its key. census: scope.add-finalizer -/
theorem addUnsafe_empty [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (h : self.state = ScopeState.empty) :
    (self.addUnsafe key finalizer).state = ScopeState.openInline key finalizer := by
  show addState self.state key finalizer = _
  rw [h]
  rfl

/-- A cleared inline slot takes the next add inline again, not into a map.
census: scope.add-finalizer -/
theorem addUnsafe_openEmpty [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (h : self.state = ScopeState.openEmpty) :
    (self.addUnsafe key finalizer).state = ScopeState.openInline key finalizer := by
  show addState self.state key finalizer = _
  rw [h]
  rfl

/-- The second add promotes both into a map. census: scope.add-finalizer -/
theorem addUnsafe_openInline [DecidableEq κ] (self : Scope κ φ β ε δ ι α)
    (existingKey key : κ) (existing finalizer : φ)
    (h : self.state = ScopeState.openInline existingKey existing) :
    (self.addUnsafe key finalizer).state =
      ScopeState.openMap (tableInsert [(existingKey, existing)] key finalizer) := by
  show addState self.state key finalizer = _
  rw [h]
  rfl

/-- A further add is a `Map.set`. census: scope.add-finalizer -/
theorem addUnsafe_openMap [DecidableEq κ] (self : Scope κ φ β ε δ ι α)
    (table : List (κ × φ)) (key : κ) (finalizer : φ)
    (h : self.state = ScopeState.openMap table) :
    (self.addUnsafe key finalizer).state =
      ScopeState.openMap (tableInsert table key finalizer) := by
  show addState self.state key finalizer = _
  rw [h]
  rfl

/-- rc.112 `scopeAddFinalizerUnsafe` has no `Closed` arm: it falls through.
census: scope.add-after-closed -/
theorem addUnsafe_closed [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (h : self.isClosed = true) : self.addUnsafe key finalizer = self := by
  cases self with
  | mk strategy state =>
    obtain ⟨exit, hstate⟩ := (ScopeState.isClosed_eq state).mp h
    rw [hstate]
    rfl

/-- The promotion preserves insertion order. census: scope.add-finalizer -/
theorem addUnsafe_promotes [DecidableEq κ] (self : Scope κ φ β ε δ ι α)
    (existingKey key : κ) (existing finalizer : φ)
    (h : self.state = ScopeState.openInline existingKey existing) (hne : existingKey ≠ key) :
    (self.addUnsafe key finalizer).finalizers =
      [(existingKey, existing), (key, finalizer)] := by
  have hkeys : key ∉ ([(existingKey, existing)] : List (κ × φ)).map Prod.fst := by
    intro hmem
    rw [List.map_cons, List.map_nil, List.mem_singleton] at hmem
    exact hne hmem.symm
  show (addState self.state key finalizer).entries = _
  rw [h]
  show tableInsert [(existingKey, existing)] key finalizer = _
  rw [tableInsert_new _ _ _ hkeys]
  rfl

/-- Registration appends, in every open shape. -/
private theorem addState_entries [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α)
    (key : κ) (finalizer : φ) (hclosed : state.isClosed = false)
    (hkey : key ∉ state.entries.map Prod.fst) :
    (addState state key finalizer).entries = state.entries ++ [(key, finalizer)] := by
  cases state with
  | empty => rfl
  | openEmpty => rfl
  | openInline existingKey existing =>
    show tableInsert [(existingKey, existing)] key finalizer = _
    rw [tableInsert_new [(existingKey, existing)] key finalizer hkey]
    rfl
  | openMap table =>
    show tableInsert table key finalizer = _
    rw [tableInsert_new table key finalizer hkey]
    rfl
  | closed _ => exact Bool.noConfusion hclosed

/-- Registration does not change whether the scope is closed. -/
private theorem addState_isClosed [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α)
    (key : κ) (finalizer : φ) :
    (addState state key finalizer).isClosed = state.isClosed := by
  cases state <;> rfl

/-- The registered key is registered. -/
private theorem addState_mem_keys [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α)
    (key : κ) (finalizer : φ) (hclosed : state.isClosed = false) :
    key ∈ (addState state key finalizer).entries.map Prod.fst := by
  cases state with
  | empty => exact List.mem_singleton_self key
  | openEmpty => exact List.mem_singleton_self key
  | openInline existingKey existing => exact tableInsert_mem_keys _ _ _
  | openMap table => exact tableInsert_mem_keys _ _ _
  | closed _ => exact Bool.noConfusion hclosed

/-- Registration preserves key duplicate-freedom. -/
private theorem addState_keys_nodup [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α)
    (key : κ) (finalizer : φ) (h : (state.entries.map Prod.fst).Nodup) :
    ((addState state key finalizer).entries.map Prod.fst).Nodup := by
  cases state with
  | empty => exact nodup_singleton key
  | openEmpty => exact nodup_singleton key
  | openInline existingKey existing => exact tableInsert_nodup _ _ _ h
  | openMap table => exact tableInsert_nodup _ _ _ h
  | closed _ => exact h

/-- Registration appends to the registration list. census: scope.add-finalizer -/
theorem addUnsafe_finalizers [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (hclosed : self.isClosed = false) (hkey : key ∉ self.finalizerKeys) :
    (self.addUnsafe key finalizer).finalizers = self.finalizers ++ [(key, finalizer)] :=
  addState_entries self.state key finalizer hclosed hkey

/-- Registration preserves key duplicate-freedom. census: scope.add-finalizer -/
theorem addUnsafe_keys_nodup [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (h : self.finalizerKeys.Nodup) :
    (self.addUnsafe key finalizer).finalizerKeys.Nodup :=
  addState_keys_nodup self.state key finalizer h

/-- rc.112 `scopeAddFinalizerExit`: register while open, run now when closed.
census: scope.add-after-closed -/
def addExit [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ) :
    Scope κ φ β ε δ ι α × Exit Unit ε δ ι α :=
  match self.closingExit? with
  | some exit => (self, run finalizer exit)
  | none => (self.addUnsafe key finalizer, Exit.void)

/-- An open scope records the finalizer and reports success.
census: scope.add-after-closed -/
theorem addExit_open [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ) (h : self.isClosed = false) :
    addExit run self key finalizer = (self.addUnsafe key finalizer, Exit.void) := by
  have hc : self.closingExit? = none := ScopeState.closingExit_of_not_closed self.state h
  show (match self.closingExit? with
    | some exit => (self, run finalizer exit)
    | none => (self.addUnsafe key finalizer, Exit.void)) = _
  rw [hc]

/-- A closed scope runs the finalizer immediately with the stored closing exit.
census: scope.add-after-closed -/
theorem addExit_closed [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ) (exit : Exit β ε δ ι α)
    (h : self.state = ScopeState.closed exit) :
    addExit run self key finalizer = (self, run finalizer exit) := by
  have hc : self.closingExit? = some exit := by
    show self.state.closingExit? = some exit
    rw [h]
    rfl
  show (match self.closingExit? with
    | some closing => (self, run finalizer closing)
    | none => (self.addUnsafe key finalizer, Exit.void)) = _
  rw [hc]

/-- A closed scope's registration list never grows. census: scope.add-after-closed -/
theorem addExit_closed_registers_nothing [DecidableEq κ]
    (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (exit : Exit β ε δ ι α) (h : self.state = ScopeState.closed exit) :
    (addExit run self key finalizer).fst.finalizers = [] := by
  rw [addExit_closed run self key finalizer exit h]
  show self.state.entries = []
  rw [h]
  rfl

/-! ### Removal -/

/-- rc.112 `scopeRemoveFinalizerUnsafe` at the state level: clear the inline slot
on a key match, otherwise delete from the map, and leave a non-`Open` state
untouched. -/
private def removeState [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α) (key : κ) :
    ScopeState κ φ β ε δ ι α :=
  match state with
  | .openInline existingKey existing =>
    if existingKey = key then .openEmpty else .openInline existingKey existing
  | .openMap table => .openMap (tableRemove table key)
  | .empty => .empty
  | .openEmpty => .openEmpty
  | .closed exit => .closed exit

/-- rc.112 `scopeRemoveFinalizerUnsafe`. census: scope.remove-finalizer -/
def removeUnsafe [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ) :
    Scope κ φ β ε δ ι α where
  strategy := self.strategy
  state := removeState self.state key

/-- Removal does not change the close strategy. census: scope.remove-finalizer -/
theorem removeUnsafe_strategy [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ) :
    (self.removeUnsafe key).strategy = self.strategy := rfl

/-- The inline slot is cleared when the key matches. census: scope.remove-finalizer -/
theorem removeUnsafe_inline_hit [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (finalizer : φ) (h : self.state = ScopeState.openInline key finalizer) :
    (self.removeUnsafe key).state = ScopeState.openEmpty := by
  show removeState self.state key = _
  rw [h]
  show (if key = key then ScopeState.openEmpty
    else ScopeState.openInline key finalizer) = _
  rw [if_pos (rfl : key = key)]

/-- An inline slot under a different key is untouched: there is no map to delete
from. census: scope.remove-finalizer -/
theorem removeUnsafe_inline_miss [DecidableEq κ] (self : Scope κ φ β ε δ ι α)
    (existingKey key : κ) (finalizer : φ)
    (h : self.state = ScopeState.openInline existingKey finalizer)
    (hne : existingKey ≠ key) : self.removeUnsafe key = self := by
  cases self with
  | mk strategy state =>
    show (Scope.mk strategy (removeState state key) : Scope κ φ β ε δ ι α) = _
    rw [show state = ScopeState.openInline existingKey finalizer from h]
    show (Scope.mk strategy
      (if existingKey = key then ScopeState.openEmpty
        else ScopeState.openInline existingKey finalizer) : Scope κ φ β ε δ ι α) = _
    rw [if_neg hne]

/-- A map deletion is `Map.delete`. census: scope.remove-finalizer -/
theorem removeUnsafe_openMap [DecidableEq κ] (self : Scope κ φ β ε δ ι α)
    (table : List (κ × φ)) (key : κ) (h : self.state = ScopeState.openMap table) :
    (self.removeUnsafe key).state = ScopeState.openMap (tableRemove table key) := by
  show removeState self.state key = _
  rw [h]
  rfl

/-- A non-`Open` scope is left untouched: removal never resurrects it.
census: scope.remove-finalizer -/
theorem removeUnsafe_not_open [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (h : self.isOpen = false) : self.removeUnsafe key = self := by
  cases self with
  | mk strategy state =>
    cases state with
    | empty => rfl
    | closed _ => rfl
    | openEmpty => exact Bool.noConfusion h
    | openInline _ _ => exact Bool.noConfusion h
    | openMap _ => exact Bool.noConfusion h

/-- The removed key is gone. census: scope.remove-finalizer -/
theorem removeUnsafe_keys [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ) :
    key ∉ (self.removeUnsafe key).finalizerKeys := by
  show key ∉ (removeState self.state key).entries.map Prod.fst
  cases self.state with
  | empty => exact List.not_mem_nil
  | openEmpty => exact List.not_mem_nil
  | closed _ => exact List.not_mem_nil
  | openMap table => exact tableRemove_keys table key
  | openInline existingKey existing =>
    show key ∉ (if existingKey = key then ScopeState.openEmpty
      else ScopeState.openInline existingKey existing).entries.map Prod.fst
    by_cases hhit : existingKey = key
    · rw [if_pos hhit]
      exact List.not_mem_nil
    · rw [if_neg hhit]
      intro hmem
      rw [ScopeState.entries_openInline, List.map_cons, List.map_nil,
        List.mem_singleton] at hmem
      exact hhit hmem.symm

/-- Removal preserves key duplicate-freedom. census: scope.remove-finalizer -/
theorem removeUnsafe_keys_nodup [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (key : κ)
    (h : self.finalizerKeys.Nodup) : (self.removeUnsafe key).finalizerKeys.Nodup := by
  show ((removeState self.state key).entries.map Prod.fst).Nodup
  cases hstate : self.state with
  | empty => exact List.nodup_nil
  | openEmpty => exact List.nodup_nil
  | closed _ => exact List.nodup_nil
  | openMap table =>
    refine tableRemove_nodup table key ?_
    show (table.map Prod.fst).Nodup
    have hkeys : self.finalizerKeys = table.map Prod.fst := by
      show self.state.entries.map Prod.fst = _
      rw [hstate]
      rfl
    rw [hkeys] at h
    exact h
  | openInline existingKey existing =>
    show ((if existingKey = key then ScopeState.openEmpty
      else ScopeState.openInline existingKey existing).entries.map Prod.fst).Nodup
    by_cases hhit : existingKey = key
    · rw [if_pos hhit]
      exact List.nodup_nil
    · rw [if_neg hhit]
      exact nodup_singleton existingKey

/-! ### Closing -/

/-- The state half of rc.112 `scopeCloseUnsafe`. It takes no `run` at all, so
"state before finalizers" is a theorem and not a promise.
census: scope.close-state-first -/
def closeState (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    Scope κ φ β ε δ ι α :=
  if self.isClosed then self else { strategy := self.strategy, state := ScopeState.closed exit }

/-- The order finalizers are run in: the materialised registration list,
backwards. census: scope.close-lifo -/
def closeOrder (self : Scope κ φ β ε δ ι α) : List φ :=
  (self.finalizers.map Prod.snd).reverse

/-- Every registered finalizer's own exit, in close order. A failing finalizer
does not abort the loop. census: scope.close-sequential -/
def closeExits (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) : List (Exit Unit ε δ ι α) :=
  self.closeOrder.map (fun finalizer => run finalizer exit)

/-- The three arms of rc.112 `scopeCloseUnsafe`: nothing, the single finalizer's
own effect, and the `exitAsVoidAll` merge. census: scope.close-merge -/
def closeResult (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) : Exit Unit ε δ ι α :=
  if self.isClosed then Exit.void
  else
    match closeExits run self exit with
    | [] => Exit.void
    | [only] => only
    | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)

/-- rc.112 `scopeCloseUnsafe`: the state flip paired with the finalizer result.
census: scope.close-state-first -/
def close (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (self : Scope κ φ β ε δ ι α)
    (exit : Exit β ε δ ι α) : Scope κ φ β ε δ ι α × Exit Unit ε δ ι α :=
  (closeState self exit, closeResult run self exit)

/-- Close is exactly its two named phases. census: scope.close-state-first -/
theorem close_eq (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    close run self exit = (closeState self exit, closeResult run self exit) := rfl

/-- State first: the written state cannot depend on what any finalizer does.
census: rule.scope-close-lifo-state-first -/
theorem close_state_independent_of_run
    (leftRun rightRun : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (close leftRun self exit).fst = (close rightRun self exit).fst := rfl

/-- An open scope records the closing exit. census: scope.close-state-first -/
theorem closeState_state (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α)
    (h : self.isClosed = false) :
    (closeState self exit).state = ScopeState.closed exit := by
  show (if self.isClosed then self
    else { strategy := self.strategy, state := ScopeState.closed exit }).state = _
  rw [if_neg (not_isClosed h)]

/-- Closing does not change the close strategy. census: scope.close-state-first -/
theorem closeState_strategy (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (closeState self exit).strategy = self.strategy := by
  show (if self.isClosed then self
    else { strategy := self.strategy, state := ScopeState.closed exit }).strategy = _
  by_cases h : self.isClosed = true
  · rw [if_pos h]
  · rw [if_neg h]

/-- Closing drops the registration list. census: scope.close-state-first -/
theorem closeState_finalizers (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (closeState self exit).finalizers = [] := by
  show (if self.isClosed then self
    else { strategy := self.strategy, state := ScopeState.closed exit }).finalizers = _
  by_cases h : self.isClosed = true
  · rw [if_pos h]
    exact ScopeState.entries_of_isClosed self.state h
  · rw [if_neg h]
    rfl

/-- A closed scope reports closed. census: scope.close-state-first -/
theorem closeState_isClosed (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (closeState self exit).isClosed = true := by
  show (if self.isClosed then self
    else { strategy := self.strategy, state := ScopeState.closed exit }).isClosed = _
  by_cases h : self.isClosed = true
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    rfl

/-- The state flip is idempotent: the first closing exit is kept.
census: scope.close-state-first -/
theorem closeState_idempotent (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α)
    (h : self.isClosed = true) : closeState self exit = self := by
  show (if self.isClosed then self
    else { strategy := self.strategy, state := ScopeState.closed exit }) = _
  rw [if_pos h]

/-- The closed scope carries the exit it was closed with.
census: scope.close-state-first -/
theorem close_closingExit (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α)
    (h : self.isClosed = false) : (closeState self exit).closingExit? = some exit := by
  show (closeState self exit).state.closingExit? = _
  rw [closeState_state self exit h]
  rfl

/-- Closing an already-closed scope returns it without running a finalizer.
census: scope.close-state-first -/
theorem close_idempotent (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) (h : self.isClosed = true) :
    close run self exit = (self, Exit.void) := by
  have hresult : closeResult run self exit = Exit.void := by
    show (if self.isClosed then Exit.void else _) = _
    rw [if_pos h]
  show (closeState self exit, closeResult run self exit) = _
  rw [closeState_idempotent self exit h, hresult]

/-- A second close runs nothing. census: scope.close-state-first -/
theorem close_twice (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (first second : Exit β ε δ ι α) :
    close run (close run self first).fst second = ((close run self first).fst, Exit.void) :=
  close_idempotent run (close run self first).fst second (closeState_isClosed self first)

/-- The sharp form of "state before finalizers": a finalizer that re-enters the
scope while it closes sees a `Closed` scope, so its own registration runs
immediately with the closing exit rather than being recorded.
census: rule.scope-close-lifo-state-first -/
theorem close_reentrant_add [DecidableEq κ]
    (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (self : Scope κ φ β ε δ ι α)
    (exit : Exit β ε δ ι α) (key : κ) (finalizer : φ) (h : self.isClosed = false) :
    addExit run (closeState self exit) key finalizer =
      (closeState self exit, run finalizer exit) :=
  addExit_closed run (closeState self exit) key finalizer exit (closeState_state self exit h)

/-- Finalizers are materialised in insertion order and iterated backwards.
census: scope.close-lifo -/
theorem closeOrder_eq (self : Scope κ φ β ε δ ι α) :
    self.closeOrder = (self.finalizers.map Prod.snd).reverse := rfl

/-- Whatever was registered last runs first. census: scope.close-lifo -/
theorem closeOrder_last_first (self : Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ)
    (finalizer : φ) (h : self.finalizers = table ++ [(key, finalizer)]) :
    self.closeOrder = finalizer :: (table.map Prod.snd).reverse := by
  show (self.finalizers.map Prod.snd).reverse = _
  rw [h, List.map_append, List.reverse_append]
  rfl

/-- Each finalizer is run against the closing exit, in close order.
census: scope.close-sequential -/
theorem closeExits_eq (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    closeExits run self exit = self.closeOrder.map (fun finalizer => run finalizer exit) :=
  rfl

/-- The close loop is the backwards `Array.from(finalizers.values())` walk.
census: scope.close-lifo -/
theorem closeExits_reverse (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    closeExits run self exit = self.finalizers.reverse.map (fun entry => run entry.snd exit) := by
  show ((self.finalizers.map Prod.snd).reverse).map (fun finalizer => run finalizer exit) = _
  rw [← List.map_reverse, List.map_map]
  rfl

/-- Every registered finalizer contributes an exit: a failing one does not abort
the close. census: scope.close-sequential -/
theorem closeExits_length (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (closeExits run self exit).length = self.finalizers.length := by
  show (((self.finalizers.map Prod.snd).reverse).map
    (fun finalizer => run finalizer exit)).length = _
  rw [List.length_map, List.length_reverse, List.length_map]

/-- No finalizer, nothing to report. census: scope.close-merge -/
theorem closeResult_nil (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) (h : self.finalizers = []) :
    closeResult run self exit = Exit.void := by
  have hexits : closeExits run self exit = [] := by
    show ((self.finalizers.map Prod.snd).reverse).map (fun finalizer => run finalizer exit) = _
    rw [h]
    rfl
  show (if self.isClosed then Exit.void
    else match closeExits run self exit with
      | [] => Exit.void
      | [only] => only
      | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)) = _
  by_cases hclosed : self.isClosed = true
  · rw [if_pos hclosed]
  · rw [if_neg hclosed, hexits]

/-- rc.112 short-circuits at `finalizers.size === 1` and returns that
finalizer's own effect, unwrapped. census: scope.close-merge -/
theorem closeResult_single (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) (key : κ) (finalizer : φ)
    (hclosed : self.isClosed = false) (h : self.finalizers = [(key, finalizer)]) :
    closeResult run self exit = run finalizer exit := by
  have hexits : closeExits run self exit = [run finalizer exit] := by
    show ((self.finalizers.map Prod.snd).reverse).map (fun name => run name exit) = _
    rw [h]
    rfl
  show (if self.isClosed then Exit.void
    else match closeExits run self exit with
      | [] => Exit.void
      | [only] => only
      | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)) = _
  rw [if_neg (not_isClosed hclosed), hexits]

/-- Two or more finalizers reach `exitAsVoidAll`. census: scope.close-merge -/
theorem closeResult_many (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α)
    (first second : Exit Unit ε δ ι α) (rest : List (Exit Unit ε δ ι α))
    (hclosed : self.isClosed = false)
    (h : closeExits run self exit = first :: second :: rest) :
    closeResult run self exit = Exit.asVoidAll (first :: second :: rest) := by
  show (if self.isClosed then Exit.void
    else match closeExits run self exit with
      | [] => Exit.void
      | [only] => only
      | head :: next :: tail => Exit.asVoidAll (head :: next :: tail)) = _
  rw [if_neg (not_isClosed hclosed), h]

/-- Every failure reason of every finalizer reaches the closing cause, in close
order. census: scope.close-sequential -/
theorem closeResult_reasons (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) (hclosed : self.isClosed = false) :
    (closeResult run self exit).causeReasons =
      (closeExits run self exit).flatMap Exit.causeReasons := by
  show ((if self.isClosed then Exit.void
    else match closeExits run self exit with
      | [] => Exit.void
      | [only] => only
      | first :: second :: rest => Exit.asVoidAll (first :: second :: rest))).causeReasons = _
  rw [if_neg (not_isClosed hclosed)]
  cases hexits : closeExits run self exit with
  | nil => rfl
  | cons first restExits =>
    cases restExits with
    | nil => rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    | cons second rest => exact Exit.asVoidAll_reasons (first :: second :: rest)

/-- A second close reports nothing. census: scope.close-state-first -/
theorem closeResult_closed (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) (h : self.isClosed = true) :
    closeResult run self exit = Exit.void := by
  show (if self.isClosed then Exit.void else _) = _
  rw [if_pos h]

/-- The strategy label selects no observation this model exposes. The temporal
difference between "sequential" and "parallel" belongs to the fiber machine,
which this packet does not model; `docs/SCOPE-DAG.md` keeps the two rows
`partial` for it. census: scope.close-parallel -/
theorem close_strategy_irrelevant (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (state : ScopeState κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (close run ({ strategy := FinalizerStrategy.parallel, state := state } :
        Scope κ φ β ε δ ι α) exit).snd =
      (close run ({ strategy := FinalizerStrategy.sequential, state := state } :
        Scope κ φ β ε δ ι α) exit).snd := rfl

/-! ### Fork linkage -/

/-- rc.112 `scopeForkUnsafe`, shape only: a child of a `Closed` parent is born
`Closed` with the parent's exit; otherwise one shared key registers a
parent-side finalizer and a child-side finalizer. The two names are nominal —
interpreting them needs a scope store, which this packet does not model
(`SCOPE-FB-FINALIZER-MEANING`). census: scope.fork-linkage -/
def fork [DecidableEq κ] (parent : Scope κ φ β ε δ ι α) (strategy : FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) :
    Scope κ φ β ε δ ι α × Scope κ φ β ε δ ι α :=
  match parent.closingExit? with
  | some exit => (parent, { strategy := strategy, state := ScopeState.closed exit })
  | none =>
    (parent.addUnsafe key closeChild,
      (make strategy : Scope κ φ β ε δ ι α).addUnsafe key detachFromParent)

/-- A child of a `Closed` parent is born `Closed`, and the parent is untouched.
census: scope.fork-linkage -/
theorem fork_closed_parent [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (exit : Exit β ε δ ι α) (h : parent.state = ScopeState.closed exit) :
    fork parent strategy key closeChild detachFromParent =
      (parent, ({ strategy := strategy, state := ScopeState.closed exit } :
        Scope κ φ β ε δ ι α)) := by
  have hc : parent.closingExit? = some exit := by
    show parent.state.closingExit? = some exit
    rw [h]
    rfl
  show (match parent.closingExit? with
    | some closing =>
      (parent, (Scope.mk strategy (ScopeState.closed closing) : Scope κ φ β ε δ ι α))
    | none => (parent.addUnsafe key closeChild,
        (make strategy : Scope κ φ β ε δ ι α).addUnsafe key detachFromParent)) = _
  rw [hc]

/-- The child inherits the parent's closing exit. census: scope.fork-linkage -/
theorem fork_closed_parent_child_exit [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (exit : Exit β ε δ ι α) (h : parent.state = ScopeState.closed exit) :
    (fork parent strategy key closeChild detachFromParent).snd.closingExit? = some exit := by
  rw [fork_closed_parent parent strategy key closeChild detachFromParent exit h]
  rfl

/-- An open parent gets the child-closing finalizer and the child gets the
detach finalizer, under one key. census: scope.fork-linkage -/
theorem fork_open_parent [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (h : parent.isClosed = false) :
    fork parent strategy key closeChild detachFromParent =
      (parent.addUnsafe key closeChild,
        (make strategy : Scope κ φ β ε δ ι α).addUnsafe key detachFromParent) := by
  have hc : parent.closingExit? = none :=
    ScopeState.closingExit_of_not_closed parent.state h
  show (match parent.closingExit? with
    | some closing =>
      (parent, (Scope.mk strategy (ScopeState.closed closing) : Scope κ φ β ε δ ι α))
    | none => (parent.addUnsafe key closeChild,
        (make strategy : Scope κ φ β ε δ ι α).addUnsafe key detachFromParent)) = _
  rw [hc]

/-- The child carries exactly the detach finalizer. census: scope.fork-linkage -/
theorem fork_child_finalizers [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (h : parent.isClosed = false) :
    (fork parent strategy key closeChild detachFromParent).snd.finalizers =
      [(key, detachFromParent)] := by
  rw [fork_open_parent parent strategy key closeChild detachFromParent h]
  rfl

/-- The parent keeps its registrations and appends the child-closing one.
census: scope.fork-linkage -/
theorem fork_parent_finalizers [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (h : parent.isClosed = false) (hkey : key ∉ parent.finalizerKeys) :
    (fork parent strategy key closeChild detachFromParent).fst.finalizers =
      parent.finalizers ++ [(key, closeChild)] := by
  rw [fork_open_parent parent strategy key closeChild detachFromParent h]
  exact addUnsafe_finalizers parent key closeChild h hkey

/-- The child carries the strategy it was forked with. census: scope.fork-linkage -/
theorem fork_child_strategy [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ) :
    (fork parent strategy key closeChild detachFromParent).snd.strategy = strategy := by
  show (match parent.closingExit? with
    | some closing =>
      (parent, (Scope.mk strategy (ScopeState.closed closing) : Scope κ φ β ε δ ι α))
    | none => (parent.addUnsafe key closeChild,
        (make strategy : Scope κ φ β ε δ ι α).addUnsafe key detachFromParent)).snd.strategy = _
  cases parent.closingExit? with
  | some closing => rfl
  | none => rfl

/-- One key, registered on both sides. census: scope.fork-linkage -/
theorem fork_shared_key [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (h : parent.isClosed = false) :
    key ∈ (fork parent strategy key closeChild detachFromParent).fst.finalizerKeys /\
      key ∈ (fork parent strategy key closeChild detachFromParent).snd.finalizerKeys := by
  rw [fork_open_parent parent strategy key closeChild detachFromParent h]
  exact ⟨addState_mem_keys parent.state key closeChild h,
    addState_mem_keys (make strategy : Scope κ φ β ε δ ι α).state key detachFromParent rfl⟩

/-- Removing an unregistered key restores the state exactly. -/
private theorem removeState_addState [DecidableEq κ] (state : ScopeState κ φ β ε δ ι α)
    (key : κ) (finalizer : φ) (hclosed : state.isClosed = false)
    (hkey : key ∉ state.entries.map Prod.fst) :
    (removeState (addState state key finalizer) key).entries = state.entries := by
  cases state with
  | empty =>
    show (if key = key then ScopeState.openEmpty
      else ScopeState.openInline key finalizer).entries = _
    rw [if_pos (rfl : key = key)]
    rfl
  | openEmpty =>
    show (if key = key then ScopeState.openEmpty
      else ScopeState.openInline key finalizer).entries = _
    rw [if_pos (rfl : key = key)]
  | openInline existingKey existing =>
    show tableRemove (tableInsert [(existingKey, existing)] key finalizer) key = _
    rw [tableInsert_new [(existingKey, existing)] key finalizer hkey,
      tableRemove_append_self [(existingKey, existing)] key finalizer hkey]
    rfl
  | openMap table =>
    show tableRemove (tableInsert table key finalizer) key = _
    rw [tableInsert_new table key finalizer hkey,
      tableRemove_append_self table key finalizer hkey]
    rfl
  | closed _ => exact Bool.noConfusion hclosed

/-- Removing the shared key restores the parent's registration list exactly: the
child's own finalizer can detach it. census: scope.fork-linkage -/
theorem fork_detach [DecidableEq κ] (parent : Scope κ φ β ε δ ι α)
    (strategy : FinalizerStrategy) (key : κ) (closeChild detachFromParent : φ)
    (h : parent.isClosed = false) (hkey : key ∉ parent.finalizerKeys) :
    ((fork parent strategy key closeChild detachFromParent).fst.removeUnsafe key).finalizers =
      parent.finalizers := by
  rw [fork_open_parent parent strategy key closeChild detachFromParent h]
  exact removeState_addState parent.state key closeChild h hkey

/-! ### The two brackets -/

/-- The registration trace a delimited body leaves in its scope.
census: scope.scoped -/
def addAll [DecidableEq κ] (self : Scope κ φ β ε δ ι α) :
    List (κ × φ) -> Scope κ φ β ε δ ι α
  | [] => self
  | entry :: rest => (self.addUnsafe entry.fst entry.snd).addAll rest

/-- An empty trace registers nothing. census: scope.scoped -/
theorem addAll_nil [DecidableEq κ] (self : Scope κ φ β ε δ ι α) : self.addAll [] = self := rfl

/-- The trace is replayed left to right. census: scope.scoped -/
theorem addAll_cons [DecidableEq κ] (self : Scope κ φ β ε δ ι α) (entry : κ × φ)
    (rest : List (κ × φ)) :
    self.addAll (entry :: rest) = (self.addUnsafe entry.fst entry.snd).addAll rest := rfl

/-- Replaying a trace does not change whether the scope is closed. -/
private theorem addAll_isClosed [DecidableEq κ] (registrations : List (κ × φ)) :
    forall self : Scope κ φ β ε δ ι α,
      (self.addAll registrations).isClosed = self.isClosed := by
  induction registrations with
  | nil => intro _; rfl
  | cons entry rest ih =>
    intro self
    show ((self.addUnsafe entry.fst entry.snd).addAll rest).isClosed = _
    rw [ih (self.addUnsafe entry.fst entry.snd)]
    exact addState_isClosed self.state entry.fst entry.snd

/-- Replaying a trace does not change the close strategy. -/
private theorem addAll_strategy [DecidableEq κ] (registrations : List (κ × φ)) :
    forall self : Scope κ φ β ε δ ι α,
      (self.addAll registrations).strategy = self.strategy := by
  induction registrations with
  | nil => intro _; rfl
  | cons entry rest ih =>
    intro self
    show ((self.addUnsafe entry.fst entry.snd).addAll rest).strategy = _
    rw [ih (self.addUnsafe entry.fst entry.snd)]
    rfl

/-- Replaying a trace with fresh keys appends it. -/
private theorem addAll_finalizers_aux [DecidableEq κ] (registrations : List (κ × φ)) :
    forall self : Scope κ φ β ε δ ι α, self.isClosed = false ->
      (self.finalizerKeys ++ registrations.map Prod.fst).Nodup ->
        (self.addAll registrations).finalizers = self.finalizers ++ registrations := by
  induction registrations with
  | nil =>
    intro self _ _
    show self.finalizers = self.finalizers ++ []
    rw [List.append_nil]
  | cons entry rest ih =>
    intro self hclosed hkeys
    have hsplit := List.nodup_append.mp hkeys
    have hnotmem : entry.fst ∉ self.finalizerKeys := by
      intro hmem
      exact hsplit.right.right entry.fst hmem entry.fst List.mem_cons_self rfl
    have hstep : (self.addUnsafe entry.fst entry.snd).finalizers =
        self.finalizers ++ [entry] :=
      addUnsafe_finalizers self entry.fst entry.snd hclosed hnotmem
    have hclosed' : (self.addUnsafe entry.fst entry.snd).isClosed = false := by
      show (addState self.state entry.fst entry.snd).isClosed = false
      rw [addState_isClosed]
      exact hclosed
    have hkeysEq : (self.addUnsafe entry.fst entry.snd).finalizerKeys ++ rest.map Prod.fst =
        self.finalizerKeys ++ (entry :: rest).map Prod.fst := by
      show ((self.addUnsafe entry.fst entry.snd).finalizers.map Prod.fst) ++ _ = _
      rw [hstep, List.map_append, List.append_assoc]
      rfl
    have hkeys' : ((self.addUnsafe entry.fst entry.snd).finalizerKeys ++
        rest.map Prod.fst).Nodup := by
      rw [hkeysEq]
      exact hkeys
    show ((self.addUnsafe entry.fst entry.snd).addAll rest).finalizers = _
    rw [ih (self.addUnsafe entry.fst entry.snd) hclosed' hkeys', hstep, List.append_assoc]
    rfl

/-- A delimited body's registration trace appends to the scope, key by key.
census: scope.scoped -/
theorem addAll_finalizers [DecidableEq κ] (self : Scope κ φ β ε δ ι α)
    (registrations : List (κ × φ)) (hclosed : self.isClosed = false)
    (hkeys : (self.finalizerKeys ++ registrations.map Prod.fst).Nodup) :
    (self.addAll registrations).finalizers = self.finalizers ++ registrations :=
  addAll_finalizers_aux registrations self hclosed hkeys

/-- A fresh scope records the trace exactly. census: scope.scoped -/
theorem make_addAll_finalizers [DecidableEq κ] (strategy : FinalizerStrategy)
    (registrations : List (κ × φ)) (h : (registrations.map Prod.fst).Nodup) :
    ((make strategy : Scope κ φ β ε δ ι α).addAll registrations).finalizers =
      registrations := by
  have hnodup : ((make strategy : Scope κ φ β ε δ ι α).finalizerKeys ++
      registrations.map Prod.fst).Nodup := by
    show ([] ++ registrations.map Prod.fst).Nodup
    rw [List.nil_append]
    exact h
  have hstep := addAll_finalizers (make strategy : Scope κ φ β ε δ ι α) registrations rfl hnodup
  rw [hstep]
  show [] ++ registrations = registrations
  rw [List.nil_append]

/-- rc.112 `scoped`, scope side only: install a fresh scope at the default
strategy, replay the body's registration trace, and close it with the body's
exit. The fiber context, the `OnExit` frame, and the context restore are not
modelled (`SCOPE-FB-FIBER`). census: scope.scoped -/
def runScoped [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Exit β ε δ ι α) :
    Scope κ φ β ε δ ι α × Exit Unit ε δ ι α :=
  close run
    ((make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α).addAll registrations) bodyExit

/-- `scoped` is the fresh scope closed with the body's exit. census: scope.scoped -/
theorem runScoped_eq [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Exit β ε δ ι α) :
    runScoped run registrations bodyExit =
      close run
        ((make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α).addAll registrations)
        bodyExit := rfl

/-- rc.112 `scoped` calls `scopeMakeUnsafe()` with no argument: the default is
the observation. census: scope.scoped -/
theorem runScoped_fresh_scope :
    (make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α) =
      { strategy := FinalizerStrategy.sequential, state := ScopeState.empty } := rfl

/-- The delimited scope ends closed with the body's exit. census: scope.scoped -/
theorem runScoped_state [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Exit β ε δ ι α) :
    (runScoped run registrations bodyExit).fst.state = ScopeState.closed bodyExit := by
  have hopen : ((make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α).addAll
      registrations).isClosed = false := by
    rw [addAll_isClosed registrations (make FinalizerStrategy.sequential)]
    rfl
  exact closeState_state _ bodyExit hopen

/-- The delimited scope carries the default strategy. census: scope.scoped -/
theorem runScoped_strategy [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Exit β ε δ ι α) :
    (runScoped run registrations bodyExit).fst.strategy = FinalizerStrategy.sequential := by
  show (closeState ((make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α).addAll
    registrations) bodyExit).strategy = _
  rw [closeState_strategy,
    addAll_strategy registrations (make FinalizerStrategy.sequential)]
  rfl

/-- A body that registers nothing closes to a closed empty scope and reports
success. census: scope.scoped -/
theorem runScoped_empty [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (bodyExit : Exit β ε δ ι α) :
    runScoped run ([] : List (κ × φ)) bodyExit =
      (({ strategy := FinalizerStrategy.sequential,
            state := ScopeState.closed bodyExit } : Scope κ φ β ε δ ι α),
        Exit.void) := rfl

/-- The delimited body's registration trace is closed in reverse.
census: scope.close-lifo -/
theorem runScoped_lifo [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Exit β ε δ ι α)
    (h : (registrations.map Prod.fst).Nodup) :
    closeExits run
        ((make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α).addAll registrations)
        bodyExit =
      registrations.reverse.map (fun entry => run entry.snd bodyExit) := by
  rw [closeExits_reverse run
    ((make FinalizerStrategy.sequential : Scope κ φ β ε δ ι α).addAll registrations) bodyExit,
    make_addAll_finalizers FinalizerStrategy.sequential registrations h]

/-! ### Closing in a monad

`closeExits` takes a *pure* `run`. A finalizer that runs in a monad — a region
runner's release, which performs an alphabet operation — needs the same walk
with the effects threaded through, in the same close order. `closeExitsM` is
that generalisation and nothing more: at `Id` it is `closeExits`.
-/

/-- Every registered finalizer's own exit, in close order, when running a
finalizer is itself effectful. The walk is left to right over `closeOrder`, so
the effects are threaded in close order and a failing finalizer does not abort
the loop. census: scope.close-sequential -/
def closeExitsM {M : Type u -> Type w} [Monad M]
    (run : φ -> Exit β ε δ ι α -> M (Exit Unit ε δ ι α))
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) : M (List (Exit Unit ε δ ι α)) :=
  self.closeOrder.mapM (fun finalizer => run finalizer exit)

/-- The monadic close walks `closeOrder`, by definition.
census: scope.close-sequential -/
theorem closeExitsM_eq {M : Type u -> Type w} [Monad M]
    (run : φ -> Exit β ε δ ι α -> M (Exit Unit ε δ ι α))
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    closeExitsM run self exit = self.closeOrder.mapM (fun finalizer => run finalizer exit) :=
  rfl

/-- An effect-free finalizer run gives back `closeExits`: the monadic
generalisation adds threading, not order. census: scope.close-sequential -/
theorem closeExitsM_id (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (self : Scope κ φ β ε δ ι α) (exit : Exit β ε δ ι α) :
    closeExitsM (M := Id) (fun finalizer bodyExit => run finalizer bodyExit) self exit =
      closeExits run self exit := by
  show self.closeOrder.mapM (m := Id) (fun finalizer => run finalizer exit) = _
  rw [closeExits_eq run self exit]
  induction self.closeOrder with
  | nil => rfl
  | cons finalizer rest ih =>
    rw [List.mapM_cons, List.map_cons, ← ih]
    rfl

/-- rc.112 `acquireRelease`, scope side only: register the release against the
ambient scope, and only after a successful acquire. `uninterruptibleMask` and
`provideContext` are not modelled (`SCOPE-FB-FIBER`).
census: scope.acquire-release -/
def acquireRelease [DecidableEq κ] (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α)
    (ambient : Scope κ φ β ε δ ι α) (key : κ) (release : φ)
    (acquireExit : Exit β ε δ ι α) : Scope κ φ β ε δ ι α × Exit Unit ε δ ι α :=
  match acquireExit with
  | .failure _ => (ambient, Exit.void)
  | .success _ => addExit run ambient key release

/-- rc.112 uses `tap`, which does not run its second argument on failure: a
resource that was never acquired is never released.
census: scope.acquire-release -/
theorem acquireRelease_failure [DecidableEq κ]
    (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (ambient : Scope κ φ β ε δ ι α)
    (key : κ) (release : φ) (cause : Cause ε δ ι α) :
    acquireRelease run ambient key release (Exit.failure cause) = (ambient, Exit.void) := rfl

/-- A successful acquire registers the release against the ambient scope.
census: scope.acquire-release -/
theorem acquireRelease_success [DecidableEq κ]
    (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (ambient : Scope κ φ β ε δ ι α)
    (key : κ) (release : φ) (value : β) :
    acquireRelease run ambient key release (Exit.success value) =
      addExit run ambient key release := rfl

/-- The release lands at the end of the ambient registration list.
census: scope.acquire-release -/
theorem acquireRelease_registers [DecidableEq κ]
    (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (ambient : Scope κ φ β ε δ ι α)
    (key : κ) (release : φ) (value : β) (hclosed : ambient.isClosed = false)
    (hkey : key ∉ ambient.finalizerKeys) :
    (acquireRelease run ambient key release (Exit.success value)).fst.finalizers =
      ambient.finalizers ++ [(key, release)] := by
  show (addExit run ambient key release).fst.finalizers = _
  rw [addExit_open run ambient key release hclosed]
  exact addUnsafe_finalizers ambient key release hclosed hkey

/-- Acquiring against an already-closed ambient scope runs the release now
rather than leaking it. census: scope.acquire-release -/
theorem acquireRelease_closed_ambient [DecidableEq κ]
    (run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) (ambient : Scope κ φ β ε δ ι α)
    (key : κ) (release : φ) (value : β) (exit : Exit β ε δ ι α)
    (h : ambient.state = ScopeState.closed exit) :
    acquireRelease run ambient key release (Exit.success value) = (ambient, run release exit) := by
  show addExit run ambient key release = _
  rw [addExit_closed run ambient key release exit h]

end Scope

end Effect4
