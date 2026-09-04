/-
Contract packet: `test/contracts/scope.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until `Effect4/Runtime/Scope.lean` declares the frozen surface.

Every public declaration is frozen by an exact `#check (@name : proposition)`
ascription so no weaker statement satisfies this contract. Names are written
fully qualified; this module deliberately does not `open Effect4`, so a
locally shadowed spelling cannot silently satisfy an ascription.

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` section 6.
-/

import Effect4.Machine.Exit
import Effect4.Machine.Scope

set_option autoImplicit false

namespace Test.Runtime.ScopeContract

universe u v

section StrategySurface

/-! S0: the two-value finalizer strategy label (census: scope.make,
scope.close-sequential, scope.close-parallel).

The strategy is a passive label. rc.112 does not attach a scheduler policy to
it: "parallel" is immediate daemon forks that inherit the closing fiber's mask.
This packet models no fiber, so it states only the alphabet. -/

#check (@Effect4.FinalizerStrategy : Type)
#check (@Effect4.FinalizerStrategy.sequential : Effect4.FinalizerStrategy)
#check (@Effect4.FinalizerStrategy.parallel : Effect4.FinalizerStrategy)
#check (@Effect4.FinalizerStrategy.all : List Effect4.FinalizerStrategy)
#synth DecidableEq Effect4.FinalizerStrategy
#synth Repr Effect4.FinalizerStrategy

#check (@Effect4.FinalizerStrategy.all_nodup : Effect4.FinalizerStrategy.all.Nodup)
#check (@Effect4.FinalizerStrategy.mem_all :
  forall strategy : Effect4.FinalizerStrategy, strategy ∈ Effect4.FinalizerStrategy.all)
#check (@Effect4.FinalizerStrategy.cases_receipt :
  forall strategy : Effect4.FinalizerStrategy,
    strategy = Effect4.FinalizerStrategy.sequential \/
      strategy = Effect4.FinalizerStrategy.parallel)

end StrategySurface

section StateSurface

/-! S1: the scope state machine (census: scope.states).

`κ` is the externally admitted finalizer-key alphabet — rc.112's `{}` object
identity. `φ` is the externally admitted finalizer-name alphabet: a finalizer
is a nominal key, never a stored Lean closure (DB-02). The three `open*`
constructors are exactly the three inhabited shapes of rc.112's `Open` record
under its own XOR invariant. -/

#check (@Effect4.ScopeState :
  Type u -> Type u -> Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))
#check (@Effect4.ScopeState.empty : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.ScopeState κ φ β ε δ ι α)
#check (@Effect4.ScopeState.openEmpty : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.ScopeState κ φ β ε δ ι α)
#check (@Effect4.ScopeState.openInline : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  κ -> φ -> Effect4.ScopeState κ φ β ε δ ι α)
#check (@Effect4.ScopeState.openMap : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  List (κ × φ) -> Effect4.ScopeState κ φ β ε δ ι α)
#check (@Effect4.ScopeState.closed : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Exit β ε δ ι α -> Effect4.ScopeState κ φ β ε δ ι α)

example {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ] [DecidableEq φ]
    [DecidableEq β] [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    DecidableEq (Effect4.ScopeState κ φ β ε δ ι α) :=
  inferInstance

#check (@Effect4.ScopeState.entries : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.ScopeState κ φ β ε δ ι α -> List (κ × φ))
#check (@Effect4.ScopeState.isOpen : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.ScopeState κ φ β ε δ ι α -> Bool)
#check (@Effect4.ScopeState.isClosed : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.ScopeState κ φ β ε δ ι α -> Bool)
#check (@Effect4.ScopeState.closingExit? : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.ScopeState κ φ β ε δ ι α -> Option (Effect4.Exit β ε δ ι α))

#check (@Effect4.ScopeState.cases_receipt :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state = Effect4.ScopeState.empty \/
      state = Effect4.ScopeState.openEmpty \/
        (exists key finalizer, state = Effect4.ScopeState.openInline key finalizer) \/
          (exists table, state = Effect4.ScopeState.openMap table) \/
            (exists exit, state = Effect4.ScopeState.closed exit))

/-! The materialised registration order of each state. -/
#check (@Effect4.ScopeState.entries_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.empty : Effect4.ScopeState κ φ β ε δ ι α).entries = [])
#check (@Effect4.ScopeState.entries_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α).entries = [])
#check (@Effect4.ScopeState.entries_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (key : κ) (finalizer : φ),
    (Effect4.ScopeState.openInline key finalizer :
      Effect4.ScopeState κ φ β ε δ ι α).entries = [(key, finalizer)])
#check (@Effect4.ScopeState.entries_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (table : List (κ × φ)),
    (Effect4.ScopeState.openMap table : Effect4.ScopeState κ φ β ε δ ι α).entries = table)
#check (@Effect4.ScopeState.entries_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

/-! `Empty` and `Closed` are not `Open`. -/
#check (@Effect4.ScopeState.isOpen_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.empty : Effect4.ScopeState κ φ β ε δ ι α).isOpen = false)
#check (@Effect4.ScopeState.isOpen_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)
#check (@Effect4.ScopeState.isOpen_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (key : κ) (finalizer : φ),
    (Effect4.ScopeState.openInline key finalizer :
      Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)
#check (@Effect4.ScopeState.isOpen_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (table : List (κ × φ)),
    (Effect4.ScopeState.openMap table : Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)
#check (@Effect4.ScopeState.isOpen_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).isOpen = false)

#check (@Effect4.ScopeState.isClosed_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state.isClosed = true <-> exists exit, state = Effect4.ScopeState.closed exit)
#check (@Effect4.ScopeState.closingExit_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).closingExit? =
      some exit)
#check (@Effect4.ScopeState.closingExit_of_not_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state.isClosed = false -> state.closingExit? = none)

/-! The cleared inline slot is not the empty map: the next add lands in the
inline slot in the first case and in the map in the second. -/
#check (@Effect4.ScopeState.openEmpty_ne_openMap_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α) ≠
      Effect4.ScopeState.openMap [])

end StateSurface

section ScopeSurface

/-! S2: the scope carrier and its observations (census: scope.states,
scope.make). -/

#check (@Effect4.Scope :
  Type u -> Type u -> Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))
#check (@Effect4.Scope.mk : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.FinalizerStrategy -> Effect4.ScopeState κ φ β ε δ ι α ->
    Effect4.Scope κ φ β ε δ ι α)
#check (@Effect4.Scope.strategy : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Effect4.FinalizerStrategy)
#check (@Effect4.Scope.state : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Effect4.ScopeState κ φ β ε δ ι α)

example {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ] [DecidableEq φ]
    [DecidableEq β] [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    DecidableEq (Effect4.Scope κ φ β ε δ ι α) :=
  inferInstance

#check (@Effect4.Scope.make : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.FinalizerStrategy -> Effect4.Scope κ φ β ε δ ι α)
#check (@Effect4.Scope.makeDefault : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α)
#check (@Effect4.Scope.finalizers : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> List (κ × φ))
#check (@Effect4.Scope.finalizerKeys : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> List κ)
#check (@Effect4.Scope.finalizerCount : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Nat)
#check (@Effect4.Scope.isOpen : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Bool)
#check (@Effect4.Scope.isClosed : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Bool)
#check (@Effect4.Scope.closingExit? : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Option (Effect4.Exit β ε δ ι α))

/-! A new scope starts Empty; the default strategy is sequential. -/
#check (@Effect4.Scope.make_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).strategy = strategy)
#check (@Effect4.Scope.make_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).state =
      Effect4.ScopeState.empty)
#check (@Effect4.Scope.make_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).finalizers = [])
#check (@Effect4.Scope.makeDefault_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.makeDefault : Effect4.Scope κ φ β ε δ ι α) =
      Effect4.Scope.make Effect4.FinalizerStrategy.sequential)
#check (@Effect4.Scope.makeDefault_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.makeDefault : Effect4.Scope κ φ β ε δ ι α).strategy =
      Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.finalizers_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizers = self.state.entries)
#check (@Effect4.Scope.finalizerKeys_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizerKeys = self.finalizers.map Prod.fst)
#check (@Effect4.Scope.finalizerCount_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizerCount = self.finalizers.length)
/-! rc.112 `scopeFinalizerCountUnsafe` answers zero for every non-Open scope. -/
#check (@Effect4.Scope.finalizerCount_not_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.isOpen = false -> self.finalizerCount = 0)

/-! The rc.112 `{}` key freshness is refused, not modelled: an Effect4 key is a
value, so no minting function can distinguish two structurally equal keys. -/
#check (@Effect4.Scope.key_freshness_refused :
  forall {κ : Type u} {γ : Type u} (mint : γ -> κ) (left right : γ),
    left = right -> mint left = mint right)

end ScopeSurface

section TableSurface

/-! S3: the keyed insertion-ordered finalizer table (census:
scope.add-finalizer, scope.remove-finalizer).

`tableInsert` is JavaScript `Map.prototype.set`: an existing key keeps its slot
and only its value changes; a new key is appended. `tableRemove` is
`Map.prototype.delete`. -/

#check (@Effect4.Scope.tableInsert : forall {κ φ : Type u} [DecidableEq κ],
  List (κ × φ) -> κ -> φ -> List (κ × φ))
#check (@Effect4.Scope.tableRemove : forall {κ φ : Type u} [DecidableEq κ],
  List (κ × φ) -> κ -> List (κ × φ))

#check (@Effect4.Scope.tableInsert_new : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∉ table.map Prod.fst ->
    Effect4.Scope.tableInsert table key finalizer = table ++ [(key, finalizer)])
#check (@Effect4.Scope.tableInsert_existing : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∈ table.map Prod.fst ->
    Effect4.Scope.tableInsert table key finalizer =
      table.map (fun entry => if entry.fst = key then (key, finalizer) else entry))
#check (@Effect4.Scope.tableInsert_keys_of_mem : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∈ table.map Prod.fst ->
    (Effect4.Scope.tableInsert table key finalizer).map Prod.fst = table.map Prod.fst)
#check (@Effect4.Scope.tableInsert_nodup : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  (table.map Prod.fst).Nodup ->
    ((Effect4.Scope.tableInsert table key finalizer).map Prod.fst).Nodup)

#check (@Effect4.Scope.tableRemove_eq : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  Effect4.Scope.tableRemove table key =
    table.filter (fun entry => decide (entry.fst ≠ key)))
#check (@Effect4.Scope.tableRemove_keys : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  key ∉ (Effect4.Scope.tableRemove table key).map Prod.fst)
#check (@Effect4.Scope.tableRemove_nodup : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  (table.map Prod.fst).Nodup ->
    ((Effect4.Scope.tableRemove table key).map Prod.fst).Nodup)

end TableSurface

section AddSurface

/-! S4: registration (census: scope.add-finalizer, scope.add-after-closed). -/

#check (@Effect4.Scope.addUnsafe : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ], Effect4.Scope κ φ β ε δ ι α -> κ -> φ -> Effect4.Scope κ φ β ε δ ι α)
#check (@Effect4.Scope.addExit : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ],
  (φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α) ->
    Effect4.Scope κ φ β ε δ ι α -> κ -> φ ->
      Effect4.Scope κ φ β ε δ ι α × Effect4.Exit Unit ε δ ι α)

#check (@Effect4.Scope.addUnsafe_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    (self.addUnsafe key finalizer).strategy = self.strategy)
/-! The first add stores an inline finalizer and its key. -/
#check (@Effect4.Scope.addUnsafe_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.empty ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openInline key finalizer)
/-! A cleared inline slot takes the next add inline again, not into a map. -/
#check (@Effect4.Scope.addUnsafe_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openEmpty ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openInline key finalizer)
/-! The second add promotes both into a map. -/
#check (@Effect4.Scope.addUnsafe_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (existing finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey existing ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openMap
          (Effect4.Scope.tableInsert [(existingKey, existing)] key finalizer))
#check (@Effect4.Scope.addUnsafe_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openMap table ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openMap (Effect4.Scope.tableInsert table key finalizer))
/-! `scopeAddFinalizerUnsafe` has no `Closed` arm at all. -/
#check (@Effect4.Scope.addUnsafe_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = true -> self.addUnsafe key finalizer = self)
/-! The promotion preserves insertion order. -/
#check (@Effect4.Scope.addUnsafe_promotes :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (existing finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey existing -> existingKey ≠ key ->
      (self.addUnsafe key finalizer).finalizers =
        [(existingKey, existing), (key, finalizer)])
/-! Registration appends, in every open shape. -/
#check (@Effect4.Scope.addUnsafe_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = false -> key ∉ self.finalizerKeys ->
      (self.addUnsafe key finalizer).finalizers = self.finalizers ++ [(key, finalizer)])
#check (@Effect4.Scope.addUnsafe_keys_nodup :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.finalizerKeys.Nodup -> (self.addUnsafe key finalizer).finalizerKeys.Nodup)

/-! `scopeAddFinalizerExit`: register when open, run now when closed. -/
#check (@Effect4.Scope.addExit_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = false ->
      Effect4.Scope.addExit run self key finalizer =
        (self.addUnsafe key finalizer, Effect4.Exit.void))
#check (@Effect4.Scope.addExit_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ)
    (exit : Effect4.Exit β ε δ ι α),
    self.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.addExit run self key finalizer = (self, run finalizer exit))
#check (@Effect4.Scope.addExit_closed_registers_nothing :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ)
    (exit : Effect4.Exit β ε δ ι α),
    self.state = Effect4.ScopeState.closed exit ->
      (Effect4.Scope.addExit run self key finalizer).fst.finalizers = [])

end AddSurface

section RemoveSurface

/-! S5: removal (census: scope.remove-finalizer). -/

#check (@Effect4.Scope.removeUnsafe : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ], Effect4.Scope κ φ β ε δ ι α -> κ -> Effect4.Scope κ φ β ε δ ι α)

#check (@Effect4.Scope.removeUnsafe_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    (self.removeUnsafe key).strategy = self.strategy)
/-! The inline slot is cleared when the key matches. -/
#check (@Effect4.Scope.removeUnsafe_inline_hit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openInline key finalizer ->
      (self.removeUnsafe key).state = Effect4.ScopeState.openEmpty)
/-! An inline slot under a different key is untouched: there is no map to
delete from. -/
#check (@Effect4.Scope.removeUnsafe_inline_miss :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey finalizer -> existingKey ≠ key ->
      self.removeUnsafe key = self)
#check (@Effect4.Scope.removeUnsafe_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ),
    self.state = Effect4.ScopeState.openMap table ->
      (self.removeUnsafe key).state =
        Effect4.ScopeState.openMap (Effect4.Scope.tableRemove table key))
/-! A non-Open scope is left untouched. -/
#check (@Effect4.Scope.removeUnsafe_not_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    self.isOpen = false -> self.removeUnsafe key = self)
#check (@Effect4.Scope.removeUnsafe_keys :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    key ∉ (self.removeUnsafe key).finalizerKeys)
#check (@Effect4.Scope.removeUnsafe_keys_nodup :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    self.finalizerKeys.Nodup -> (self.removeUnsafe key).finalizerKeys.Nodup)

end RemoveSurface

section CloseSurface

/-! S6: closing (census: scope.close-state-first, scope.close-lifo,
scope.close-sequential, scope.close-parallel, scope.close-merge,
rule.scope-close-lifo-state-first).

`run` is the externally supplied finalizer interpretation: it maps a nominal
finalizer and the closing exit to the finalizer's own exit. It is an argument,
never stored in the scope, so no Lean closure enters canonical scope data. -/

#check (@Effect4.Scope.closeState : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> Effect4.Exit β ε δ ι α -> Effect4.Scope κ φ β ε δ ι α)
#check (@Effect4.Scope.closeOrder : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  Effect4.Scope κ φ β ε δ ι α -> List φ)
#check (@Effect4.Scope.closeExits : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  (φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α) ->
    Effect4.Scope κ φ β ε δ ι α -> Effect4.Exit β ε δ ι α ->
      List (Effect4.Exit Unit ε δ ι α))
#check (@Effect4.Scope.closeResult : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  (φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α) ->
    Effect4.Scope κ φ β ε δ ι α -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
#check (@Effect4.Scope.close : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
  (φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α) ->
    Effect4.Scope κ φ β ε δ ι α -> Effect4.Exit β ε δ ι α ->
      Effect4.Scope κ φ β ε δ ι α × Effect4.Exit Unit ε δ ι α)

/-! Close is exactly the state flip paired with the finalizer result. -/
#check (@Effect4.Scope.close_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.close run self exit =
      (Effect4.Scope.closeState self exit, Effect4.Scope.closeResult run self exit))
/-! State first: the resulting state cannot depend on what any finalizer does. -/
#check (@Effect4.Scope.close_state_independent_of_run :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (leftRun rightRun : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.close leftRun self exit).fst =
      (Effect4.Scope.close rightRun self exit).fst)
#check (@Effect4.Scope.closeState_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeState self exit).state = Effect4.ScopeState.closed exit)
#check (@Effect4.Scope.closeState_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).strategy = self.strategy)
#check (@Effect4.Scope.closeState_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).finalizers = [])
#check (@Effect4.Scope.closeState_isClosed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).isClosed = true)
#check (@Effect4.Scope.closeState_idempotent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.closeState self exit = self)
#check (@Effect4.Scope.close_closingExit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeState self exit).closingExit? = some exit)
/-! Closing an already-Closed scope returns without running a finalizer. -/
#check (@Effect4.Scope.close_idempotent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.close run self exit = (self, Effect4.Exit.void))
#check (@Effect4.Scope.close_twice :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (first second : Effect4.Exit β ε δ ι α),
    Effect4.Scope.close run (Effect4.Scope.close run self first).fst second =
      ((Effect4.Scope.close run self first).fst, Effect4.Exit.void))
/-! The sharp form of "state before finalizers": a finalizer that re-enters the
scope while it closes sees a Closed scope, so its own registration runs
immediately with the closing exit rather than being recorded. -/
#check (@Effect4.Scope.close_reentrant_add :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (key : κ)
    (finalizer : φ),
    self.isClosed = false ->
      Effect4.Scope.addExit run (Effect4.Scope.closeState self exit) key finalizer =
        (Effect4.Scope.closeState self exit, run finalizer exit))

/-! LIFO: finalizers are materialised in insertion order and iterated backwards. -/
#check (@Effect4.Scope.closeOrder_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.closeOrder = (self.finalizers.map Prod.snd).reverse)
#check (@Effect4.Scope.closeOrder_last_first :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (table : List (κ × φ)) (key : κ) (finalizer : φ),
    self.finalizers = table ++ [(key, finalizer)] ->
      self.closeOrder = finalizer :: (table.map Prod.snd).reverse)
#check (@Effect4.Scope.closeExits_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.closeExits run self exit =
      self.closeOrder.map (fun finalizer => run finalizer exit))
#check (@Effect4.Scope.closeExits_reverse :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.closeExits run self exit =
      self.finalizers.reverse.map (fun entry => run entry.snd exit))
/-! Every registered finalizer runs: a failing one does not abort the close. -/
#check (@Effect4.Scope.closeExits_length :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeExits run self exit).length = self.finalizers.length)

/-! The three arms of `scopeCloseUnsafe`: nothing, the single finalizer's own
effect, and the `exitAsVoidAll` merge. -/
#check (@Effect4.Scope.closeResult_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.finalizers = [] -> Effect4.Scope.closeResult run self exit = Effect4.Exit.void)
#check (@Effect4.Scope.closeResult_single :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (key : κ)
    (finalizer : φ),
    self.isClosed = false -> self.finalizers = [(key, finalizer)] ->
      Effect4.Scope.closeResult run self exit = run finalizer exit)
#check (@Effect4.Scope.closeResult_many :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α)
    (first second : Effect4.Exit Unit ε δ ι α) (rest : List (Effect4.Exit Unit ε δ ι α)),
    self.isClosed = false ->
      Effect4.Scope.closeExits run self exit = first :: second :: rest ->
        Effect4.Scope.closeResult run self exit =
          Effect4.Exit.asVoidAll (first :: second :: rest))
/-! Every failure reason of every finalizer reaches the closing cause, in close
order. -/
#check (@Effect4.Scope.closeResult_reasons :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeResult run self exit).causeReasons =
        (Effect4.Scope.closeExits run self exit).flatMap Effect4.Exit.causeReasons)
#check (@Effect4.Scope.closeResult_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.closeResult run self exit = Effect4.Exit.void)
/-! The strategy label selects no observation this model exposes. The temporal
difference between "sequential" and "parallel" belongs to the fiber machine,
which this packet does not model; `docs/SCOPE-DAG.md` records the two rows that
stay `partial` because of it. -/
#check (@Effect4.Scope.close_strategy_irrelevant :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (state : Effect4.ScopeState κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.close run
        ({ strategy := Effect4.FinalizerStrategy.parallel, state := state } :
          Effect4.Scope κ φ β ε δ ι α) exit).snd =
      (Effect4.Scope.close run
        ({ strategy := Effect4.FinalizerStrategy.sequential, state := state } :
          Effect4.Scope κ φ β ε δ ι α) exit).snd)

end CloseSurface

section ForkSurface

/-! S7: scope fork linkage (census: scope.fork-linkage).

The two linked finalizers are nominal: `closeChild` is the parent-side name of
`(exit) => scopeClose(child, exit)` and `detachFromParent` is the child-side
name of `(_) => scopeRemoveFinalizerUnsafe(parent, key)`. Interpreting those
two names needs a scope store, which this packet does not model; what is frozen
here is the linkage shape and the removal law that makes the detach work. -/

#check (@Effect4.Scope.fork : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ],
  Effect4.Scope κ φ β ε δ ι α -> Effect4.FinalizerStrategy -> κ -> φ -> φ ->
    Effect4.Scope κ φ β ε δ ι α × Effect4.Scope κ φ β ε δ ι α)

/-! A child of a Closed parent is born Closed with the parent's exit. -/
#check (@Effect4.Scope.fork_closed_parent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) (exit : Effect4.Exit β ε δ ι α),
    parent.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.fork parent strategy key closeChild detachFromParent =
        (parent, ({ strategy := strategy, state := Effect4.ScopeState.closed exit } :
          Effect4.Scope κ φ β ε δ ι α)))
#check (@Effect4.Scope.fork_closed_parent_child_exit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) (exit : Effect4.Exit β ε δ ι α),
    parent.state = Effect4.ScopeState.closed exit ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.closingExit? =
        some exit)
#check (@Effect4.Scope.fork_open_parent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      Effect4.Scope.fork parent strategy key closeChild detachFromParent =
        (parent.addUnsafe key closeChild,
          (Effect4.Scope.make strategy :
            Effect4.Scope κ φ β ε δ ι α).addUnsafe key detachFromParent))
#check (@Effect4.Scope.fork_child_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.finalizers =
        [(key, detachFromParent)])
#check (@Effect4.Scope.fork_parent_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false -> key ∉ parent.finalizerKeys ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).fst.finalizers =
        parent.finalizers ++ [(key, closeChild)])
#check (@Effect4.Scope.fork_child_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.strategy =
      strategy)
/-! One key, registered on both sides. -/
#check (@Effect4.Scope.fork_shared_key :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      key ∈ (Effect4.Scope.fork parent strategy key closeChild
          detachFromParent).fst.finalizerKeys /\
        key ∈ (Effect4.Scope.fork parent strategy key closeChild
          detachFromParent).snd.finalizerKeys)
/-! Removing the shared key restores the parent's registration list exactly:
the child's own finalizer can detach it. -/
#check (@Effect4.Scope.fork_detach :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false -> key ∉ parent.finalizerKeys ->
      ((Effect4.Scope.fork parent strategy key closeChild
        detachFromParent).fst.removeUnsafe key).finalizers = parent.finalizers)

end ForkSurface

section BracketSurface

/-! S8: the two brackets, scope side only (census: scope.scoped,
scope.acquire-release).

`Scope.runScoped` carries rc.112's `scoped` name; `scoped` is a Lean keyword.
Neither bracket models the fiber context, the OnExit frame, or
`uninterruptibleMask`. -/

#check (@Effect4.Scope.addAll : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ],
  Effect4.Scope κ φ β ε δ ι α -> List (κ × φ) -> Effect4.Scope κ φ β ε δ ι α)
#check (@Effect4.Scope.runScoped : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ],
  (φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α) -> List (κ × φ) ->
    Effect4.Exit β ε δ ι α -> Effect4.Scope κ φ β ε δ ι α × Effect4.Exit Unit ε δ ι α)
#check (@Effect4.Scope.acquireRelease : forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
  [DecidableEq κ],
  (φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α) ->
    Effect4.Scope κ φ β ε δ ι α -> κ -> φ -> Effect4.Exit β ε δ ι α ->
      Effect4.Scope κ φ β ε δ ι α × Effect4.Exit Unit ε δ ι α)

#check (@Effect4.Scope.addAll_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α), self.addAll [] = self)
#check (@Effect4.Scope.addAll_cons :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (entry : κ × φ) (rest : List (κ × φ)),
    self.addAll (entry :: rest) = (self.addUnsafe entry.fst entry.snd).addAll rest)
#check (@Effect4.Scope.addAll_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (registrations : List (κ × φ)),
    self.isClosed = false ->
      (self.finalizerKeys ++ registrations.map Prod.fst).Nodup ->
        (self.addAll registrations).finalizers = self.finalizers ++ registrations)
#check (@Effect4.Scope.make_addAll_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (strategy : Effect4.FinalizerStrategy) (registrations : List (κ × φ)),
    (registrations.map Prod.fst).Nodup ->
      ((Effect4.Scope.make strategy :
        Effect4.Scope κ φ β ε δ ι α).addAll registrations).finalizers = registrations)

/-! `scoped` installs a fresh default-strategy scope and closes it with the
body's exit. -/
#check (@Effect4.Scope.runScoped_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.runScoped run registrations bodyExit =
      Effect4.Scope.close run
        ((Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
          Effect4.Scope κ φ β ε δ ι α).addAll registrations) bodyExit)
#check (@Effect4.Scope.runScoped_fresh_scope :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
      Effect4.Scope κ φ β ε δ ι α) =
      { strategy := Effect4.FinalizerStrategy.sequential,
        state := Effect4.ScopeState.empty })
#check (@Effect4.Scope.runScoped_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.runScoped run registrations bodyExit).fst.state =
      Effect4.ScopeState.closed bodyExit)
#check (@Effect4.Scope.runScoped_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.runScoped run registrations bodyExit).fst.strategy =
      Effect4.FinalizerStrategy.sequential)
#check (@Effect4.Scope.runScoped_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (bodyExit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.runScoped run ([] : List (κ × φ)) bodyExit =
      (({ strategy := Effect4.FinalizerStrategy.sequential,
            state := Effect4.ScopeState.closed bodyExit } :
          Effect4.Scope κ φ β ε δ ι α),
        Effect4.Exit.void))
#check (@Effect4.Scope.runScoped_lifo :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (registrations.map Prod.fst).Nodup ->
      Effect4.Scope.closeExits run
          ((Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
            Effect4.Scope κ φ β ε δ ι α).addAll registrations) bodyExit =
        registrations.reverse.map (fun entry => run entry.snd bodyExit))

/-! `acquireRelease` registers the release only after a successful acquire. -/
#check (@Effect4.Scope.acquireRelease_failure :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ)
    (cause : Effect4.Cause ε δ ι α),
    Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.failure cause) =
      (ambient, Effect4.Exit.void))
#check (@Effect4.Scope.acquireRelease_success :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β),
    Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.success value) =
      Effect4.Scope.addExit run ambient key release)
#check (@Effect4.Scope.acquireRelease_registers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β),
    ambient.isClosed = false -> key ∉ ambient.finalizerKeys ->
      (Effect4.Scope.acquireRelease run ambient key release
        (Effect4.Exit.success value)).fst.finalizers =
          ambient.finalizers ++ [(key, release)])
/-! Acquiring against an already-closed ambient scope runs the release now. -/
#check (@Effect4.Scope.acquireRelease_closed_ambient :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β)
    (exit : Effect4.Exit β ε δ ι α),
    ambient.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.success value) =
        (ambient, run release exit))

end BracketSurface

section GroundChecks

/-! S9: small executable checks over closed alphabets. They are finite probes,
not laws; every law above is separately frozen. -/

abbrev Key := Nat
abbrev Finalizer := Nat
abbrev Err := Nat
abbrev Defect := Bool
abbrev Interruptor := Nat
abbrev Ann := Nat

abbrev GroundScope := Effect4.Scope Key Finalizer Unit Err Defect Interruptor Ann
abbrev GroundExit := Effect4.Exit Unit Err Defect Interruptor Ann

def failWith (error : Nat) : GroundExit :=
  Effect4.Exit.failure
    (Effect4.Cause.mk [Effect4.Reason.fail error Effect4.ReasonAnnotations.empty])

/-- Finalizer `0` succeeds, `1` and `2` fail with their error, `3` fails with
the empty cause. -/
def run : Finalizer -> GroundExit -> GroundExit
  | 0, _ => Effect4.Exit.void
  | 1, _ => failWith 1
  | 2, _ => failWith 2
  | 3, _ => Effect4.Exit.failure Effect4.Cause.empty
  | _, _ => Effect4.Exit.void

def emptyScope : GroundScope := Effect4.Scope.make Effect4.FinalizerStrategy.sequential
def oneScope : GroundScope := emptyScope.addUnsafe 10 0
def twoScope : GroundScope := oneScope.addUnsafe 20 1
def threeScope : GroundScope := twoScope.addUnsafe 30 2

/-! The first add is inline; the second promotes both into an ordered map. -/
example : oneScope.state = Effect4.ScopeState.openInline 10 0 := by decide
example : twoScope.state = Effect4.ScopeState.openMap [(10, 0), (20, 1)] := by decide
example : threeScope.finalizers = [(10, 0), (20, 1), (30, 2)] := by decide

/-! The last registered finalizer runs first. -/
example : threeScope.closeOrder = [2, 1, 0] := by decide

/-! A failing finalizer does not stop the ones that follow it. -/
example : (Effect4.Scope.closeExits run threeScope Effect4.Exit.void).length = 3 := by decide

/-! Every failure reason reaches one flat closing cause, in close order. -/
example :
    (Effect4.Scope.close run threeScope Effect4.Exit.void).snd =
      Effect4.Exit.failure
        (Effect4.Cause.mk
          [Effect4.Reason.fail 2 Effect4.ReasonAnnotations.empty,
            Effect4.Reason.fail 1 Effect4.ReasonAnnotations.empty]) := by
  decide

/-! Close writes the state and drops the registration list. -/
example :
    (Effect4.Scope.close run threeScope Effect4.Exit.void).fst.state =
      Effect4.ScopeState.closed Effect4.Exit.void := by
  decide
example : (Effect4.Scope.close run threeScope Effect4.Exit.void).fst.finalizers = [] := by
  decide

/-! A second close runs nothing. -/
example :
    Effect4.Scope.close run (Effect4.Scope.close run threeScope Effect4.Exit.void).fst
        (failWith 9) =
      ((Effect4.Scope.close run threeScope Effect4.Exit.void).fst, Effect4.Exit.void) := by
  decide

/-! The single-finalizer arm returns the finalizer's own exit, so an empty-cause
failure survives where `exitAsVoidAll` would have erased it. -/
example :
    Effect4.Scope.closeResult run (emptyScope.addUnsafe 10 3) Effect4.Exit.void =
      Effect4.Exit.failure Effect4.Cause.empty := by
  decide
example :
    Effect4.Exit.asVoidAll
        (Effect4.Scope.closeExits run (emptyScope.addUnsafe 10 3) Effect4.Exit.void) =
      Effect4.Exit.success () := by
  decide

/-! Adding to a closed scope runs the finalizer now, with the stored exit. -/
example :
    Effect4.Scope.addExit run (Effect4.Scope.close run oneScope (failWith 7)).fst 40 1 =
      ((Effect4.Scope.close run oneScope (failWith 7)).fst, failWith 1) := by
  decide

/-! Removing the inline slot leaves `openEmpty`: neither `empty` nor `openMap []`. -/
example : (oneScope.removeUnsafe 10).state = Effect4.ScopeState.openEmpty := by decide
example :
    (oneScope.removeUnsafe 10).state ≠
      (Effect4.ScopeState.empty :
        Effect4.ScopeState Key Finalizer Unit Err Defect Interruptor Ann) := by
  decide
example : (oneScope.removeUnsafe 10).state ≠ Effect4.ScopeState.openMap [] := by decide
example :
    ((oneScope.removeUnsafe 10).addUnsafe 50 0).state =
      Effect4.ScopeState.openInline 50 0 := by
  decide
example :
    (((twoScope.removeUnsafe 10).removeUnsafe 20).addUnsafe 50 0).state =
      Effect4.ScopeState.openMap [(50, 0)] := by
  decide

/-! Removal leaves an Empty or Closed scope untouched. -/
example : emptyScope.removeUnsafe 10 = emptyScope := by decide
example :
    (Effect4.Scope.close run oneScope Effect4.Exit.void).fst.removeUnsafe 10 =
      (Effect4.Scope.close run oneScope Effect4.Exit.void).fst := by
  decide

/-! A child of a Closed parent is born Closed with the parent's exit. -/
example :
    (Effect4.Scope.fork (Effect4.Scope.close run oneScope (failWith 7)).fst
        Effect4.FinalizerStrategy.parallel 99 1 2).snd =
      ({ strategy := Effect4.FinalizerStrategy.parallel,
          state := Effect4.ScopeState.closed (failWith 7) } : GroundScope) := by
  decide

/-! One shared key links the two scopes, and only that key detaches the parent. -/
example :
    (Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1 2).fst.finalizers =
      [(10, 0), (20, 1), (99, 1)] := by
  decide
example :
    (Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1 2).snd.finalizers =
      [(99, 2)] := by
  decide
example :
    ((Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1
        2).fst.removeUnsafe 99).finalizers = twoScope.finalizers := by
  decide
example :
    ((Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1
        2).fst.removeUnsafe 77).finalizers ≠ twoScope.finalizers := by
  decide

/-! `runScoped` and `acquireRelease`. -/
example :
    (Effect4.Scope.runScoped run ([] : List (Key × Finalizer)) (failWith 5) :
        GroundScope × GroundExit) =
      ({ strategy := Effect4.FinalizerStrategy.sequential,
          state := Effect4.ScopeState.closed (failWith 5) },
        Effect4.Exit.void) := by
  decide
example :
    (Effect4.Scope.runScoped run [(10, 0), (20, 1)] Effect4.Exit.void :
      GroundScope × GroundExit).snd = failWith 1 := by
  decide
example :
    Effect4.Scope.acquireRelease run oneScope 20 1 (Effect4.Exit.failure Effect4.Cause.empty) =
      (oneScope, Effect4.Exit.void) := by
  decide
example :
    (Effect4.Scope.acquireRelease run oneScope 20 1
      (Effect4.Exit.success ())).fst.finalizers = [(10, 0), (20, 1)] := by
  decide

/-! The strategy label changes no exit in this model. -/
example :
    (Effect4.Scope.close run
        { strategy := Effect4.FinalizerStrategy.parallel, state := threeScope.state }
        Effect4.Exit.void).snd =
      (Effect4.Scope.close run threeScope Effect4.Exit.void).snd := by
  decide

end GroundChecks

section AxiomReceipts

#print axioms Effect4.Scope.make_state
#print axioms Effect4.Scope.addUnsafe_finalizers
#print axioms Effect4.Scope.addExit_closed
#print axioms Effect4.Scope.removeUnsafe_inline_hit
#print axioms Effect4.Scope.close_state_independent_of_run
#print axioms Effect4.Scope.close_reentrant_add
#print axioms Effect4.Scope.close_idempotent
#print axioms Effect4.Scope.closeOrder_last_first
#print axioms Effect4.Scope.closeResult_single
#print axioms Effect4.Scope.closeResult_reasons
#print axioms Effect4.Scope.fork_closed_parent
#print axioms Effect4.Scope.fork_detach
#print axioms Effect4.Scope.runScoped_lifo
#print axioms Effect4.Scope.acquireRelease_registers

end AxiomReceipts

end Test.Runtime.ScopeContract
