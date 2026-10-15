import Effect4.Laws.Program.AnswerSlots.Ordinary

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: both crew initializer classes share their reference-allocation protocol.
Reach: a source certificate with any reference count and initialized binding list.
Limit: this certificate and its laws establish no machine exclusivity or admitted history.
Consumer: the root allocation and gate answer classes of Workers and QueueWorkers.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The actual source and value certificates of a crew's initialization prefix. -/
structure Initialization (root : NativeEff) where
  width : Nat
  bindings : List Val
  request : Nat → Term
  initial : Nat → Val
  head : ∀ index, index < width → ∃ tail,
    Node.at_ (.eff root) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (request index)) tail))
  closed : ∀ index, index < width → ∀ env, evalTerm env (request index) = some (initial index)
  next : ∀ index, index < width →
    bindings.take index ++ [.cell ⟨index⟩] = bindings.take (index + 1)

/-- A source initializer exposes its actual allocation and saved root continuation. -/
theorem Initialization.compile {root : NativeEff} (spec : Initialization root) (index : Nat)
    (point : Point) (fuel : Nat) (small : index < spec.width)
    (path : point.path = List.replicate index 1) (amount : point.fuel = fuel + 1) :
    resolve root point =
      .onSuccess (compileEff (.perform .refMake (spec.request index)) (point.child 0)) (.cont point) := by
  obtain ⟨tail, found⟩ := spec.head index small
  rw [← path] at found
  rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount]

/-- The actual reference initializer returns the value supplied by its source certificate. -/
theorem Initialization.operation {root : NativeEff} (spec : Initialization root) (index : Nat)
    (point : Point) (fuel : Nat) (small : index < spec.width) (amount : point.fuel = fuel + 1) :
    compileEff (.perform .refMake (spec.request index)) point =
      .sync (.op (.refMake (spec.initial index))) := by
  rw [Agreement.compileEff_perform_sync .refMake _ amount rfl, spec.closed index small point.env]
  rfl
end Effect4.Program.AnswerSlots
