import Effect4.Laws.Program.Typed.Residual

set_option autoImplicit false
namespace KripkeResearch
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed
open Effect4.Laws.Effects

abbrev W := Effect4.Program.Typed.World

/-- Research notation only: truth in every world allowed by the actual host order. -/
def Future (P : W → Prop) (w : W) : Prop := ∀ w', w.leHost w' → P w'

def Persistent (P : W → Prop) : Prop := ∀ {w w'}, w.leHost w' → P w → P w'

theorem future_now {P : W → Prop} {w : W} (h : Future P w) : P w :=
  h w (leHost_refl w)

theorem future_future {P : W → Prop} {w : W} (h : Future P w) : Future (Future P) w :=
  fun _w' ord w'' ord' => h w'' (leHost_trans _ _ _ ord ord')

theorem future_map {P Q : W → Prop} {w : W}
    (h : Future (fun w => P w → Q w) w) (hp : Future P w) : Future Q w :=
  fun w' ord => h w' ord (hp w' ord)

theorem future_iff_of_persistent {P : W → Prop} (mono : Persistent P) (w : W) :
    Future P w ↔ P w :=
  ⟨future_now, fun h _w' ord => mono ord h⟩

theorem fits_future_iff (v : Val) (ty : Ty) (w : W) :
    Future (fun w => Fits w v ty) w ↔ Fits w v ty :=
  future_iff_of_persistent (fun ord h => fits_mono ord h) w

theorem typed_future_iff (root : ProgramSource) (ty : EffTy) (p : RProgram) (w : W) :
    Future (fun w => TypedProg root w ty p) w ↔ TypedProg root w ty p :=
  future_iff_of_persistent (fun ord h => typedProg_mono root _ _ ty p ord h) w

/-- A concrete allowed extension which is not globally well formed. -/
def w0 : W := initialWorld (EffTy.pure .nat)
def badStore : Stores := { Stores.empty with refs := [Val.cell ⟨3⟩] }
def w1 : W := { w0 with state := badStore }

theorem grows : w0.leHost w1 := by
  have stores : Stores.empty.le badStore :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _,
      fun _ h => h, Nat.le_refl _⟩
  have compatible : CellCompatible w0 w1 := by
    refine ⟨?_, ?_⟩
    · intro key ty h
      cases h.1
    · intro key ty h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, stores⟩, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, compatible, fun _ _ _ h => h, rfl⟩, fun _ _ h => h⟩

theorem initial_valid :
    WorldValid (EffTy.pure .nat) w0 (loadR (.succeed (.lit (.nat 0))) 10) :=
  initial_world_valid _ _ _ _ ⟨rfl, rfl⟩

theorem bad_not_wf : ¬ w1.state.WF := by
  intro hwf
  have impossible := hwf.1 (Val.cell ⟨3⟩) List.mem_cons_self
  change false = true at impossible
  exact Bool.noConfusion impossible

theorem validity_not_future : w0.state.WF ∧ ¬ Future (fun w => w.state.WF) w0 :=
  ⟨Stores.empty_wf, fun future => bad_not_wf (future w1 grows)⟩

/-- Pointwise existence in future worlds does not supply one fixed witness for them all. -/
theorem future_exists : Future (fun w => ∃ n : Nat, n = w.state.refs.length) w0 :=
  fun w _ => ⟨w.state.refs.length, rfl⟩

theorem no_uniform_witness : ¬ ∃ n : Nat, Future (fun w => n = w.state.refs.length) w0 := by
  rintro ⟨n, h⟩
  have h0 : n = 0 := h w0 (leHost_refl w0)
  have h1 : n = 1 := h w1 grows
  have impossible : (0 : Nat) = 1 := h0.symm.trans h1
  cases impossible

theorem uniform_witness_positive : ∃ n : Nat, Future (fun _ => n = 0) w0 :=
  ⟨0, fun _ _ => rfl⟩

/-- The existing generic protocol judgment assumes the handler's postcondition. -/
def oneOp : _root_.Effects.Signature := ⟨Unit, fun _ => Unit⟩
def trivialOrder : WorldOrder Unit := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩
def protocol (possible : Prop) : Protocol Unit oneOp :=
  ⟨fun _ => Unit, fun _ _ _ => True, fun _ _ _ _ => possible⟩
def request (result : Bool) : _root_.Effects.Program oneOp Bool :=
  .vis () (fun _ => .pure result)
def resultTrue : Unit → Bool → Prop := fun _ b => b = true

theorem impossible_post_admits_bad_continuation :
    Effect4.Laws.Effects.Typed trivialOrder (protocol False) () resultTrue (request false) :=
  .vis () trivial (fun _ _ _ impossible => False.elim impossible)

theorem possible_post_accepts_good_continuation :
    Effect4.Laws.Effects.Typed trivialOrder (protocol True) () resultTrue (request true) :=
  .vis () trivial (fun _ _ _ _ => .pure rfl)

theorem possible_post_rejects_bad_continuation :
    ¬ Effect4.Laws.Effects.Typed trivialOrder (protocol True) () resultTrue (request false) := by
  intro h
  cases h with
  | vis cert pre next =>
    have bad := next () trivial () trivial
    cases bad with
    | pure impossible => cases impossible

#print axioms future_now
#print axioms future_future
#print axioms future_map
#print axioms future_iff_of_persistent
#print axioms fits_future_iff
#print axioms typed_future_iff
#print axioms grows
#print axioms initial_valid
#print axioms validity_not_future
#print axioms future_exists
#print axioms no_uniform_witness
#print axioms uniform_witness_positive
#print axioms impossible_post_admits_bad_continuation
#print axioms possible_post_accepts_good_continuation
#print axioms possible_post_rejects_bad_continuation
end KripkeResearch
