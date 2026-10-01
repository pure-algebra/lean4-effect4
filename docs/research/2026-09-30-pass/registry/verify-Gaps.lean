import Effect4.Laws.Program.Typed.Assembly
import Effect4.Api.HostSession
import Test.Program.ExitTypeLane

/-! Verifier of the registry seat: the two layer gaps, pushed further.

Research evidence outside the Test root. Base `be15b062`. Written by the adversarial verifier;
it does not edit the seat's files.

Three questions the seat's `LayerGap.lean` leaves open:

1. Does the live, certified route admit the gap programs? `LayerGap.lean` shows `Api.typeOf`
   accepts them. Here `admitProgram` (the admission `HostSession.start` runs) accepts them too
   (kernel theorems for `errLeak` and `valueLeak`, `#guard` for the rest), and the live session
   reaches the bad exits (finite checks, `#guard`).
2. Is gap 1 only in `Layer.effect`? It is also in `Layer.effectDiscard` (kernel theorems).
3. What does the typed state say when a gap program crashes rather than returns a wrong
   value? A body that applies `succ` to the value the gap puts in scope dies with the
   bad-shape defect (`badName`), which the exit-type lane treats as impossible for a checked
   program (`ExitTypeLane.badDefect`). The typed state's exit clause admits that exit at
   every type (`strongExit_of_dies`), so even a repaired M6 capstone would not see the crash.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.RegistryVerify.Gaps
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Api.HostSession

abbrev E := Eff NativeOp
def n (i : Nat) : Term := .lit (.nat i)
def s (x : String) : Term := .lit (.str x)
def u : Term := .lit .unit
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def succOf (t : Term) : Term := .app "succ" (.cons t .nil)
def tape : List Api.Decision := [Api.evaluate, Api.flush]

/-- The seat's programs, copied (`LayerGap.lean:47-71`). -/
def errLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer (.effect key (.bind (.succeed (s "x")) (.fail (.var 0)))) false
      (.service key)))
def valueLeak : E := .scoped (.provideLayer (.effect key (.succeed (s "x"))) false (.service key))
def succeedLeak : E := .provideLayer (.succeed key (.bool true)) false (.service key)

/-- Gap 1, crashing: the body binds `1` and takes its successor; at run time level 0 is the
outer string. -/
def crash1 : E :=
  .bind (.succeed (s "s"))
    (.scoped (.provideLayer (.effect key (.bind (.succeed (n 1)) (.succeed (succOf (.var 0)))))
      false (.service key)))

/-- Gap 2, crashing: the service answers a Boolean at the number key; its successor. -/
def crash2 : E :=
  .bind (.provideLayer (.succeed key (.bool true)) false (.service key))
    (.succeed (succOf (.var 0)))

/-- Gap 1 in `Layer.effectDiscard`. -/
def discardLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer (.effectDiscard (.bind (.succeed (s "x")) (.fail (.var 0)))) false
      (.succeed u)))

/-! ## 1. The live admission and the live session (finite checks) -/

#guard [errLeak, valueLeak, succeedLeak, crash1, crash2, discardLeak].all fun p =>
  (admitProgram p []).toOption.isSome

def header : Header := ⟨version, "verify", "verify", []⟩

/-- `start` (which admits through `admitProgram`), then `evaluate` and `flush` on the live
session; the root's exit. -/
def liveExit (p : E) : Option (Option ExitV) :=
  match start p [] "verify" header 1000 with
  | .error _ => none
  | .ok s0 =>
    let r1 := advance s0 1000 Api.evaluate
    let r2 := advance r1.session 1000 Api.flush
    some ((r2.session.machine.fiber? Api.root).bind (·.exit))

def firstFail (ex : Option ExitV) : Option Val :=
  ex.bind fun e => match e with
    | .failure c => firstErrorValue? c
    | .success _ => none

def isDie : Reason Err Defect FiberId Ann → Bool
  | .die _ _ => true
  | _ => false

def isBadName : Reason Err Defect FiberId Ann → Bool
  | .die .badName _ => true
  | _ => false

/-- A failure whose reasons are all the bad-shape defect. -/
def diesBadShape (ex : Option ExitV) : Bool :=
  match ex with
  | some (.failure c) => !c.reasons.isEmpty && c.reasons.all isBadName
  | _ => false

#guard ((liveExit errLeak).map firstFail) = some (some (.nat 9))
#guard (liveExit valueLeak) = some (some (.success (.str "x")))
#guard (liveExit succeedLeak) = some (some (.success (.bool true)))
#guard ((liveExit crash1).map diesBadShape) = some true
#guard ((liveExit crash2).map diesBadShape) = some true

/-! ## 2. Kernel facts -/

/-- The live admission (`admitProgram`, what `HostSession.start` runs) accepts both gaps'
programs, so a capstone premised on admission rather than on `Api.typeOf` is refuted too. -/
theorem errLeak_admitted : (admitProgram errLeak []).toOption.isSome = true := by
  decide +kernel

theorem valueLeak_admitted : (admitProgram valueLeak []).toOption.isSome = true := by
  decide +kernel

theorem crash1_checked :
    (Api.typeOf crash1 []).map (fun t => (t.answer, t.error)) = some (.nat, .never) := by
  decide +kernel

theorem crash2_checked :
    (Api.typeOf crash2 []).map (fun t => (t.answer, t.error)) = some (.nat, .never) := by
  decide +kernel

theorem discardLeak_checked :
    (Api.typeOf discardLeak []).map (fun t => (t.answer, t.error)) = some (.unit, .string) := by
  decide +kernel

/-- Gap 1 in `effectDiscard`: checked at error `string`, fails with the outer number. -/
theorem discardLeak_native_exit : firstFail (Api.replay discardLeak 200 tape).exit = some (.nat 9) := by
  decide +kernel

theorem crash1_native_dies : diesBadShape (Api.replay crash1 200 tape).exit = true := by
  decide +kernel

theorem crash2_native_dies : diesBadShape (Api.replay crash2 200 tape).exit = true := by
  decide +kernel

/-- The same crash on the reference machine M6 is stated on, through the proved
`run_eq_ref_exit`. -/
theorem crash1_reference_dies :
    diesBadShape (((replayR crash1 200 tape).machine.fiber? Api.root).bind RunFiber.exit) = true := by
  rw [← run_eq_ref_exit]
  exact crash1_native_dies

theorem crash2_reference_dies :
    diesBadShape (((replayR crash2 200 tape).machine.fiber? Api.root).bind RunFiber.exit) = true := by
  rw [← run_eq_ref_exit]
  exact crash2_native_dies

/-! ## 3. The typed state's exit clause admits a crash at every type -/

section Blind
open Effect4.Program.Typed

/-- An exit whose reasons are all defects is a strong exit at every type in every world
(`reasonAdmits` admits `die`, `ErrorImage.lean:31-36`; `StrongCause` admits it,
`Typed/Admission.lean:65-68`). -/
theorem strongExit_of_dies (w : Typed.World) (ty : EffTy) (c : CauseV)
    (h : c.reasons.all isDie = true) : StrongExit w ty (.failure c) := by
  refine ⟨?_, ?_, ?_⟩
  · show causeAdmits _ ty.error c = true
    unfold causeAdmits
    rw [List.all_eq_true] at h ⊢
    intro r hr
    have hd := h r hr
    cases r with
    | fail e a => cases hd
    | die d a => rfl
    | interrupt i a => cases hd
  · intro v hv
    cases hv
  · intro c' hc'
    cases hc'
    intro r hr
    have hd := (List.all_eq_true.mp h) r hr
    cases r with
    | fail e a => cases hd
    | die d a => trivial
    | interrupt i a => trivial

theorem allDie_of_diesBadShape (ex : Option ExitV) (h : diesBadShape ex = true) :
    ∃ c, ex = some (.failure c) ∧ c.reasons.all isDie = true := by
  cases ex with
  | none => cases h
  | some e =>
    cases e with
    | success v => cases h
    | failure c =>
      refine ⟨c, rfl, ?_⟩
      have hc : c.reasons.all isBadName = true := by
        simp only [diesBadShape, Bool.and_eq_true] at h
        exact h.2
      rw [List.all_eq_true] at hc ⊢
      intro r hr
      have hb := hc r hr
      cases r with
      | fail e a => cases hb
      | die d a => rfl
      | interrupt i a => cases hb

/-- `crash1` is checked at `nat`, dies with the bad-shape defect on the reference machine,
and that exit satisfies the typed state's exit clause at every type, in every world. So the
exit clause of M6's typed state cannot tell this run from a sound one. -/
theorem crash1_exit_clause_blind (w : Typed.World) (ty : EffTy) :
    ∃ ex, ((replayR crash1 200 tape).machine.fiber? Api.root).bind RunFiber.exit = some ex ∧
      StrongExit w ty ex := by
  obtain ⟨c, hc, hall⟩ := allDie_of_diesBadShape _ crash1_reference_dies
  exact ⟨.failure c, hc, strongExit_of_dies w ty c hall⟩

theorem crash2_exit_clause_blind (w : Typed.World) (ty : EffTy) :
    ∃ ex, ((replayR crash2 200 tape).machine.fiber? Api.root).bind RunFiber.exit = some ex ∧
      StrongExit w ty ex := by
  obtain ⟨c, hc, hall⟩ := allDie_of_diesBadShape _ crash2_reference_dies
  exact ⟨.failure c, hc, strongExit_of_dies w ty c hall⟩

end Blind

-- The lane's rule catches both crashes: `badDefect` holds of the exit's reason.
#guard (match (Api.replay crash1 200 tape).exit with
  | some (.failure c) => c.reasons.any (Test.Program.ExitTypeLane.badDefect (EffTy.pure .nat))
  | _ => false)
#guard (match (Api.replay crash2 200 tape).exit with
  | some (.failure c) => c.reasons.any (Test.Program.ExitTypeLane.badDefect (EffTy.pure .nat))
  | _ => false)

#print axioms errLeak_admitted
#print axioms valueLeak_admitted
#print axioms crash1_checked
#print axioms crash2_checked
#print axioms discardLeak_checked
#print axioms discardLeak_native_exit
#print axioms crash1_native_dies
#print axioms crash2_native_dies
#print axioms crash1_reference_dies
#print axioms crash2_reference_dies
#print axioms strongExit_of_dies
#print axioms allDie_of_diesBadShape
#print axioms crash1_exit_clause_blind
#print axioms crash2_exit_clause_blind

#eval IO.println "verify-Gaps: all guards passed."

end Research.Pass.RegistryVerify.Gaps
