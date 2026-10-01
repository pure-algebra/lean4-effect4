import Effect4.Laws.Program.Typed.Assembly
import Test.Program.ExitTypeLane
import TypeScript.Render

/-! Registry seat, a finding of task 3: two layer typing gaps, each breaking the typed guarantee
at the root of a closed, host-free program, on the native machine and on the reference machine.

Research evidence outside the Test root. Base `be15b062`. Every fact below except the printed
TypeScript text is a kernel theorem (`decide +kernel` evaluates the run; the reference
machine's exit follows from the proved `run_eq_ref_exit`, `Laws/Program/RuntimeR.lean:248-255`).

**Gap 1, the environment of a layer's effect body.** The checker types a layer as a closed
term: `checkLayer` takes no environment and checks an effect body at `[]`
(`Program/Checker.lean:227-236`). The runtime builds that body at the enclosing point with the
enclosing point's runtime environment: `provideLayerWithK` builds the layer at `p.child 0`
(`Program/Compile.lean:767-781`), `constructionAt` resolves the body at `q.child 0`
(`:741-749`), and `Point.child` keeps `env` (`:79-80`). Levels count from the outside, so under
`k` enclosing binders the body's own binders sit at levels `k, k+1, …` at run time and at
`0, 1, …` in the checker. A body with its own binder, under an outer binder, reads the wrong
value.

**Gap 2, the provided service's type.** `checkLayer`'s `succeed` and `effect` rules never
compare the value a leaf provides with the key's service type (`Checker.lean:228-233`);
`LayerTy` records only the key set (`out`), and `service key` answers `sig.serviceTy key`
(`:215-217`). A leaf that provides a value of another type is admitted, and `service` answers
it at the table's type.

Neither is in `Test/Counterexamples/REGISTER.md` or `docs/DESIGN-ISSUES.md` at `be15b062`. The
exit-type lane does not reach them: its layer effect bodies bind nothing
(`Test/Program/TypedCorpus.lean`, the `layer.*` entries), and every layer value it provides is a
number at a number key. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.Registry.LayerGap
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Test.Program.ExitTypeLane (fits)

abbrev E := Eff NativeOp
def n (i : Nat) : Term := .lit (.nat i)
def s (x : String) : Term := .lit (.str x)
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def tape : List Api.Decision := [Api.evaluate, Api.flush]

/-- Gap 1: under an outer binder, the layer body binds `"x"` and fails with level 0. -/
def errLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer (.effect key (.bind (.succeed (s "x")) (.fail (.var 0)))) false
      (.service key)))

/-- Gap 1's control: the same layer under no outer binder. -/
def errLeakControl : E :=
  .scoped (.provideLayer (.effect key (.bind (.succeed (s "x")) (.fail (.var 0)))) false
    (.service key))

/-- Gap 1 seen by a forked fiber: the fork inside the layer body is checked at `string` and
returns the outer `9`. -/
def forkLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer
      (.effect key (.bind (.succeed (s "x"))
        (.bind (.withFiber (.fork (.succeed (.var 0)) ⟨true, false, .inherit⟩))
          (.bind (.awaitFiber (.var 1) .joinEffect) (.succeed (n 1))))))
      false (.service key)))

/-- Gap 2, an `effect` leaf: the key's service type is `nat`; the leaf provides a string. -/
def valueLeak : E := .scoped (.provideLayer (.effect key (.succeed (s "x"))) false (.service key))

/-- Gap 2, a `succeed` leaf: a Boolean at the same key. -/
def succeedLeak : E := .provideLayer (.succeed key (.bool true)) false (.service key)

/-- Gap 2's control: a number at the number key. -/
def valueControl : E := .scoped (.provideLayer (.effect key (.succeed (n 5))) false (.service key))

/-- The exit-type lane's verdict on the root: the run's exit against the checked type. -/
def rootFits (p : E) : Option Bool :=
  (Api.typeOf p []).bind fun ty =>
    let r := Api.replay p 200 tape
    r.exit.map (fits ty r.machine.state.externals.allocated)

/-- The first typed failure's value in an exit. -/
def firstFail (ex : Option ExitV) : Option Val :=
  ex.bind fun e => match e with
    | .failure c => firstErrorValue? c
    | .success _ => none

/-! ## The checked types -/

theorem key_service_nat : (nativeSignature []).serviceTy key = some .nat := by decide +kernel

theorem errLeak_checked :
    (Api.typeOf errLeak []).map (fun t => (t.answer, t.error)) = some (.nat, .string) := by
  decide +kernel

theorem forkLeak_checked :
    (Api.typeOf forkLeak []).map (fun t => (t.answer, t.error)) = some (.nat, .never) := by
  decide +kernel

theorem valueLeak_checked :
    (Api.typeOf valueLeak []).map (fun t => (t.answer, t.error)) = some (.nat, .never) := by
  decide +kernel

theorem succeedLeak_checked :
    (Api.typeOf succeedLeak []).map (fun t => (t.answer, t.error)) = some (.nat, .never) := by
  decide +kernel

/-- The fork's handle inside the layer body: the checker types the forked program at the
body's environment `[string]`. -/
theorem forkLeak_handle :
    (Checker.checkAction (nativeSignature []) [.string] [] (.fork (.succeed (.var 0) : E)
      ⟨true, false, .inherit⟩)).toOption.map (·.answer) = some (.fiberOf .string .never) := by
  decide +kernel

/-! ## The runs break them -/

/-- Gap 1: the root fails with the outer `9`, not the `"x"` the checker bound, and the exit is
outside the checked type. -/
theorem errLeak_native_exit : firstFail (Api.replay errLeak 200 tape).exit = some (.nat 9) := by
  decide +kernel

theorem errLeak_violates : rootFits errLeak = some false := by decide +kernel

/-- The same on the reference machine, the one M6's capstone is stated on. -/
theorem errLeak_reference_exit :
    firstFail (((replayR errLeak 200 tape).machine.fiber? Api.root).bind RunFiber.exit) =
      some (.nat 9) := by
  rw [← run_eq_ref_exit]
  exact errLeak_native_exit

/-- Gap 1's control fails with `"x"`, inside its checked type. -/
theorem errLeakControl_exit :
    firstFail (Api.replay errLeakControl 200 tape).exit = some (.str "x") := by decide +kernel

theorem errLeakControl_fits : rootFits errLeakControl = some true := by decide +kernel

/-- Gap 1 at a forked fiber: its handle says `string`; it returns `9`. -/
theorem forkLeak_child_exit :
    ((Api.replay forkLeak 200 tape).machine.fiber? ⟨1⟩).bind RunFiber.exit =
      some (.success (.nat 9)) := by
  decide +kernel

/-- Gap 2: the root answers the provided value at the table's `nat`. -/
theorem valueLeak_exit : (Api.replay valueLeak 200 tape).exit = some (.success (.str "x")) := by
  decide +kernel

theorem valueLeak_violates : rootFits valueLeak = some false := by decide +kernel

theorem succeedLeak_exit :
    (Api.replay succeedLeak 200 tape).exit = some (.success (.bool true)) := by decide +kernel

theorem succeedLeak_violates : rootFits succeedLeak = some false := by decide +kernel

theorem valueLeak_reference_exit :
    ((replayR valueLeak 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
      some (.success (.str "x")) := by
  rw [← run_eq_ref_exit]
  exact valueLeak_exit

theorem valueControl_fits : rootFits valueControl = some true := by decide +kernel

/-! ## M6's capstone, refuted with no host answer

The same technique as the plan review's `current_m6_capstone_false`
(`2026-09-30-origin-plan-review/Probe.lean:61-70`), which used a host answer to a sleep. This
tape answers nothing, so the proposed repair of `RReachable` (count only tapes that apply no
host answer; host-answers note §4) does not exclude it. -/

section Capstone
open Effect4.Program.Typed

def errLeakTy : EffTy := ⟨.nat, .string, Env.Requirement.empty⟩
def badExit : ExitV := .failure ⟨[.fail (.tag 9) ReasonAnnotations.empty]⟩
def bad : RState := (replayR errLeak 200 tape).machine

theorem errLeak_typeOf : Api.typeOf errLeak [] = some errLeakTy := by decide +kernel

theorem errLeakTy_closed : ClosedEff errLeakTy := ⟨rfl, rfl⟩

/-- The tape applies no host answer. -/
theorem tape_answers_nothing :
    tape.all (fun d => match d with | .answerAsync _ _ _ => false | _ => true) = true := rfl

theorem bad_reachable : RReachable (errLeak : ProgramSource) 200 bad := ⟨tape, rfl⟩

theorem bad_has_bad_exit : ∃ f ∈ bad.fibers, f.id = Api.root ∧ f.exit = some badExit := by
  decide +kernel

theorem bad_exit_not_typed (w : Typed.World) : ¬ StrongExit w errLeakTy badExit := by
  intro h
  exact Bool.noConfusion h.1

theorem bad_not_typed (w : Typed.World) :
    ¬ TypedState (errLeak : ProgramSource) errLeakTy w bad := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := bad_has_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty badExit at he
  apply bad_exit_not_typed w
  apply he errLeakTy
  rw [hid]
  exact h.1.root

/-- `typedState_reachable` (`Laws/Program/Typed/Assembly.lean:224-227`), specialized to this
program and this reached machine, is false. This refutes an open target; no accepted theorem
is contradicted. -/
theorem m6_capstone_false_without_hosts : ¬ (
    Api.typeOf errLeak [] = some errLeakTy →
    ClosedEff errLeakTy →
    RReachable (errLeak : ProgramSource) 200 bad →
    ∃ w, TypedState (errLeak : ProgramSource) errLeakTy w bad) := by
  intro h
  obtain ⟨w, hw⟩ := h errLeak_typeOf errLeakTy_closed bad_reachable
  exact bad_not_typed w hw

/-- Gap 2 refutes the capstone on its own. -/
def valueLeakTy : EffTy := ⟨.nat, .never, Env.Requirement.empty⟩
def badValueExit : ExitV := .success (.str "x")
def badValue : RState := (replayR valueLeak 200 tape).machine

theorem valueLeak_typeOf : Api.typeOf valueLeak [] = some valueLeakTy := by decide +kernel

theorem badValue_has_bad_exit :
    ∃ f ∈ badValue.fibers, f.id = Api.root ∧ f.exit = some badValueExit := by
  decide +kernel

theorem badValue_exit_not_typed (w : Typed.World) : ¬ StrongExit w valueLeakTy badValueExit := by
  intro h
  exact Bool.noConfusion h.1

theorem m6_capstone_false_valueLeak : ¬ (
    Api.typeOf valueLeak [] = some valueLeakTy →
    ClosedEff valueLeakTy →
    RReachable (valueLeak : ProgramSource) 200 badValue →
    ∃ w, TypedState (valueLeak : ProgramSource) valueLeakTy w badValue) := by
  intro h
  obtain ⟨w, hw⟩ := h valueLeak_typeOf ⟨rfl, rfl⟩ ⟨tape, rfl⟩
  obtain ⟨f, hf, hid, hex⟩ := badValue_has_bad_exit
  have he := (hw.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty badValueExit at he
  apply badValue_exit_not_typed w
  apply he valueLeakTy
  rw [hid]
  exact hw.1.root

end Capstone

#print axioms key_service_nat
#print axioms errLeak_checked
#print axioms forkLeak_checked
#print axioms valueLeak_checked
#print axioms succeedLeak_checked
#print axioms forkLeak_handle
#print axioms errLeak_native_exit
#print axioms errLeak_violates
#print axioms errLeak_reference_exit
#print axioms errLeakControl_exit
#print axioms errLeakControl_fits
#print axioms forkLeak_child_exit
#print axioms valueLeak_exit
#print axioms valueLeak_violates
#print axioms succeedLeak_exit
#print axioms succeedLeak_violates
#print axioms valueLeak_reference_exit
#print axioms valueControl_fits
#print axioms errLeak_typeOf
#print axioms errLeakTy_closed
#print axioms tape_answers_nothing
#print axioms bad_reachable
#print axioms bad_has_bad_exit
#print axioms bad_exit_not_typed
#print axioms bad_not_typed
#print axioms m6_capstone_false_without_hosts
#print axioms valueLeak_typeOf
#print axioms badValue_has_bad_exit
#print axioms badValue_exit_not_typed
#print axioms m6_capstone_false_valueLeak

/-! ## The printed face agrees with the checker, not with the runtime

A finite check on rendered text. The layer body's own binder is printed `a0`, shadowing the
outer `a0`, so by JavaScript scoping `Effect.fail(a0)` fails with `"x"`, as the checker says
(a reading of the printed program; not run under TypeScript here). -/

#guard (Api.print errLeak []).toOption.map (TypeScript.Render.expr TypeScript.house0 0) =
  some ("Effect.flatMap(Effect.succeed(9), (a0) => Effect.scoped(Effect.provide(" ++
    "Effect.service(Context.Service<number>(\"k4_4\")), Layer.effect(" ++
    "Context.Service<number>(\"k4_4\"), Effect.flatMap(Effect.succeed(\"x\"), " ++
    "(a0) => Effect.fail(a0))))))")

#eval IO.println "Layer gap probe: all theorems checked, the print guard passed."

end Research.Pass.Registry.LayerGap
