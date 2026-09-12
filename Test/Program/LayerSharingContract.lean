import Lean
import Effect4.Api
import Effect4.Laws.Api.Fuel
import Lean.Util.CollectAxioms

/-! Closed counted-layer instance: one actual reference site versus two nested
reference sites, with the same table and ordinary run tape. Each certificate
transition is checked by the kernel; the public fuel law extends the finite
results to every command budget at least 300, with compile fuel fixed at 16. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Test.Program.LayerSharingContract
open Effect4 Effect4.Machine Effect4.Program
def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩
def layerCount : LayerTerm NativeOp :=
  .effect kA (.bind (.service kRef)
    (.bind (.perform (.refUpdate .incr) (.var 0)) (.succeed (.lit (.nat 5)))))
def refTarget : LayerId := [1, 0, 0, 0]
def once : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer layerCount false
        (.provideLayer (.ref refTarget) false (.service kA)))
        (.perform .refGet (.var 0))))
def twice : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer layerCount false
        (.provideLayer (.ref refTarget) false
          (.provideLayer (.ref refTarget) false (.service kA))))
        (.perform .refGet (.var 0))))

#guard once.layerRefsWF
#guard twice.layerRefsWF
#guard Api.wellTyped once
#guard Api.wellTyped twice

abbrev Commands := List (Cmd EffName EffThunk Val Err Defect FiberId Ann)
abbrev State := Api.Machine × Commands
def tick (p : Api.Program) (s : State) : State :=
  letI := evaluatorFor p
  driveState (interpOf p) 1 s.1 s.2

def ticks (p : Api.Program) (n : Nat) (s : State) : State :=
  letI := evaluatorFor p
  driveState (interpOf p) n s.1 s.2

theorem ticks_succ (p : Api.Program) (n : Nat) (s : State) :
    ticks p (n + 1) s = tick p (ticks p n s) := by
  letI := evaluatorFor p
  exact driveState_add (interpOf p) n 1 s.1 s.2

theorem replay_of_ticks (p : Api.Program) (n : Nat) (s : State)
    (h : ticks p n ((Api.load p 16, [Cmd.evaluate Api.root, Cmd.drainDue]) : State) = s)
    (hcmd : s.2 = []) (harm : s.1.armed = [])
    (hstuck : s.1.stuck = none) (hfinished : s.1.finished = true) :
    letI := evaluatorFor p
    replayEval (interpOf p) n [Api.evaluate, Api.flush] (Api.load p 16) =
      ReplayResult.finished s.1 := by
  letI := evaluatorFor p
  have hd : driveState (interpOf p) n (Api.load p 16)
      [Cmd.evaluate Api.root, Cmd.drainDue] = s := h
  have hload : (Api.load p 16).stuck = none := rfl
  have hflush : flushAllState (interpOf p) n n s.1 = (s.1, true) := by
    cases n <;> simp [flushAllState, harm]
  simp [replayEval, hload, Api.evaluate, Api.flush, stepDecisionState,
    stepDecisionState.loop, hd, settled, hcmd, hstuck, hflush, hfinished]

theorem run_of_ticks (p : Api.Program) (n : Nat) (s : State)
    (h : ticks p n ((Api.load p 16, [Cmd.evaluate Api.root, Cmd.drainDue]) : State) = s)
    (hcmd : s.2 = []) (harm : s.1.armed = [])
    (hstuck : s.1.stuck = none) (hfinished : s.1.finished = true) :
    (Api.run p n [] [] [] 16).outcome = .finished ∧
    (Api.run p n [] [] [] 16).machine = s.1 := by
  have hr := replay_of_ticks p n s h hcmd harm hstuck hfinished
  simp [Api.run, Api.replay, hr]

/- One local elaboration block proposes the finite certificate. Only the
   checked state definitions and equality theorems enter this module. -/
open Lean Elab Meta
run_elab do
  let snapshot (n : Ident) (t : Syntax) : TermElabM Unit := do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← inferType e
    let value ← reduce e
    let name := (← getCurrNamespace) ++ n.getId
    addDecl (.defnDecl { name := name, levelParams := [], type := ty, value := value, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := ← mkEq e (.const name []), value := ← mkEqRefl value })
    logInfo m!"checked {name}"
  let theoremDecl (n : Ident) (t v : Syntax) : TermElabM Unit := do
    let ty ← Term.elabTerm t none
    let value ← Term.elabTerm v (some ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let value ← instantiateMVars value
    let name := (← getCurrNamespace) ++ n.getId
    addDecl (.thmDecl { name := name, levelParams := [], type := ty, value := value })
  for (fixture, count) in [("once", 216), ("twice", 300)] do
    let p := mkIdent (Lean.Name.mkSimple fixture)
    let base := mkIdent (p.getId.appendAfter "_s0")
    let first := mkIdent (p.getId.appendAfter "_prefix0")
    snapshot base (← `(((Api.load $p 16,
      [Cmd.evaluate Api.root, Cmd.drainDue]) : State)))
    theoremDecl first (← `(ticks $p 0 $base = $base)) (← `(rfl))
    for i in [:count] do
      let prev := mkIdent (p.getId.appendAfter s!"_s{i}")
      let next := mkIdent (p.getId.appendAfter s!"_s{i+1}")
      let prevProof := mkIdent (p.getId.appendAfter s!"_prefix{i}")
      let nextProof := mkIdent (p.getId.appendAfter s!"_prefix{i+1}")
      let eqProof := mkIdent (next.getId.appendAfter "_eq")
      let idx := Syntax.mkNumLit (toString (i+1))
      let prevIdx := Syntax.mkNumLit (toString i)
      snapshot next (← `(tick $p $prev))
      theoremDecl nextProof (← `(ticks $p $idx $base = $next)) (← `(
        (ticks_succ $p $prevIdx $base).trans
          ((congrArg (tick $p) $prevProof).trans $eqProof)))

theorem once_commands_done : once_s216.2 = [] := rfl
theorem once_exit : (once_s216.1.fiber? Api.root).bind RunFiber.exit =
    some (.success (.nat 1)) := rfl
theorem once_refs : once_s216.1.state.refs = [.nat 1] := rfl
#print axioms once_prefix216
#print axioms once_exit
#print axioms once_refs

theorem twice_commands_done : twice_s300.2 = [] := rfl
theorem twice_exit : (twice_s300.1.fiber? Api.root).bind RunFiber.exit =
    some (.success (.nat 1)) := rfl
theorem twice_refs : twice_s300.1.state.refs = [.nat 1] := rfl
#print axioms twice_prefix300
#print axioms twice_exit
#print axioms twice_refs

theorem once_run : (Api.run once 216 [] [] [] 16).outcome = .finished ∧
    (Api.run once 216 [] [] [] 16).machine = once_s216.1 :=
  run_of_ticks once 216 once_s216
    ((congrArg (ticks once 216) once_s0_eq).trans once_prefix216)
    once_commands_done rfl rfl rfl

theorem twice_run : (Api.run twice 300 [] [] [] 16).outcome = .finished ∧
    (Api.run twice 300 [] [] [] 16).machine = twice_s300.1 :=
  run_of_ticks twice 300 twice_s300
    ((congrArg (ticks twice 300) twice_s0_eq).trans twice_prefix300)
    twice_commands_done rfl rfl rfl

theorem once_count : (Api.run once 216 [] [] [] 16).outcome = .finished ∧
    (Api.run once 216 [] [] [] 16).exit = some (.success (.nat 1)) ∧
    (Api.run once 216 [] [] [] 16).stores.refs = [.nat 1] := by
  refine ⟨once_run.1, ?_, ?_⟩
  · unfold Api.Run.exit
    rw [once_run.2]
    exact once_exit
  · unfold Api.Run.stores
    rw [once_run.2]
    exact once_refs

theorem twice_count : (Api.run twice 300 [] [] [] 16).outcome = .finished ∧
    (Api.run twice 300 [] [] [] 16).exit = some (.success (.nat 1)) ∧
    (Api.run twice 300 [] [] [] 16).stores.refs = [.nat 1] := by
  refine ⟨twice_run.1, ?_, ?_⟩
  · unfold Api.Run.exit
    rw [twice_run.2]
    exact twice_exit
  · unfold Api.Run.stores
    rw [twice_run.2]
    exact twice_refs

theorem provide_ref_twice (fuel : Nat) (hf : 300 ≤ fuel) :
    (Api.run once fuel [] [] [] 16).outcome = .finished ∧
    (Api.run twice fuel [] [] [] 16).outcome = .finished ∧
    (Api.run twice fuel [] [] [] 16).exit = (Api.run once fuel [] [] [] 16).exit ∧
    (Api.run once fuel [] [] [] 16).stores.refs = [.nat 1] ∧
    (Api.run twice fuel [] [] [] 16).stores.refs = [.nat 1] := by
  have onceStable : Api.run once fuel [] [] [] 16 = Api.run once 216 [] [] [] 16 :=
    Api.finished_mono_fuel once 216 fuel [Api.evaluate, Api.flush] [] [] [] 16
      once_count.1 (Nat.le_trans (by decide) hf)
  have twiceStable : Api.run twice fuel [] [] [] 16 = Api.run twice 300 [] [] [] 16 :=
    Api.finished_mono_fuel twice 300 fuel [Api.evaluate, Api.flush] [] [] [] 16 twice_count.1 hf
  rw [onceStable, twiceStable]
  exact ⟨once_count.1, twice_count.1, twice_count.2.1.trans once_count.2.1.symm,
    once_count.2.2, twice_count.2.2⟩

#print axioms replay_of_ticks
#print axioms run_of_ticks
#print axioms once_run
#print axioms twice_run
#print axioms once_count
#print axioms twice_count
#print axioms provide_ref_twice
end Test.Program.LayerSharingContract

run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  let mut definitions : Nat := 0
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      count := count + 1
      let deps ← Lean.collectAxioms name
      Lean.logInfo m!"{name}: {deps}"
      unless deps.all (fun dep => dep == ``propext || dep == ``Quot.sound) do
        throwError "axiom ceiling exceeded: {name}: {deps}"
      if let .defnInfo defn := info then
        definitions := definitions + 1
        unless defn.safety == .safe do
          throwError "non-safe definition: {name}"
        let root := `Test.Program.LayerSharingContract
        let leaf := name.getString!
        let expected := ["kA", "kRef", "layerCount", "refTarget", "once", "twice",
          "Commands", "State", "tick", "ticks"].contains leaf ||
          leaf.startsWith "once_s" || leaf.startsWith "twice_s"
        unless name.getPrefix == root && expected do
          throwError "unexpected retained definition: {name}"
  unless count > 0 do throwError "empty audit"
  Lean.logInfo m!"PASS: inspected all {count} declarations defined by the current module; {definitions} ordinary definitions; no retained elaborator helper"
