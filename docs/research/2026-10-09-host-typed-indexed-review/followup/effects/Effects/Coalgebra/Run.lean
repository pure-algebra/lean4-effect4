import Effects.Coalgebra.Protocol

/-!
# Running a system against a host

`System.run` runs a system against a host to a depth: the host runs the system's unfolding. The
result is `some (some a, s')` when the system ends with `a` and the host's state is `s'`;
`some (none, s')` when the run reached a cut or the depth; `none` when the host did not answer.

The corollaries a consumer uses:

* `run_of_sim`: where a simulated system finishes against a host, the simulating system finishes
  the same way, at the same depth, against the same host;
* `run_eq_of_bisim`: bisimilar states run alike against every host, at every depth;
* `run_mono`: a run that finished at one depth finishes the same way at every greater depth;
* `run_of_sim_program`: where a system simulated by a program finishes against a host, the
  program finishes the same way against that host. This is the shape of a host-as-handler law:
  one simulation, every host.

`Program.peel` and `System.peel` hide the operations of an inner signature behind a total
function of a state: a program over `S ⊕ₛ T` becomes a system over `T` whose states carry the
inner state. `run_peel` says what that system's runs are: the runs of the program against the
inner function routed beside the host.
-/

namespace Effects

universe uOp uAns uT uX uY

namespace System

variable {S : Signature.{uOp, uAns}} {A : Type uAns} {X : Type uX} {Y : Type uY} {σ : Type uAns}

/-- **Run a system against a host, to a depth.** -/
def run (system : System S A X) (host : Comodel S σ) (depth : Nat) (state : X) (start : σ) :
    Option (Option A × σ) :=
  host.run (system.unfold depth state) start

/-- **Where a simulated system finishes, the simulating one finishes the same way.** -/
theorem run_of_sim {c : System S A X} {d : System S A Y} {R : X → Y → Prop} (h : IsSim c d R)
    {x : X} {y : Y} (hxy : R x y) (host : Comodel S σ) {depth : Nat} {start finish : σ}
    {value : A} (hrun : c.run host depth x start = some (some value, finish)) :
    d.run host depth y start = some (some value, finish) :=
  host.run_approx (unfold_approx_of_sim h depth x y hxy) hrun

/-- **Bisimilar states run alike against every host, at every depth.** -/
theorem run_eq_of_bisim {c : System S A X} {d : System S A Y} {R : X → Y → Prop}
    (h : IsBisim c d R) {x : X} {y : Y} (hxy : R x y) (host : Comodel S σ) (depth : Nat)
    (start : σ) : c.run host depth x start = d.run host depth y start := by
  rw [run, run, unfold_eq_of_bisim h depth x y hxy]

/-- A run that finished at one depth finishes the same way at every greater depth. -/
theorem run_mono (c : System S A X) (host : Comodel S σ) {depth depth' : Nat}
    (hle : depth ≤ depth') {x : X} {start finish : σ} {value : A}
    (hrun : c.run host depth x start = some (some value, finish)) :
    c.run host depth' x start = some (some value, finish) :=
  host.run_approx (c.unfold_mono hle x) hrun

end System

namespace Program

variable {S : Signature.{uOp, uAns}} {A : Type uAns} {X : Type uX} {σ : Type uAns}

/-- A program's own system finishes against a host as the program does. -/
theorem run_system (host : Comodel S σ) {depth : Nat} {program : Program S A} {start finish : σ}
    {value : A} (hrun : Program.system.run host depth program start = some (some value, finish)) :
    host.run program start = some (value, finish) := by
  have h := host.run_approx (Program.unfold_system depth program) hrun
  rw [Comodel.run_uncut] at h
  cases hp : host.run program start with
  | none =>
    rw [hp] at h
    simp only [Option.map_none, reduceCtorEq] at h
  | some result =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact congrArg some (Prod.ext h.1 h.2)

/-- **One simulation, every host.** Where a system simulated by a program finishes against a
host, the program finishes the same way against that host. -/
theorem run_of_sim_program {c : System S A X} {R : X → Program S A → Prop}
    (h : IsSim c Program.system R) {x : X} {program : Program S A} (hxy : R x program)
    (host : Comodel S σ) {depth : Nat} {start finish : σ} {value : A}
    (hrun : c.run host depth x start = some (some value, finish)) :
    host.run program start = some (value, finish) :=
  run_system host (System.run_of_sim h hxy host hrun)

end Program

/-! ## Hiding an inner signature -/

namespace Comodel

variable {S : Signature.{uOp, uAns}} {ρ : Type uAns}

/-- A host that always answers, by a total function of its state. -/
def ofTotal (inner : (operation : S.Op) → ρ → S.Answer operation × ρ) : Comodel S ρ where
  answer operation state := some (inner operation state)

end Comodel

namespace Program

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}} {A : Type uAns} {ρ : Type uAns}

/-- **The next step toward `T`** of a program over `S ⊕ₛ T`: the operations of `S` are answered
along the way by a total function of the state `ρ`; the first operation of `T` is the step's
call, or the result with the final inner state is its end. -/
def peel (inner : (operation : S.Op) → ρ → S.Answer operation × ρ) :
    Program (S ⊕ₛ T) A → ρ → Step T (A × ρ) (Program (S ⊕ₛ T) A × ρ)
  | .pure value, state => .done (value, state)
  | .vis (.inl operation) next, state =>
    peel inner (next (inner operation state).1) (inner operation state).2
  | .vis (.inr operation) next, state => .call operation (fun answer => (next answer, state))

/-- What `peel` reads off a run: the routed run of a program is the run its next step gives. -/
theorem run_route_peel (inner : (operation : S.Op) → ρ → S.Answer operation × ρ) {σ : Type uAns}
    (host : Comodel T σ) : ∀ (program : Program (S ⊕ₛ T) A) (state : ρ) (start : σ),
      ((Comodel.ofTotal inner).route host).run program (state, start) =
        match program.peel inner state with
        | .done result => some (result.1, (result.2, start))
        | .call operation next =>
          (host.answer operation start).bind fun reply =>
            ((Comodel.ofTotal inner).route host).run (next reply.1).1 ((next reply.1).2, reply.2)
  | .pure _, _, _ => rfl
  | .vis (.inl operation) next, state, start => by
    rw [Comodel.run_vis_some _ _ (show ((Comodel.ofTotal inner).route host).answer
        (.inl operation) (state, start) =
          some ((inner operation state).1, ((inner operation state).2, start)) from rfl)]
    exact run_route_peel inner host (next (inner operation state).1) _ start
  | .vis (.inr operation) next, state, start => by
    show _ = (host.answer operation start).bind _
    rcases h : host.answer operation start with _ | ⟨reply, start'⟩
    · exact Comodel.run_vis_none _ _ (show ((Comodel.ofTotal inner).route host).answer
        (.inr operation) (state, start) = none by
          show (host.answer operation start).map _ = none
          rw [h]
          rfl)
    · exact Comodel.run_vis_some _ _ (show ((Comodel.ofTotal inner).route host).answer
        (.inr operation) (state, start) = some (reply, (state, start')) by
          show (host.answer operation start).map _ = _
          rw [h]
          rfl)

end Program

namespace System

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}} {A : Type uAns} {ρ : Type uAns}

/-- **A program over `S ⊕ₛ T` as a system over `T`**, the operations of `S` hidden behind a
total function of the inner state. -/
def peel (inner : (operation : S.Op) → ρ → S.Answer operation × ρ) :
    System T (A × ρ) (Program (S ⊕ₛ T) A × ρ) :=
  fun state => some (Program.peel inner state.1 state.2)

/-- **What the hiding system's runs are.** Where it finishes against a host, the program finishes
the same way against the inner function routed beside the host. -/
theorem run_peel (inner : (operation : S.Op) → ρ → S.Answer operation × ρ) {σ : Type uAns}
    (host : Comodel T σ) : ∀ (depth : Nat) (program : Program (S ⊕ₛ T) A) (state : ρ)
      (start : σ) {value : A} {state' : ρ} {finish : σ},
      (peel inner).run host depth (program, state) start =
          some (some (value, state'), finish) →
        ((Comodel.ofTotal inner).route host).run program (state, start) =
          some (value, (state', finish))
  | 0, _, _, _, _, _, _, h => by
    simp only [run, unfold_zero, Comodel.run_pure, Option.some.injEq, Prod.mk.injEq,
      reduceCtorEq, false_and] at h
  | depth + 1, program, state, start, value, state', finish, h => by
    rw [Program.run_route_peel]
    rcases hp : program.peel inner state with ⟨result⟩ | ⟨operation, next⟩
    · have hu := unfold_done (system := peel inner) (state := (program, state))
        (show peel inner (program, state) = some (.done result) by
          show some (program.peel inner state) = _
          rw [hp]) depth
      rw [run, hu, Comodel.run_pure] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · have hu := unfold_call (system := peel inner) (state := (program, state))
        (show peel inner (program, state) = some (.call operation next) by
          show some (program.peel inner state) = _
          rw [hp]) depth
      rw [run, hu] at h
      show (host.answer operation start).bind _ = _
      rcases ha : host.answer operation start with _ | ⟨reply, start'⟩
      · rw [Comodel.run_vis_none _ _ ha] at h
        simp only [reduceCtorEq] at h
      · rw [Comodel.run_vis_some _ _ ha] at h
        exact run_peel inner host depth (next reply).1 (next reply).2 start' h

/-- Two states whose steps are one unfold alike, at every depth. -/
theorem unfold_eq_of_step {Y : Type uY} {system : System T A Y} {x y : Y} (h : system x = system y) :
    ∀ depth, system.unfold depth x = system.unfold depth y
  | 0 => rfl
  | depth + 1 => by simp only [unfold, h]

/-- **The hiding system loses no finished run.** Where the program finishes against the inner
function routed beside a host, the hiding system finishes the same way at some depth: one more
than the number of the host's answers on the way. With `run_peel`, the hiding system's finished
runs are exactly the program's. -/
theorem run_peel_complete (inner : (operation : S.Op) → ρ → S.Answer operation × ρ) {σ : Type uAns}
    (host : Comodel T σ) : ∀ (program : Program (S ⊕ₛ T) A) (state : ρ) (start : σ) {value : A}
      {state' : ρ} {finish : σ},
      ((Comodel.ofTotal inner).route host).run program (state, start) =
          some (value, (state', finish)) →
        ∃ depth, (peel inner).run host depth (program, state) start =
          some (some (value, state'), finish)
  | .pure value, state, start, value', state', finish, h => by
    rw [Comodel.run_pure, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨1, rfl⟩
  | .vis (.inl operation) next, state, start, value, state', finish, h => by
    rw [Comodel.run_vis_some _ _ (show ((Comodel.ofTotal inner).route host).answer
        (.inl operation) (state, start) =
          some ((inner operation state).1, ((inner operation state).2, start)) from rfl)] at h
    obtain ⟨depth, hd⟩ := run_peel_complete inner host (next (inner operation state).1)
      (inner operation state).2 start h
    refine ⟨depth, ?_⟩
    rw [run, unfold_eq_of_step (system := peel inner)
      (show peel inner (Program.vis (.inl operation) next, state) =
        peel inner (next (inner operation state).1, (inner operation state).2) from rfl) depth]
    exact hd
  | .vis (.inr operation) next, state, start, value, state', finish, h => by
    rcases ha : host.answer operation start with _ | ⟨reply, start'⟩
    · have hr : ((Comodel.ofTotal inner).route host).answer (.inr operation) (state, start) = none := by
        show (host.answer operation start).map _ = none
        rw [ha]
        rfl
      rw [Comodel.run_vis_none _ _ hr] at h
      cases h
    · have hr : ((Comodel.ofTotal inner).route host).answer (.inr operation) (state, start) =
          some (reply, (state, start')) := by
        show (host.answer operation start).map _ = _
        rw [ha]
        rfl
      rw [Comodel.run_vis_some _ _ hr] at h
      obtain ⟨depth, hd⟩ := run_peel_complete inner host (next reply) state start' h
      refine ⟨depth + 1, ?_⟩
      have hu := unfold_call (system := peel inner)
        (state := (Program.vis (.inr operation) next, state))
        (show peel inner (Program.vis (.inr operation) next, state) =
          some (.call operation fun answer => (next answer, state)) from rfl) depth
      rw [run, hu, Comodel.run_vis_some _ _ ha]
      exact hd

end System

end Effects
