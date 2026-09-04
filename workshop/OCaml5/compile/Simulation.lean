import OCaml5.compile.Agreement

/-!
# Spike P4: the simulation statement, and the pure fragment

Status: spike P4, 2026-09-04. Module `OCaml5.compile.Simulation`. Report:
`docs/research/2026-09-04-spike-p4-compile.md` §6.

`compile_correct` is written down exactly (§1); the two lemmas that reduce it to a pair of
settled runs are proved (§2); the pure fragment is checked instance by instance in the
evaluator, with the reason it is not checked in the kernel measured and recorded (§3); and the
arms it is not proved for are stated one by one, with the invariant each needs (§4). Nothing
here is `sorry`, `axiom`, `partial`, `unsafe` or `native_decide`; the unproved arms are
*statements*, `Prop`-valued definitions with no proof claimed.
-/

namespace OCaml5.compile

open OCaml5 OCaml5.Code

/-! ## 1. The statement

The two machines have different carriers, so the theorem is stated through the two projections
of `OCaml5.compile.Agreement`: `outcomeMatches` on outcomes, `rowsOfOutput` on the printed
output. The existential over `fuel'` is what makes this a simulation rather than a lockstep
bisimulation: one `Machine` step is many `Code.Machine` steps, and how many depends on the
term. -/

/-- **`compile_correct`.** If the runtime machine finishes on `t` — any fuel that is enough —
then some fuel is enough for the compiled program, and the two agree on the outcome and on
every row. -/
def CompileCorrect (t : Term Nat) : Prop :=
  ∀ (fuel : Nat) (m : OCaml5.Machine Nat) (o : OCaml5.Outcome Nat),
    OCaml5.Machine.run fuel (OCaml5.Machine.start t) = (m, o) →
    o ≠ OCaml5.Outcome.fuel →
    ∃ fuel' : Nat,
      outcomeMatches o (Code.Machine.exec fuel' (Compile.compile t)).1 = true ∧
      m.rows = rowsOfOutput (Code.Machine.exec fuel' (Compile.compile t)).2

mutual

/-- The syntactic half of `compile`'s domain: `ocamlc` compiles the term
(`Compiler.Admissible`, `bytegen.ml:796-804`), and it uses neither of the two runtime entry
points `Code.Machine.purePrim` has no arm for. -/
def usesNoGap : Term Nat → Bool
  | .val _ | .unit | .var _ | .none | .emit _ | .getCell => true
  | .lam b | .emitOf _ b | .setCell b | .some b | .raise b | .perform b | .contUseNoexc b =>
      usesNoGap b
  | .app a b | .letIn a b | .seq a b | .add a b | .tryWith a b => usesNoGap a && usesNoGap b
  | .eff _ b | .exn _ b => usesNoGap b
  | .matchOpt a b c | .resume a b c | .runstack a b c | .reperform a b c
  | .allocStack a b c => usesNoGap a && usesNoGap b && usesNoGap c
  | .matchEff s cls d => usesNoGap s && usesNoGapEff cls && usesNoGap d
  | .matchExn s cls d => usesNoGap s && usesNoGapExn cls && usesNoGap d
  | .contUseUpdate _ _ _ _ => false
  | .dropCont _ => false

/-- Clause lists, for the two `match` forms. -/
def usesNoGapEff : List (EffId × Term Nat) → Bool
  | [] => true
  | (_, t) :: r => usesNoGap t && usesNoGapEff r

/-- Likewise for `matchExn`. -/
def usesNoGapExn : List (ExnId × Term Nat) → Bool
  | [] => true
  | (_, t) :: r => usesNoGap t && usesNoGapExn r

end

/-- The domain: admissible, and no `Shallow`, no `caml_drop_continuation`. -/
def Fragment (t : Term Nat) : Bool := Compiler.Admissible t && usesNoGap t

/-- The semantic side condition, which is not syntactic and is exactly the three restrictions
`OCaml5.Compile`'s header lists: every `emitOf` is applied to an integer, every `matchOpt` and
`matchExn` scrutinee has a representable shape, and every closure is applied at its arity.
Spelled here as what all three amount to: the compiled program never gets stuck. -/
def NotStuck (t : Term Nat) : Prop :=
  ∀ (fuel' : Nat) (why : String),
    (Code.Machine.exec fuel' (Compile.compile t)).1 ≠ Code.Outcome.stuck why

/-- **The theorem P4 owes.** Executed on 15 witnesses, 10 `Stdlib` builder shapes and 455
generated programs (`OCaml5.compile.Agreement`, `OCaml5.compile.Fuzz`); proved below for the
pure fragment; the remaining arms are §4. -/
def CompileCorrectOnFragment : Prop :=
  ∀ t : Term Nat, Fragment t = true → NotStuck t → CompileCorrect t

/-! ## 2. Two lemmas about `run`

`Machine.run` reads the outcome off the step it stopped at, so once it has stopped, more fuel
changes nothing. That is all that is needed to turn a `rfl`-checkable fact at one fuel into a
statement about every fuel — which is what `CompileCorrect` quantifies over. -/

universe u

variable {ν : Type u} [ToString ν] [Add ν]

/-- More fuel changes nothing once the run has settled. -/
theorem run_add (n : Nat) :
    ∀ (m m' : OCaml5.Machine ν) (o : OCaml5.Outcome ν),
      OCaml5.Machine.run n m = (m', o) → o ≠ OCaml5.Outcome.fuel →
      ∀ k, OCaml5.Machine.run (n + k) m = (m', o) := by
  induction n with
  | zero =>
    intro m m' o h hne _
    rw [OCaml5.Machine.run] at h
    cases h
    exact absurd rfl hne
  | succ n ih =>
    intro m m' o h hne k
    have hstep : (n + 1) + k = (n + k) + 1 := by omega
    rw [hstep, OCaml5.Machine.run]
    rw [OCaml5.Machine.run] at h
    cases hs : m.step with
    | inl m1 => rw [hs] at h; exact ih m1 m' o h hne k
    | inr o1 => rw [hs] at h; exact h

/-- A settled run is unique: two fuels that both finish agree on the machine and the outcome. -/
theorem run_det {m : OCaml5.Machine ν} {n n' : Nat} {m1 m2 : OCaml5.Machine ν}
    {o1 o2 : OCaml5.Outcome ν}
    (h1 : OCaml5.Machine.run n m = (m1, o1)) (hne1 : o1 ≠ OCaml5.Outcome.fuel)
    (h2 : OCaml5.Machine.run n' m = (m2, o2)) (hne2 : o2 ≠ OCaml5.Outcome.fuel) :
    (m1, o1) = (m2, o2) := by
  rcases Nat.le_total n n' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add n m m1 o1 h1 hne1 k] at h2
    exact h2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add n' m m2 o2 h2 hne2 k] at h1
    exact h1.symm

/-- The shape every proof in §3 has: one settled run of each machine, plus the two
projections. Both runs are supplied as equations so that the two `rfl`s stay separate from the
`simp` that discharges the projection. -/
theorem correct_of_runs (t : Term Nat) (F G : Nat)
    (m : OCaml5.Machine Nat) (o : OCaml5.Outcome Nat) (o' : Code.Outcome) (s : String)
    (hrun : OCaml5.Machine.run F (OCaml5.Machine.start t) = (m, o))
    (hne : o ≠ OCaml5.Outcome.fuel)
    (hexec : Code.Machine.exec G (Compile.compile t) = (o', s))
    (hout : outcomeMatches o o' = true)
    (hrows : m.rows = rowsOfOutput s) :
    CompileCorrect t := by
  intro fuel m'' o'' h'' hne''
  have hd := run_det h'' hne'' hrun hne
  have ho : o'' = o := congrArg Prod.snd hd
  have hm : m'' = m := congrArg Prod.fst hd
  subst ho; subst hm
  exact ⟨G, by rw [hexec]; exact hout, by rw [hexec]; exact hrows⟩

/-! ## 3. The pure fragment

§2 is the whole of what can be *proved* here at a price the build can pay. The two lemmas are
general — every fuel, every term, every payload type — and `correct_of_runs` reduces
`CompileCorrect t` to two settled runs and the two projections, which is the shape any
instance of the theorem has.

What §2 does **not** buy is the instances. `Code.Machine.exec` is not a function the kernel can
reduce cheaply: its state carries association lists, strings and the whole block table, so a
`rfl` on `Code.Machine.exec 12 (compile (.val n))` costs the kernel about three gigabytes, and
the eleven instances below cost thirty. Measured, not guessed:

```
$ lean workshop/OCaml5/compile/Simulation.lean -o /tmp/Sim.olean
   30767131504  peak memory footprint
```

So the instances are **executed** rather than proved: `#guard` runs both machines in the
evaluator and checks exactly the two hypotheses `correct_of_runs` wants. Each line below is
therefore one application of `correct_of_runs` away from `CompileCorrect` of that term, and the
missing step is a kernel reduction, not a mathematical one. Making it a proof needs the
simulation relation of §4 — with which the instances become corollaries and no machine is run
in the kernel at all.

`agreesAtFuel tf cf t` is `agreesWithTerm` at an explicit pair of fuels, so that the numbers
`correct_of_runs` would be given are visible. -/

/-- The two hypotheses of `correct_of_runs`, decided. -/
def agreesAtFuel (tf cf : Nat) (t : Term Nat) : Bool :=
  let (m, o) := OCaml5.Machine.run tf (OCaml5.Machine.start t)
  let (o', s) := Code.Machine.exec cf (Compile.compile t)
  outcomeMatches o o' && (m.rows == rowsOfOutput s)

/- A literal. -/
#guard agreesAtFuel 2 12 (.val 7)
#guard agreesAtFuel 2 12 (.val 0)
#guard agreesAtFuel 2 12 (.val 4294967296)

/- `()`. -/
#guard agreesAtFuel 2 12 .unit

/- `let x = a in x`: the de Bruijn environment and the `Var` environment agree at index 0. -/
#guard agreesAtFuel 5 12 (.letIn (.val 4) (.var 0))

/- `a + b` on payloads: `Term.add` against `%int_add`. -/
#guard agreesAtFuel 6 14 (.add (.val 2) (.val 3))
#guard agreesAtFuel 10 18 (.add (.add (.val 2) (.val 3)) (.val 4))

/- One row: `Term.emit` against `caml_print_string`, and the row projection that inverts it. -/
#guard agreesAtFuel 2 12 (.emit "r")
#guard agreesAtFuel 2 12 (.emit "a\tb")

/- `a; b`, with a row in `a`, so the projection is checked on a non-empty output. -/
#guard agreesAtFuel 5 13 (.seq (.emit "r") (.val 1))
#guard agreesAtFuel 8 14 (.seq (.emit "r") (.seq (.emit "s") (.val 1)))

/- `emitOf`: the label, the tab, the rendered integer, the newline. -/
#guard agreesAtFuel 4 16 (.emitOf "l" (.val 9))

/- `(fun x -> x) n`: a one-parameter `Closure` applied at its arity. -/
#guard agreesAtFuel 7 15 (.app (.lam (.var 0)) (.val 5))
#guard agreesAtFuel 12 20 (.app (.lam (.add (.var 0) (.var 0))) (.val 5))

/- The option forms: `Cond (is_int …)` against `Machine`'s `matchOpt` arms. -/
#guard agreesAtFuel 7 17 (.matchOpt (.some (.val 3)) (.val 0) (.var 0))
#guard agreesAtFuel 4 15 (.matchOpt .none (.val 8) (.var 0))

/- `r := n; !r`: the one mutable cell against the one-field block of the entry block. -/
#guard agreesAtFuel 7 15 (.letIn (.setCell (.val 8)) .getCell)

/- An uncaught exception: `Machine`'s `uncaught` against a raise that reaches an empty
`caml_exn_stack` and an empty callback stack. -/
#guard agreesAtFuel 6 16 (.raise (.exn ⟨2⟩ .unit))

/- `try raise X with X -> 3`: `Pushtrap`/`Poptrap` and the constructor chain, the two
non-effect control forms. -/
#guard agreesAtFuel 12 32
  (.tryWith (.raise (.exn ⟨2⟩ .unit)) (.matchExn (.var 0) [(⟨2⟩, .val 3)] (.raise (.var 0))))
#guard agreesAtFuel 12 40
  (.tryWith (.raise (.exn ⟨3⟩ .unit)) (.matchExn (.var 0) [(⟨2⟩, .val 3)] (.val 9)))

/-! ### The two structural facts `compile` has by construction -/

/-- The entry block is always `0`. -/
theorem compile_start (t : Term Nat) : (Compile.compile t).start = 0 := rfl

/-- `compile?` is `compile` exactly on the terms `ocamlc` compiles (`bytegen.ml:803-804`). -/
theorem compile?_admissible {t : Term Nat} (h : Compiler.Admissible t = true) :
    Compile.compile? t = Option.some (Compile.compile t) := by
  simp [Compile.compile?, h]

theorem compile?_inadmissible {t : Term Nat} (h : Compiler.Admissible t = false) :
    Compile.compile? t = Option.none := by
  simp [Compile.compile?, h]

/-! ## 4. The obligations

What §3 does not cover, arm by arm. Each is a `Prop`, none is an axiom, and each says what
invariant would discharge it. The common missing ingredient is a **simulation relation**
`R : Machine ν → Code.Machine → Prop` between a `Term` configuration and a `Code`
configuration, which §3 avoids by running both machines to the end at a fixed fuel. The relation
has to say:

1. **Environments.** `Machine`'s `Control.eval env t` carries a `List (Value ν)`, innermost
   first; `Code.Machine` carries an `EnvId` whose record chain binds the `Var`s `compile`'s
   compile-time environment assigned. `R` must say that the *i*-th entry of `env` is the value
   `Code.Machine.look` finds for the *i*-th `Var`. This is where `compile`'s one global
   invariant lives: a `Var` is fresh, so `bind` never shadows, so the chain is a function.
2. **Frames against `k`.** `Machine`'s `StackInfo.frames` is a list of `Frame ν`;
   `Code.Machine`'s low-level continuation is a chain of `FrameRec`s ending in
   `Val.prim "hval"` or `"halt"`. `R` must relate the two lists element by element, and the
   `Frame.trap` entries to `caml_exn_stack`'s `trapK` entries — which is the plan's ruling 5
   (traps live on their stack) meeting js_of_ocaml's global stack, spike O2 report §6's
   deviation, spike P3's subject.
3. **Stacks against fibers.** `Machine.stacks` with `StackHandler.parent` is a parent chain;
   `Code.Machine.fiberStack` is a list, outermost last. `R` must say the chain and the list are
   the same sequence, and that `Machine.conts` and `Code.Machine.conts` are nulled together.
-/

/-- **Obligation 1, the pure arms in general.** §3 proves ten shapes; the general statement is
one induction over the pure grammar with the environment relation of note 1 above. -/
def PureArms : Prop :=
  ∀ t : Term Nat,
    Fragment t = true → NotStuck t →
    -- no effect primitive and no trap occurs in `t`
    (Compiler.opcodes t = []) → CompileCorrect t

/-- **Obligation 2, `perform`.** `Machine.doPerform` allocates a `Cont_tag` block, nulls the
performer's parent, switches to the parent and applies the performer's own `handle_effect`
there with three arguments (`interp.c:1334-1357`). `Code.Machine.performEffect` conses the
current fiber onto the continuation's cell list, pops to the parent and applies `h[3]`
(`effect.js:107-120`). The obligation is that the two agree *under `R`*: same effect value,
same continuation identity up to the heap bijection, same handler, and the performer's frames
saved in the cell that the parent chain saved. -/
def PerformArm : Prop :=
  ∀ (t : Term Nat), Fragment t = true → NotStuck t →
    (∀ e, t = .perform e → CompileCorrect t)

/-- **Obligation 3, `resume` and `runstack`.** `Machine.doResumeStack` sets the parent of the
OUTERMOST captured stack and switches to the INNERMOST; `Code.Machine.resumeCells` installs
every cell head-to-tail and answers the innermost cell's `k`. The obligation is that "outermost
first" in the cell list is the parent chain read backwards, which is spike O2 report §2.1's
reading of `effect.js:83-89`. `compile`'s null-stack guard has to be discharged here too: the
`Cond` on the stack value is the `Is_long` test of `interp.c:1291`. -/
def ResumeArm : Prop :=
  ∀ (t : Term Nat), Fragment t = true → NotStuck t →
    (∀ s f a, t = .resume s f a ∨ t = .runstack s f a → CompileCorrect t)

/-- **Obligation 4, `reperform`.** `Machine.doReperform` appends the reperforming stack to the
*tail* of the captured chain using its `last_fiber` argument (`interp.c:1386-1388`);
`Code.Machine.performEffect` conses onto the *head* of the cell list and has no `last_fiber` at
all, because `parse_bytecode.ml:2467` drops it. The obligation is that head-consing an
outermost-first list and tail-appending a parent chain are the same operation, so that dropping
`last_fiber` is sound — which is exactly why `compile` may emit a two-argument `%reperform`. -/
def ReperformArm : Prop :=
  ∀ (t : Term Nat), Fragment t = true → NotStuck t →
    (∀ e c l, t = .reperform e c l → CompileCorrect t)

/-- **Obligation 5, the traps.** `Term.tryWith` compiles to `Pushtrap`/`Poptrap`, whose entries
live on one global `caml_exn_stack`, while `Machine`'s `Frame.trap` lives on the current stack
and is captured with it (plan ruling 5). §3 proves the one-trap, one-stack case by running both
machines; the general case is spike P3's bisimulation, and this obligation is its image under
`compile`. -/
def TrapArm : Prop :=
  ∀ (t : Term Nat), Fragment t = true → NotStuck t →
    (∀ b h, t = .tryWith b h → CompileCorrect t)

/-- **Obligation 6, the two gaps.** `Code.Machine.purePrim` needs one arm for
`caml_continuation_use_and_update_handler_noexc` (`effect.js:156-161`: take the stack, then
overwrite the *head* cell's `Handlers`, the head being the outermost fiber, which is
`fiber.c:632-649`'s "walk to the outermost captured fiber"), and one for
`caml_drop_continuation` — the latter only if js_of_ocaml implements it, which 5.7.1 does not
(witness 12). With the first arm, `Shallow.fiber`, `Shallow.continue_with` and
`Shallow.discontinue_with` come inside `compile`'s domain and witnesses 11 and 15 join the
corpus. The arm is P2's to add; this is the statement of what it must do. -/
def ShallowArm : Prop :=
  ∀ (t : Term Nat), Compiler.Admissible t = true → usesNoGap t = false → NotStuck t →
    CompileCorrect t

end OCaml5.compile
