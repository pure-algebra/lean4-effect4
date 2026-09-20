import Effect4.Api.Supervision
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Api.Frontier
import Effect4.Laws.Auto.Inversion
import Effect4.Laws.Program.Size
import Effect4.Laws.Auto.Obligations

/-!
# Laws.Api.Supervision — the static table and the running machine say the same thing

Three groups.

**(a) Diagnostic fork flags.** The daemon flag on a `RunEvent.forked` is decided by the fork
site, never by the run. `spawn` is where every fork of the machine goes through, and it
stamps the options it was handed (`Machine/Fibers.lean:908-923`); the four arms above it hand
it either the site's own written options (`fork`) or options with `daemon := true` forced
(`forkIn`, `forkScoped`, a race entrant, a parallel close's finalizer). So each arm appends
exactly one `forked` event, with the flag the static `ForkKind` carries. The starting half of
a fork emits a `scheduledTask` and no `forked`, which is why the equations read past it.

The static half is whole-program and has no case per constructor: `forkSitesOf_child_flag` is
the generic node step, and `supervision_child_flag` lifts it through the fold by the generic
child step — a node's children are what the generated layer view lists, and a child is
smaller than its node by one fold (`sizeAlg`) and one lemma (`size_child_lt`).

**(b) What a status can change by.** `statusOf` is a function of four observations — the
fiber's exit, the fiber that tracks it, the scope link on it, and its origin — so it changes only when one of the four does. That is the `guard_persists` shape
(`Laws/Api/Guard.lean:22`) for supervision: `status_persists` states it, and the machine
writes that move the observations are named beside it. `spawn_status_fresh` is DI-75 in one
theorem: a child is a loose daemon from the moment it exists until the command that holds it
runs.

**(c) The parked fibers.** `awaits` (`Program/Admit.lean:39`) and `fiberStatuses` agree:
every outstanding host call names a fiber of the machine whose status is live, and a fiber
whose status is `.exited` is not parked, so it registers no call. Both directions need one
machine fact — an exited fiber is off its guard, because `RunFiber.publish` writes the exit
and clears the guard together (`Machine/Fibers.lean:1696-1704`) — and it is a hypothesis
here, `exitedUnparked`, because a machine written by hand need not have it.
-/

set_option autoImplicit false
-- The `DecidableEq` section variables are what the machine's own definitions take; a law
-- about a definition that does not need them is stated in the same section anyway.
set_option linter.unusedSectionVars false

namespace Effect4.Api

open Effect4 Effect4.Machine Effect4.Program

universe u v

/-- Diagnostic trace projection. Runtime supervision reads fiber origins. -/
def TraceFacts.forkedOf {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {κ η : Type (max u v)} (trace : List (RunEvent ν σ β ε δ ι α χ κ η)) :
    List (FiberId × FiberId × Bool) :=
  trace.filterMap fun
    | .forked parent child daemon => some (parent, child, daemon)
    | _ => none

/-! ## A measure on the program, so a fold's law is one generic step

`supervision` recurses the generic way: a node's sites are its own plus its children's, where
"its children" is what the generated layer view lists. To reason about that by the same
generic step, a child must be smaller than its node: the node count `sizeAlg` and the lemmas
`size_pos` / `size_child_lt` of `Laws/Program/Size.lean`, shared with the printer's
completeness. -/

variable {Op : Type}

/-! ## (a) The static half: every site of a program is the table's -/

/-- A site the table calls a tracked child is a `fork` whose program wrote `daemon := false`.
The generic node step: the only place a `ForkSite` is made. -/
theorem forkSitesOf_child_flag {R : EffFam → Type} (fam : EffFam) (ctor : String)
    (args : List (ArgF Op R)) (p : List Nat) (s : ForkSite)
    (member : s ∈ forkSitesOf fam ctor args p) (kind : s.kind = ForkKind.child) :
    s.options.daemon = false := by
  unfold forkSitesOf at member
  aesop

/-- Every other kind of site forks a daemon, by the kind alone. -/
theorem forkSite_isDaemon (s : ForkSite) : s.isDaemon = true ↔ s.kind ≠ ForkKind.child := by
  unfold ForkSite.isDaemon
  aesop (add norm simp ForkKind.isDaemon)

/-- A site in `atChildPaths` is a site of one of the readers. -/
theorem mem_atChildPaths : ∀ (readers : List (List Nat → List ForkSite)) (p : List Nat)
    (i : Nat) (s : ForkSite), s ∈ atChildPaths readers p i →
    ∃ reader ∈ readers, ∃ q, s ∈ reader q
  | [], _, _, _, member => by aesop (add norm simp atChildPaths)
  | reader :: rest, p, i, s, member => by
    have ih := mem_atChildPaths rest p (i + 1) s
    aesop (add norm simp atChildPaths) (add safe forward ih)

/-- A reader among a node's folded children is the fold of a child the view lists. -/
theorem mem_childReaders : ∀ (args : List (ArgF Op (EffSelfCarrier Op)))
    (reader : List Nat → List ForkSite),
    reader ∈ childReaders (args.map (ArgF.fold superAlg)) →
    ∃ (fam' : EffFam) (c : EffSelfCarrier Op fam'),
      ArgF.child fam' c ∈ args ∧ reader = cataFam superAlg fam' c :=
  fun args reader member => by
    unfold childReaders at member
    rw [List.mem_filterMap] at member
    obtain ⟨a, ha, hmatch⟩ := member
    rw [List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    cases b <;> aesop (add norm simp ArgF.fold)

/-- The fold's law by node count: at each node the sites are the table's own plus the
children's, and a child is smaller. -/
theorem supervision_child_flag_bounded :
    ∀ (n : Nat) (fam : EffFam) (e : EffSelfCarrier Op fam),
      cataFam sizeAlg fam e ≤ n →
      ∀ (p : List Nat) (s : ForkSite), s ∈ cataFam superAlg fam e p →
        s.kind = ForkKind.child → s.options.daemon = false
  | 0, fam, e, size, _, _, _, _ => absurd size (by have := size_pos fam e; omega)
  | n + 1, fam, e, size, p, s, member, kind => by
    have hb := cata_build superLayer fam (view fam e).1 (view fam e).2 e (build_view fam e)
    rw [show (superAlg : EffAlgebra Op SiteReader) = EffAlgebra.ofLayer superLayer from rfl, hb,
      superLayer, List.mem_append] at member
    rcases member with node | child
    · exact forkSitesOf_child_flag fam _ _ p s node kind
    · obtain ⟨reader, hreader, q, hq⟩ := mem_atChildPaths _ _ _ _ child
      obtain ⟨fam', c, hc, rfl⟩ := mem_childReaders _ _ hreader
      have hlt := size_child_lt fam e fam' c hc
      exact supervision_child_flag_bounded n fam' c (by omega) q s hq kind

/-- **The static table is coherent, whole-program.** Every site of a program that the table
calls a tracked child is a `fork` whose program wrote `daemon := false` — so the flag the
machine will stamp there is the flag the site carries. One proof, through the generic node
step and the generic child step: no case per constructor. -/
theorem supervision_child_flag (e : Effect4.Program.Eff Op) (s : ForkSite)
    (member : s ∈ supervision e) (kind : s.kind = ForkKind.child) : s.options.daemon = false :=
  supervision_child_flag_bounded (cataFam sizeAlg .eff e) .eff e (Nat.le_refl _) [] s member kind

/-- The same fact read off `isDaemon`: a site of a program that does not fork a daemon was
written with `daemon := false`. -/
theorem supervision_isDaemon_flag (e : Effect4.Program.Eff Op) (s : ForkSite)
    (member : s ∈ supervision e) (daemon : s.isDaemon = false) : s.options.daemon = false := by
  refine supervision_child_flag e s member ?_
  have := forkSite_isDaemon s
  aesop

/-! ## (a) The machine half: what a fork stamps -/

section MachineForks

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]

def M1Trace.forkedOf_append (a b : List (RunEvent ν σ β ε δ ι α χ κ η)) : ProofGraph.Obligation (
    TraceFacts.forkedOf (a ++ b) = TraceFacts.forkedOf a ++ TraceFacts.forkedOf b) := ⟨⟩
#proof_wanted M1Trace.forkedOf_append

/-- Reading the `forked` events of two traces in turn. -/
theorem forkedOf_append (a b : List (RunEvent ν σ β ε δ ι α χ κ η)) :
    TraceFacts.forkedOf (a ++ b) = TraceFacts.forkedOf a ++ TraceFacts.forkedOf b := List.filterMap_append ..

/-- `spawn` appends exactly one event, naming the parent, the fresh id and the options'
daemon flag (`Machine/Fibers.lean:908-923`). -/
theorem spawn_trace (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).1.trace =
      m.trace ++ [RunEvent.forked parent.id ⟨m.nextId⟩ options.daemon] := rfl

def M1Trace.spawn_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) : ProofGraph.Obligation (
    TraceFacts.forkedOf (spawn interp m parent program options).1.trace =
      TraceFacts.forkedOf m.trace ++ [(parent.id, ⟨m.nextId⟩, options.daemon)]) := ⟨⟩
#proof_wanted M1Trace.spawn_forked

theorem spawn_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    TraceFacts.forkedOf (spawn interp m parent program options).1.trace =
      TraceFacts.forkedOf m.trace ++ [(parent.id, ⟨m.nextId⟩, options.daemon)] := by
  aesop (add norm simp [spawn_trace, TraceFacts.forkedOf])

/-- The id the spawn mints is the machine's `nextId`. -/
theorem spawn_child (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).2.2 = ⟨m.nextId⟩ := rfl

/-- The fresh id is consumed. -/
theorem spawn_nextId (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).1.nextId = m.nextId + 1 := rfl

/-- The spawn appends the child and touches no other fiber (`:922`); the child starts with no
exit, no observer and no child of its own (`RunFiber.make`, `:259-275`). -/
def M1Origin.spawn_fibers (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) : ProofGraph.Obligation (∃ child : RunFiber ν σ β ε δ ι α χ κ φ,
      (spawn interp m parent program options).1.fibers = m.fibers ++ [child] ∧
        child.id = ⟨m.nextId⟩ ∧ child.exit = none ∧ child.observers = [] ∧
        child.children = [] ∧ child.origin = .forked parent.id options.daemon []) := ⟨⟩

theorem spawn_fibers (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    ∃ child : RunFiber ν σ β ε δ ι α χ κ φ,
      (spawn interp m parent program options).1.fibers = m.fibers ++ [child] ∧
        child.id = ⟨m.nextId⟩ ∧ child.exit = none ∧ child.observers = [] ∧
        child.children = [] ∧ child.origin = .forked parent.id options.daemon [] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

def M1Trace.start_forked (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediately : Bool) : ProofGraph.Obligation (
    TraceFacts.forkedOf (start m parent child immediately).1.trace = TraceFacts.forkedOf m.trace) := ⟨⟩
#proof_wanted M1Trace.start_forked

/-- Starting a child emits a `scheduledTask` or nothing; either way, no `forked` (`:925-933`). -/
theorem start_forked (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediately : Bool) :
    TraceFacts.forkedOf (start m parent child immediately).1.trace = TraceFacts.forkedOf m.trace := by
  cases immediately <;>
    aesop (add norm simp [start, RunMachine.emit, RunMachine.arm, TraceFacts.forkedOf])

def M1Trace.fork_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) : ProofGraph.Obligation (
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.fork program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, options.daemon)]) := ⟨⟩
#proof_wanted M1Trace.fork_forked

/-- `fork`: the flag the program wrote (`:1191-1201`, `Effect.forkChild` / `forkDetach`). -/
theorem fork_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) :
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.fork program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, options.daemon)] := by
  rw [withFiber_fork]
  cases hd : options.daemon <;> aesop (add norm simp [hd, start_forked, spawn_forked])

def M1Trace.forkIn_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat) : ProofGraph.Obligation (
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkIn program options scope)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)]) := ⟨⟩
#proof_wanted M1Trace.forkIn_forked

/-- `forkIn`: a daemon at the pin, whatever the program wrote (`:1205`, `:5366`). -/
theorem forkIn_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat) :
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkIn program options scope)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] := by
  aesop (add norm simp [withFiber_forkIn, start_forked, spawn_forked])

def M1Trace.forkScoped_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (_ambient : interp.ambientScope f.context = some scope) : ProofGraph.Obligation (
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)]) := ⟨⟩
#proof_wanted M1Trace.forkScoped_forked

/-- `forkScoped` with an ambient scope: `forkIn` on it (`:1213`, `:5406`). -/
theorem forkScoped_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (ambient : interp.ambientScope f.context = some scope) :
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] := by
  have arm := withFiber_forkScoped_ambient interp m f yielding program options scope ambient
  aesop (add norm simp [arm, start_forked, spawn_forked])

def M1Trace.forkScoped_none_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions)
    (_ambient : interp.ambientScope f.context = none) : ProofGraph.Obligation (
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options)).machine.trace = TraceFacts.forkedOf m.trace) := ⟨⟩
#proof_wanted M1Trace.forkScoped_none_forked

/-- `forkScoped` with no ambient scope forks nothing at all (`:1218-1221`). -/
theorem forkScoped_none_forked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions)
    (ambient : interp.ambientScope f.context = none) :
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options)).machine.trace = TraceFacts.forkedOf m.trace := by
  have arm := withFiber_forkScoped_none interp m f yielding program options ambient
  aesop (add norm simp arm)

def M1Trace.launchEntrant_forked (interp : RunInterp ν σ β ε δ ι α χ St κ) (raceId : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) : ProofGraph.Obligation (
    TraceFacts.forkedOf (launchEntrant interp raceId m host program).1.trace =
      TraceFacts.forkedOf m.trace ++ [(host.id, ⟨m.nextId⟩, true)]) := ⟨⟩
#proof_wanted M1Trace.launchEntrant_forked

/-- A race entrant: an immediate daemon (`:938-942`, `:1521`). -/
theorem launchEntrant_forked (interp : RunInterp ν σ β ε δ ι α χ St κ) (raceId : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) :
    TraceFacts.forkedOf (launchEntrant interp raceId m host program).1.trace =
      TraceFacts.forkedOf m.trace ++ [(host.id, ⟨m.nextId⟩, true)] := by
  aesop (add norm simp [launchEntrant, spawn_forked])

def M1Trace.forkFinalizers_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (host : RunFiber ν σ β ε δ ι α χ κ φ) : ProofGraph.Obligation (
    ∀ (programs : List κ) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      ∃ new, TraceFacts.forkedOf (forkFinalizers interp m host programs).1.trace =
        TraceFacts.forkedOf m.trace ++ new ∧ new.all (fun e => e.2.2) = true) := ⟨⟩
#proof_wanted M1Trace.forkFinalizers_forked

/-- A parallel scope close forks one immediate daemon per finalizer (`:948-954`, `:3820`):
every event it adds carries `true`. -/
theorem forkFinalizers_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (host : RunFiber ν σ β ε δ ι α χ κ φ) :
    ∀ (programs : List κ) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      ∃ new, TraceFacts.forkedOf (forkFinalizers interp m host programs).1.trace =
        TraceFacts.forkedOf m.trace ++ new ∧ new.all (fun e => e.2.2) = true
  | [], m => ⟨[], by aesop (add norm simp forkFinalizers)⟩
  | program :: rest, m => by
    have ih := forkFinalizers_forked interp host rest
      (spawn interp m host program ⟨true, true, Supervision.MaskMode.inherit⟩).1
    obtain ⟨new, hnew, hall⟩ := ih
    exact ⟨(host.id, ⟨m.nextId⟩, true) :: new,
      by aesop (add norm simp [forkFinalizers, hnew, spawn_forked]),
      by aesop (add norm simp hall)⟩

/-! ### The same arms on the shared path the term evaluator takes -/

def M1Trace.action_fork_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (program : κ) (options : Supervision.ForkOptions)
    (answer : FiberAction.Answer ν σ β ε δ ι α χ κ φ) : ProofGraph.Obligation (
    TraceFacts.forkedOf (FiberAction.fork interp m f yielding program options answer).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, options.daemon)]) := ⟨⟩
#proof_wanted M1Trace.action_fork_forked

theorem action_fork_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (program : κ) (options : Supervision.ForkOptions)
    (answer : FiberAction.Answer ν σ β ε δ ι α χ κ φ) :
    TraceFacts.forkedOf (FiberAction.fork interp m f yielding program options answer).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, options.daemon)] := by
  unfold FiberAction.fork
  cases hd : options.daemon <;> aesop (add norm simp [hd, start_forked, spawn_forked])

def M1Trace.action_forkIn_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (program : κ) (options : Supervision.ForkOptions) (scope : Nat)
    (answer : FiberAction.Answer ν σ β ε δ ι α χ κ φ) : ProofGraph.Obligation (
    TraceFacts.forkedOf (FiberAction.forkIn interp m f yielding program options scope answer).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)]) := ⟨⟩
#proof_wanted M1Trace.action_forkIn_forked

theorem action_forkIn_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (program : κ) (options : Supervision.ForkOptions) (scope : Nat)
    (answer : FiberAction.Answer ν σ β ε δ ι α χ κ φ) :
    TraceFacts.forkedOf (FiberAction.forkIn interp m f yielding program options scope answer).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] := by
  aesop (add norm simp [FiberAction.forkIn, start_forked, spawn_forked])

def M1Trace.action_forkScoped_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (program : κ) (options : Supervision.ForkOptions) (scope : Nat)
    (answer : FiberAction.Answer ν σ β ε δ ι α χ κ φ)
    (_ambient : interp.ambientScope f.context = some scope) : ProofGraph.Obligation (
    TraceFacts.forkedOf (FiberAction.forkScoped interp m f yielding program options answer).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)]) := ⟨⟩
#proof_wanted M1Trace.action_forkScoped_forked

theorem action_forkScoped_forked (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (program : κ) (options : Supervision.ForkOptions) (scope : Nat)
    (answer : FiberAction.Answer ν σ β ε δ ι α χ κ φ)
    (ambient : interp.ambientScope f.context = some scope) :
    TraceFacts.forkedOf (FiberAction.forkScoped interp m f yielding program options answer).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] := by
  aesop (add norm simp [FiberAction.forkScoped, ambient, start_forked, spawn_forked])

def M1Trace.supervision_static (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (raceId : Nat) (_ambient : interp.ambientScope f.context = some scope) : ProofGraph.Obligation (
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.fork program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, options.daemon)] ∧
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkIn program options scope)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] ∧
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] ∧
    TraceFacts.forkedOf (launchEntrant interp raceId m f program).1.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)]) := ⟨⟩
#proof_wanted M1Trace.supervision_static

/-- **Diagnostic fork flags.** At each of the four forks the machine can make, the `forked` event
it appends carries the flag the fork *site* carries: the program's own flag at a `fork`,
`true` at a `forkIn`, a `forkScoped` and a race entrant. Nothing about the run enters. -/
theorem TraceFacts.supervision_static_flags (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (raceId : Nat) (ambient : interp.ambientScope f.context = some scope) :
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.fork program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, options.daemon)] ∧
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkIn program options scope)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] ∧
    TraceFacts.forkedOf (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options)).machine.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] ∧
    TraceFacts.forkedOf (launchEntrant interp raceId m f program).1.trace =
      TraceFacts.forkedOf m.trace ++ [(f.id, ⟨m.nextId⟩, true)] :=
  ⟨fork_forked interp m f yielding program options,
   forkIn_forked interp m f yielding program options scope,
   forkScoped_forked interp m f yielding program options scope ambient,
   launchEntrant_forked interp raceId m f program⟩

end MachineForks

/-! ## (b) What a fiber's status can change by -/

/-- The next id is fresh: no fiber carries it and no fiber tracks it. A run keeps this —
`spawn` mints the id from `nextId` and bumps it (`Machine/Fibers.lean:912-922`) — and a
machine written by hand need not, so the laws that need it take it. -/
def NextIdFresh (m : Machine) : Prop :=
  ∀ g ∈ m.fibers, g.id ≠ ⟨m.nextId⟩ ∧ (⟨m.nextId⟩ : FiberId) ∉ g.children

/-- The decidable twin, so a battery can pin it on a real run. -/
def nextIdFresh (m : Machine) : Bool :=
  m.fibers.all fun g => g.id != ⟨m.nextId⟩ && !g.children.contains ⟨m.nextId⟩

theorem nextIdFresh_iff (m : Machine) : nextIdFresh m = true ↔ NextIdFresh m := by
  unfold nextIdFresh NextIdFresh
  aesop

/-- **status_persists.** A fiber's status is a function of four observations and nothing
else: its own exit, the fiber that tracks it, the scope it is pinned to, and its origin. So it survives every change to the machine except a change to one of those four —
the fiber exits, its parent starts or stops tracking it, its pin is made or dropped, or its origin changes. This is `guard_persists`' shape (`Laws/Api/Guard.lean:22`) for supervision. -/
def M1Origin.status_persists (m m' : Machine) (f f' : Fiber)
    (_exit : f'.exit = f.exit)
    (_track : parentOf m' f'.id = parentOf m f.id)
    (_pin : pinOf f' = pinOf f)
    (_origin : f'.origin = f.origin) : ProofGraph.Obligation (statusOf m' f' = statusOf m f) := ⟨⟩
#proof_wanted M1Origin.status_persists

theorem status_persists (m m' : Machine) (f f' : Fiber)
    (exit : f'.exit = f.exit)
    (track : parentOf m' f'.id = parentOf m f.id)
    (pin : pinOf f' = pinOf f)
    (origin : f'.origin = f.origin) :
    statusOf m' f' = statusOf m f := by
  unfold statusOf
  aesop

/-- The first of the four is written in one place: `RunFiber.publish` (`:1696-1704`). -/
theorem publish_status (m : Machine) (f : Fiber) (exit : ExitV) :
    statusOf m (f.publish exit) = FiberStatus.exited exit := by aesop

/-- `.exited` says exactly that the fiber has exited, and nothing else produces it. -/
theorem status_exited_iff (m : Machine) (f : Fiber) (exit : ExitV) :
    statusOf m f = FiberStatus.exited exit ↔ f.exit = some exit := by
  unfold statusOf
  aesop

/-- A fiber that has not exited has a live status. -/
theorem status_live_of_none (m : Machine) (f : Fiber) (h : f.exit = none) :
    (statusOf m f).live = true := by
  unfold statusOf
  aesop (add norm simp FiberStatus.live)

/-- Nobody tracks an id no fiber's `children` holds. -/
theorem parentOf_append_none (fibers : List Fiber) (child : Fiber) (id : FiberId)
    (before : ∀ g ∈ fibers, id ∉ g.children) (fresh : child.children = []) :
    ((fibers ++ [child]).find? fun g => g.children.contains id) = none := by aesop

/-- Appending a fiber with no children of its own leaves every tracking answer alone. -/
theorem parentOf_append_same (fibers : List Fiber) (child : Fiber) (id : FiberId)
    (fresh : child.children = []) :
    ((fibers ++ [child]).find? fun g => g.children.contains id) =
      (fibers.find? fun g => g.children.contains id) := by aesop

/-- **DI-75 in one theorem.** A spawned fiber is a loose daemon the moment it exists: nothing
tracks it (tracking is `Cmd.trackChild`, run after its start, `:1903-1910`) and nothing pins
it (`Cmd.link`, likewise after its start, `:1208`), while its origin already records the fork. Between the fork and the command that holds it, even a tracked child is
unheld — which is why a `daemonsQuiet` reading is a reading of a settled machine. -/
theorem spawn_status_fresh
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (m : Machine)
    (parent : Fiber) (program : NCode) (options : Supervision.ForkOptions)
    (fresh : NextIdFresh m) (child : Fiber)
    (member : child ∈ (spawn interp m parent program options).1.fibers)
    (id : child.id = ⟨m.nextId⟩) :
    statusOf (spawn interp m parent program options).1 child = FiberStatus.daemon := by
  obtain ⟨new, hfib, hid, hexit, hobs, hchildren, horigin⟩ :=
    spawn_fibers interp m parent program options
  rw [hfib, List.mem_append] at member
  have hsame : child = new := by
    rcases member with old | fresh'
    · exact absurd id (fresh child old).1
    · aesop
  subst hsame
  have hparent : parentOf (spawn interp m parent program options).1 child.id = none := by
    unfold parentOf
    rw [id, hfib,
      parentOf_append_none m.fibers child ⟨m.nextId⟩ (fun g hg => (fresh g hg).2) hchildren]
    rfl
  have hpin : pinOf child = none := by
    unfold pinOf
    rw [hobs]
    rfl
  unfold statusOf
  rw [hexit, hparent, hpin, horigin]

/-- A spawn changes no existing fiber's status: it appends a fiber with no children, touches
no other, and retains every existing origin. -/
theorem spawn_status_other
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (m : Machine)
    (parent : Fiber) (program : NCode) (options : Supervision.ForkOptions)
    (_fresh : NextIdFresh m) (g : Fiber) (_member : g ∈ m.fibers) :
    statusOf (spawn interp m parent program options).1 g = statusOf m g := by
  obtain ⟨new, hfib, _, _, _, hchildren, _⟩ := spawn_fibers interp m parent program options
  refine status_persists m (spawn interp m parent program options).1 g g rfl ?_ rfl rfl
  unfold parentOf
  rw [hfib, parentOf_append_same m.fibers new g.id hchildren]

/-! ## (c) `fiberStatuses` and `awaits` agree on which fibers are parked -/

/-- Every outstanding host call names a parked fiber of the machine, at its own token. -/
theorem awaits_parked (m : Machine) (a : Await) (member : a ∈ Program.awaits m) :
    ∃ f ∈ m.fibers, f.id = a.1 ∧ f.parked = Parked.withGuard a.2.1 := by
  unfold Program.awaits at member
  rw [List.mem_filterMap] at member
  obtain ⟨f, hf, hmatch⟩ := member
  cases hp : f.parked with
  | notParked => rw [hp] at hmatch; aesop
  | withGuard token => rw [hp] at hmatch; aesop

/-- An exited fiber is off its guard, so it registers no outstanding call of its own. -/
theorem exited_notParked (m : Machine) (unparked : exitedUnparked m = true) (f : Fiber)
    (member : f ∈ m.fibers) (exit : ExitV) (status : statusOf m f = FiberStatus.exited exit) :
    f.parked = Parked.notParked := by
  have hexit : f.exit = some exit := (status_exited_iff m f exit).mp status
  unfold exitedUnparked at unparked
  have hall := List.all_eq_true.mp unparked f member
  rw [hexit] at hall
  aesop

/-- A parked fiber has not exited, so `fiberStatuses` reports it live. -/
theorem parked_status_live (m : Machine) (unparked : exitedUnparked m = true) (f : Fiber)
    (member : f ∈ m.fibers) (token : Nat) (parked : f.parked = Parked.withGuard token) :
    (statusOf m f).live = true := by
  unfold exitedUnparked at unparked
  have hall := List.all_eq_true.mp unparked f member
  rw [parked] at hall
  have hexit : f.exit = none := by
    cases hx : f.exit with
    | none => rfl
    | some e => rw [hx] at hall; aesop
  exact status_live_of_none m f hexit

/-- **The agreement.** Every outstanding host call names a fiber whose entry in
`fiberStatuses` is live: `awaits` and `fiberStatuses` never disagree about a parked fiber. -/
theorem awaits_live (m : Machine) (unparked : exitedUnparked m = true) (a : Await)
    (member : a ∈ Program.awaits m) :
    ∃ f ∈ m.fibers, f.id = a.1 ∧ (a.1, statusOf m f) ∈ fiberStatuses m ∧
      (statusOf m f).live = true := by
  obtain ⟨f, hf, hid, hparked⟩ := awaits_parked m a member
  have live := parked_status_live m unparked f hf a.2.1 hparked
  unfold fiberStatuses
  aesop

/-! ## The property the check decides -/

/-- `daemonsQuiet` decides `Supervised`: no fiber of the machine is a loose daemon. -/
theorem daemonsQuiet_iff (m : Machine) : daemonsQuiet m = true ↔ Supervised m := by
  unfold daemonsQuiet unpinnedDaemonsAlive fiberStatuses Supervised
  rw [List.isEmpty_iff, List.filterMap_eq_nil_iff]
  constructor
  · intro quiet f hf
    have := quiet (f.id, statusOf m f) (List.mem_map_of_mem hf)
    aesop
  · intro supervised entry hentry
    rw [List.mem_map] at hentry
    aesop

/-- A finished machine is quiet: every fiber has exited, so none is a live daemon. -/
theorem finished_daemonsQuiet (m : Machine) (h : m.finished = true) : daemonsQuiet m = true := by
  rw [daemonsQuiet_iff]
  intro f hf
  have hsome := List.all_eq_true.mp h f hf
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨exit, hexit⟩ := hsome
  rw [(status_exited_iff m f exit).mpr hexit]
  aesop

/-- **The property, at the observation.** A terminated observation is a quiet one: no unpinned
daemon is alive, because nothing is alive. What `daemonsQuiet` adds is that it is decidable at
every *other* observation too, where the run has not ended and the question has content. -/
theorem terminated_daemonsQuiet (m : Machine)
    (h : HostProtocol.observe m = HostProtocol.State.terminated) : daemonsQuiet m = true :=
  finished_daemonsQuiet m ((observe_terminated_iff .tape m).mp h).2

end Effect4.Api

-- BEGIN M1 PHASE B Api.Supervision
/-! Phase B integration fragment: unbuilt obligations only. Merge after the existing
owner declarations; do not add an import of the file this fragment is appended to. -/

set_option autoImplicit false

namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program

universe u v

/-- Laws-side projection of the stored id and origin; includes roots and paths. -/
def originEntries {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St κ φ η : Type (max u v)} (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    List (FiberId × Origin) :=
  m.fibers.map fun f => (f.id, f.origin)

namespace M1Origin

section MachineForks
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]

def spawn_origins (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) : ProofGraph.Obligation
    (originEntries (spawn interp m parent program options site).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked parent.id options.daemon site)]) := ⟨⟩
#proof_wanted spawn_origins

def start_origins (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediate : Bool) :
    ProofGraph.Obligation
    (originEntries (start m parent child immediate).1 = originEntries m) := ⟨⟩
#proof_wanted start_origins

/-- Exact replacement shape: state retains the explicit action/list-cell path. -/
def supervision_static (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (scope raceId : Nat)
    (site entrantSite : List Nat)
    (_ambient : interp.ambientScope f.context = some scope) : ProofGraph.Obligation
    (originEntries (evaluatePrim.withFiber interp m f yielding
        (.fork program options site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id options.daemon site)] ∧
    originEntries (evaluatePrim.withFiber interp m f yielding
        (.forkIn program options scope site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true site)] ∧
    originEntries (evaluatePrim.withFiber interp m f yielding
        (.forkScoped program options site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true site)] ∧
    originEntries (launchEntrant interp raceId m f program entrantSite).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true entrantSite)]) := ⟨⟩
#proof_wanted supervision_static

def forkScoped_none_origins (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat)
    (_ambient : interp.ambientScope f.context = none) : ProofGraph.Obligation
    (originEntries (evaluatePrim.withFiber interp m f yielding
      (.forkScoped program options site)).machine = originEntries m) := ⟨⟩
#proof_wanted forkScoped_none_origins

end MachineForks

/-- Loaded roots are roots by their stored field, independent of diagnostics. -/
def load_origins (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) : ProofGraph.Obligation
    (originEntries (Api.load program fuel answers) = [(Api.root, Origin.root)]) := ⟨⟩

/-- One located source fork, its decoded action, and its stamp. Static membership
is frozen separately with exactly the same parameters and premises.
No claim that the point is ever reached is made. -/
def source_fork (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions)
    (_located : Node.at_ (.eff program) point.path = some (.eff (.withFiber (.fork body options))))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) : ProofGraph.Obligation
    (let q := point.child 0
     let action : NAction := .fork (resolve program (q.child 0)) options q.path
     let site : ForkSite := ⟨q.path, if options.daemon then .daemon else .child, options⟩
     actionAt program point = some action ∧
      originEntries (evaluatePrim.withFiber (interpOf program table) m parent yielding action).machine =
        originEntries m ++ [(⟨m.nextId⟩, .forked parent.id site.isDaemon site.path)]) := ⟨⟩
#proof_wanted source_fork

def source_forkIn (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (scopeTerm : Term) (scope : Nat)
    (_located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkIn body options scopeTerm))))
    (_scope : evalTerm point.env scopeTerm = some (Val.scopeHandle scope))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) : ProofGraph.Obligation
    (let q := point.child 0
     let action : NAction := .forkIn (resolve program (q.child 0)) options scope q.path
     let site : ForkSite := ⟨q.path, .pinned (some scopeTerm), options⟩
     actionAt program point = some action ∧
      originEntries (evaluatePrim.withFiber (interpOf program table) m parent yielding action).machine =
        originEntries m ++ [(⟨m.nextId⟩, .forked parent.id site.isDaemon site.path)]) := ⟨⟩
#proof_wanted source_forkIn

/-- The supplied scope is the callback argument; this does not bypass or prove
successful evaluation of forkScoped's earlier ambient-service read. -/
def source_forkScoped (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (scope : Nat)
    (_located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkScoped body options))))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) : ProofGraph.Obligation
    (let q := point.child 0
     let action : NAction := .forkIn (resolve program (q.child 0)) options scope q.path
     let site : ForkSite := ⟨q.path, .pinned none, options⟩
     actionAt program point = some .ambientScope ∧ forkScopedAt program point scope = some action ∧
      originEntries (evaluatePrim.withFiber (interpOf program table) m parent yielding action).machine =
        originEntries m ++ [(⟨m.nextId⟩, .forked parent.id site.isDaemon site.path)]) := ⟨⟩
#proof_wanted source_forkScoped

/-- Race creation records the list cursor, but creates no child yet. -/
def source_race (program : NativeEff) (point : Point) (entrants : Effs NativeOp)
    (_located : Node.at_ (.eff program) point.path = some (.eff (.withFiber (.raceAll entrants))))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) : ProofGraph.Obligation
    (let q := (point.child 0).child 0
     let codes := actionAt.entrants entrants q
     actionAt program point = some (.raceAll codes (some q.path)) ∧
      originEntries (beginRace (interpOf program table) m parent yielding codes (some q.path)).machine =
        originEntries m ∧
      (beginRace (interpOf program table) m parent yielding codes (some q.path)).machine.races.map
        (fun r => r.nextSite) = m.races.map (fun r => r.nextSite) ++ [some q.path]) := ⟨⟩
#proof_wanted source_race

/-- A list cons at an actual source path is the static row for that launch. -/
def source_race_site (program body : NativeEff) (rest : Effs NativeOp) (path : List Nat)
    (_located : Node.at_ (.eff program) path = some (.effs (.cons body rest))) : ProofGraph.Obligation
    ((⟨path, .raceEntrant, raceEntrantOptions⟩ : ForkSite) ∈ supervision program) := ⟨⟩
#proof_wanted source_race_site

/-- Exact local launch boundary, including the no-accepted-answer condition.
The driver may stop between launches; nothing here forces the next one to occur. -/
def race_launch_origins (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : Machine) (raceId : Nat) (race : Race EffName EffThunk Val Err Defect FiberId Ann)
    (parent : Fiber) (code : NCode) (remaining : List NCode) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (_race : m.race? raceId = some race) (_programs : race.programs = code :: remaining)
    (_open : race.state.accepted.isSome = false) (_parent : m.fiber? race.host = some parent) :
    ProofGraph.Obligation
    (originEntries (driveStep interp m (.launch raceId) rest).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked parent.id true (race.nextSite.getD []))] ∧
      ((driveStep interp m (.launch raceId) rest).1.race? raceId).map (fun r => r.nextSite) =
        some (race.nextSite.map (fun path => path ++ [1]))) := ⟨⟩
#proof_wanted race_launch_origins

/-- Symbolic two-entrant path control, not a claim that both entrants run. -/
def source_two_race_paths (program first second : NativeEff) (point : Point)
    (_located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.raceAll (.cons first (.cons second .nil)))))) : ProofGraph.Obligation
    (let q := (point.child 0).child 0
     actionAt program point = some (.raceAll
       [compileEff first (q.child 0), compileEff second ((q.child 1).child 0)] (some q.path))) := ⟨⟩
#proof_wanted source_two_race_paths

def source_fork_site (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions)
    (_located : Node.at_ (.eff program) point.path = some (.eff (.withFiber (.fork body options))))
    (_table : RowTable) (_m : Machine) (_parent : Fiber) (_yielding : Bool) : ProofGraph.Obligation
    (let q := point.child 0
     let site : ForkSite := ⟨q.path, if options.daemon then .daemon else .child, options⟩
     site ∈ supervision program) := ⟨⟩
#proof_wanted source_fork_site

def source_forkIn_site (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (scopeTerm : Term) (scope : Nat)
    (_located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkIn body options scopeTerm))))
    (_scope : evalTerm point.env scopeTerm = some (Val.scopeHandle scope))
    (_table : RowTable) (_m : Machine) (_parent : Fiber) (_yielding : Bool) : ProofGraph.Obligation
    (let q := point.child 0
     let site : ForkSite := ⟨q.path, .pinned (some scopeTerm), options⟩
     site ∈ supervision program) := ⟨⟩
#proof_wanted source_forkIn_site

def source_forkScoped_site (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (_scope : Nat)
    (_located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkScoped body options))))
    (_table : RowTable) (_m : Machine) (_parent : Fiber) (_yielding : Bool) : ProofGraph.Obligation
    (let q := point.child 0
     let site : ForkSite := ⟨q.path, .pinned none, options⟩
     site ∈ supervision program) := ⟨⟩
#proof_wanted source_forkScoped_site

def source_two_race_sites (program first second : NativeEff) (point : Point)
    (_located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.raceAll (.cons first (.cons second .nil)))))) : ProofGraph.Obligation
    (let q := (point.child 0).child 0
     (⟨q.path, .raceEntrant, raceEntrantOptions⟩ : ForkSite) ∈ supervision program ∧
      (⟨(q.child 1).path, .raceEntrant, raceEntrantOptions⟩ : ForkSite) ∈ supervision program) := ⟨⟩
#proof_wanted source_two_race_sites

end M1Origin
end Effect4.Api

namespace Effect4.Api.TraceFacts
open Effect4 Effect4.Machine Effect4.Program
universe u v

/-- The state side of the one diagnostic agreement control, in creation order. -/
def originForks {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St κ φ η : Type (max u v)} (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    List (FiberId × FiberId × Bool) :=
  m.fibers.filterMap fun f =>
    match f.origin with
    | .forked parent daemon _ => some (parent, f.id, daemon)
    | .root => none

/-- Diagnostic agreement; deliberately not an invariant of arbitrary records. -/
def Agrees {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St κ φ η : Type (max u v)} (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop :=
  forkedOf m.trace = originForks m

namespace M1Trace

def load_agrees (program : NativeEff) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) : ProofGraph.Obligation
    (Agrees (Api.load program compileFuel answers)) := ⟨⟩

end M1Trace
end Effect4.Api.TraceFacts

namespace Effect4.Api.M1Trace
open Effect4 Effect4.Machine Effect4.Program

def statusOf_replace_trace (m : Api.Machine) (f : Api.Fiber)
    (trace : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    ProofGraph.Obligation (statusOf { m with trace } f = statusOf m f) := ⟨⟩

def fiberStatuses_replace_trace (m : Api.Machine)
    (trace : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    ProofGraph.Obligation (fiberStatuses { m with trace } = fiberStatuses m) := ⟨⟩

end Effect4.Api.M1Trace
-- END M1 PHASE B Api.Supervision

#typed_state_obligations Effect4.Api.M1Origin ceiling 18 using aesop (rule_sets := [Effect4.Stores])
#typed_state_obligations Effect4.Api.M1Trace ceiling 15 using aesop (rule_sets := [Effect4.Stores])
