import Effect4.Api.Supervision
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.ForkLedger
import Effect4.Laws.Api.Frontier
import Effect4.Laws.Auto.Inversion
import Effect4.Laws.Program.Size
import Effect4.Laws.Auto.Obligations

/-!
# Laws.Api.Supervision — the static table and the running machine say the same thing

Three groups.

**(a) Static fork sites and ledger entries.** Runtime provenance is read from the fork
ledger. The diagnostic trace laws and agreement control are in `Test/Api/TraceOrigin.lean`.

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

/-! ## (a) The static half: a located site is a site of the table

The fold reads a node's own sites and each child's at the child's path, in the order
`Node.child` numbers children. `child_sub` checks that order against the generated child
table, one case per table row, by the same step; the rest is induction on the path. -/

/-- The supervision fold of a node, read at a path. -/
def foldNode : Node Op → List Nat → List ForkSite
  | .eff e => cataFam superAlg .eff e
  | .stmts s => cataFam superAlg .stmts s
  | .stmt s => cataFam superAlg .stmt s
  | .action a => cataFam superAlg .action a
  | .effs es => cataFam superAlg .effs es
  | .layer l => cataFam superAlg .layer l
  | .layers ls => cataFam superAlg .layers ls

/-- A site of the reader at position `i` of `atChildPaths`, read at its child path. -/
theorem mem_atChildPaths_index : ∀ (readers : List (List Nat → List ForkSite)) (p : List Nat)
    (k i : Nat) (r : List Nat → List ForkSite) (s : ForkSite),
    readers[i]? = some r → s ∈ r (p ++ [k + i]) → s ∈ atChildPaths readers p k
  | [], _, _, _, _, _, h, _ => nomatch h
  | reader :: rest, p, k, 0, r, s, h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [atChildPaths, List.mem_append]
    exact Or.inl (by simpa only [Nat.add_zero] using hs)
  | reader :: rest, p, k, i + 1, r, s, h, hs => by
    simp only [List.getElem?_cons_succ] at h
    simp only [atChildPaths, List.mem_append]
    refine Or.inr (mem_atChildPaths_index rest p (k + 1) i r s h ?_)
    rwa [Nat.add_assoc, Nat.add_comm 1 i]

/-- A site of a child reader belongs to the node's fold. -/
theorem fold_child_mem (fam : EffFam) (e : EffSelfCarrier Op fam) (i : Nat)
    (r : List Nat → List ForkSite)
    (hr : (childReaders ((view fam e).2.map (ArgF.fold superAlg)))[i]? = some r)
    (p : List Nat) (s : ForkSite) (hs : s ∈ r (p ++ [i])) : s ∈ cataFam superAlg fam e p := by
  have hb := cata_build superLayer fam (view fam e).1 (view fam e).2 e (build_view fam e)
  rw [show (superAlg : EffAlgebra Op SiteReader) = EffAlgebra.ofLayer superLayer from rfl, hb,
    superLayer, List.mem_append]
  exact Or.inr (mem_atChildPaths_index _ p 0 i r s hr (by simpa only [Nat.zero_add] using hs))

/-- A node's own sites belong to its fold. -/
theorem fold_own_mem (fam : EffFam) (e : EffSelfCarrier Op fam) (p : List Nat) (s : ForkSite)
    (hs : s ∈ forkSitesOf fam (view fam e).1 ((view fam e).2.map (ArgF.fold superAlg)) p) :
    s ∈ cataFam superAlg fam e p := by
  have hb := cata_build superLayer fam (view fam e).1 (view fam e).2 e (build_view fam e)
  rw [show (superAlg : EffAlgebra Op SiteReader) = EffAlgebra.ofLayer superLayer from rfl, hb,
    superLayer, List.mem_append]
  exact Or.inl hs

/-- A node's folded child readers, in child order. -/
def readersOf : Node Op → List (List Nat → List ForkSite)
  | .eff e => childReaders ((view .eff e).2.map (ArgF.fold superAlg))
  | .stmts s => childReaders ((view .stmts s).2.map (ArgF.fold superAlg))
  | .stmt s => childReaders ((view .stmt s).2.map (ArgF.fold superAlg))
  | .action a => childReaders ((view .action a).2.map (ArgF.fold superAlg))
  | .effs es => childReaders ((view .effs es).2.map (ArgF.fold superAlg))
  | .layer l => childReaders ((view .layer l).2.map (ArgF.fold superAlg))
  | .layers ls => childReaders ((view .layers ls).2.map (ArgF.fold superAlg))

theorem foldNode_child_mem (n : Node Op) (i : Nat) (r : List Nat → List ForkSite)
    (hr : (readersOf n)[i]? = some r) (p : List Nat) (s : ForkSite) (hs : s ∈ r (p ++ [i])) :
    s ∈ foldNode n p := by
  cases n with
  | eff e => exact fold_child_mem .eff e i r hr p s hs
  | stmts x => exact fold_child_mem .stmts x i r hr p s hs
  | stmt x => exact fold_child_mem .stmt x i r hr p s hs
  | action a => exact fold_child_mem .action a i r hr p s hs
  | effs es => exact fold_child_mem .effs es i r hr p s hs
  | layer l => exact fold_child_mem .layer l i r hr p s hs
  | layers ls => exact fold_child_mem .layers ls i r hr p s hs

theorem child_sub (n c : Node Op) (i : Nat) (h : n.child i = some c) (p : List Nat)
    (s : ForkSite) (hs : s ∈ foldNode c (p ++ [i])) : s ∈ foldNode n p := by
  unfold Node.child at h
  split at h <;> cases h <;> refine foldNode_child_mem _ _ _ ?_ p s hs <;> rfl

/-- **Path inclusion.** The sites of the node at a path, read at that path, are the program's. -/
theorem at_sub : ∀ (path : List Nat) (n m : Node Op) (p : List Nat) (s : ForkSite),
    Node.at_ n path = some m → s ∈ foldNode m (p ++ path) → s ∈ foldNode n p
  | [], n, m, p, s, h, hs => by
    simp only [Node.at_, Option.some.injEq] at h
    subst h
    simpa only [List.append_nil] using hs
  | i :: rest, n, m, p, s, h, hs => by
    simp only [Node.at_] at h
    cases hc : n.child i with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      have hs' : s ∈ foldNode m ((p ++ [i]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using hs
      exact child_sub n c i hc p s (at_sub rest c m (p ++ [i]) s h hs')

/-- A located node's own sites, read at its path, are the program's. -/
theorem mem_supervision_of_at (program : Eff Op) (path : List Nat) (m : Node Op) (s : ForkSite)
    (located : Node.at_ (.eff program) path = some m) (own : s ∈ foldNode m path) :
    s ∈ supervision program :=
  at_sub path (.eff program) m [] s located (by simpa only [List.nil_append] using own)

/-! ## (a) The machine half: what a fork stamps -/

section MachineForks

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- `spawn` appends exactly one event, naming the parent, the fresh id and the options'
daemon flag (`Machine/Fibers.lean:908-923`). -/
theorem spawn_trace (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).1.trace =
      m.trace ++ [RunEvent.forked parent.id ⟨m.nextId⟩ options.daemon] := by aesop

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The id the spawn mints is the machine's `nextId`. -/
theorem spawn_child (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).2.2 = ⟨m.nextId⟩ := by aesop

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The fresh id is consumed. -/
theorem spawn_nextId (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).1.nextId = m.nextId + 1 := by aesop

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
theorem spawn_fibers (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) :
    ∃ child : RunFiber ν σ β ε δ ι α χ κ φ,
      (spawn interp m parent program options).1.fibers = m.fibers ++ [child] ∧
        child.id = ⟨m.nextId⟩ ∧ child.exit = none ∧ child.observers = [] ∧
        child.children = [] ∧ (spawn interp m parent program options).1.forks =
          m.forks ++ [ForkRecord.mk child.id parent.id options.daemon []] := by aesop

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

@[aesop unsafe 90% apply (rule_sets := [Effect4.Fibers])]
theorem status_persists (m m' : Machine) (f f' : Fiber)
    (exit : f'.exit = f.exit)
    (track : parentOf m' f'.id = parentOf m f.id)
    (pin : pinOf f' = pinOf f)
    (origin : m'.originOf f'.id = m.originOf f.id) :
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
    (fresh : NextIdFresh m) (recordsFresh : m.forkRecord? ⟨m.nextId⟩ = none) (child : Fiber)
    (member : child ∈ (spawn interp m parent program options).1.fibers)
    (id : child.id = ⟨m.nextId⟩) :
    statusOf (spawn interp m parent program options).1 child = FiberStatus.daemon := by
  obtain ⟨new, hfib, hid, hexit, hobs, hchildren, _hforks⟩ :=
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
  have hfresh : m.fiber? ⟨m.nextId⟩ = none := by
    apply List.find?_eq_none.mpr
    intro g hg hit
    exact (fresh g hg).1 (of_decide_eq_true hit)
  have horigin := ForkLedger.spawn_originOf_new interp m parent program options [] hfresh recordsFresh
  unfold statusOf
  rw [hexit, hparent, hpin, id, horigin]

/-- A spawn changes no existing fiber's status: it appends a fiber with no children, touches
no other, and retains every existing origin. -/
theorem spawn_status_other
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (m : Machine)
    (parent : Fiber) (program : NCode) (options : Supervision.ForkOptions)
    (fresh : NextIdFresh m) (g : Fiber) (member : g ∈ m.fibers) :
    statusOf (spawn interp m parent program options).1 g = statusOf m g := by
  obtain ⟨new, hfib, _, _, _, hchildren, _⟩ := spawn_fibers interp m parent program options
  refine status_persists m (spawn interp m parent program options).1 g g rfl ?_ rfl ?_
  · unfold parentOf
    rw [hfib, parentOf_append_same m.fibers new g.id hchildren]
  · exact ForkLedger.spawn_originOf_other interp m parent program options [] g.id
      (Ne.symm (fresh g member).1)

/-! ## (c) `fiberStatuses` and `awaits` agree on which fibers are parked -/

/-- Every outstanding host call names a parked fiber of the machine, at its own token. -/
theorem awaits_parked (m : Machine) (a : Await) (member : a ∈ Program.awaits m) :
    ∃ f ∈ m.fibers, f.id = a.fiber ∧ f.parked = Parked.withGuard a.token := by
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
    ∃ f ∈ m.fibers, f.id = a.fiber ∧ (a.fiber, statusOf m f) ∈ fiberStatuses m ∧
      (statusOf m f).live = true := by
  obtain ⟨f, hf, hid, hparked⟩ := awaits_parked m a member
  have live := parked_status_live m unparked f hf a.token hparked
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

/-- The ordered fork-ledger projection, including exact source paths. Roots have no
entry. Root/member origin observations use RunMachine.originOf separately. -/
def originEntries {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St κ φ η : Type (max u v)} (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    List (FiberId × Origin) :=
  m.forks.map fun record =>
    (record.child, Origin.forked record.parent record.daemon record.site)

namespace M1Origin

section MachineForks
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]

end MachineForks

/-! The five source-site connectors (slice 6), proved. -/

theorem source_race_site_proof (program body : NativeEff) (rest : Effs NativeOp) (path : List Nat)
    (located : Node.at_ (.eff program) path = some (.effs (.cons body rest))) :
    (⟨path, .raceEntrant, raceEntrantOptions⟩ : ForkSite) ∈ supervision program :=
  mem_supervision_of_at program path _ _ located (fold_own_mem .effs _ path _ (List.mem_singleton_self _))

theorem source_fork_site_proof (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions)
    (located : Node.at_ (.eff program) point.path = some (.eff (.withFiber (.fork body options))))
    (_table : RowTable) (_m : Machine) (_parent : Fiber) (_yielding : Bool) :
    (let q := point.child 0
     let site : ForkSite := ⟨q.path, if options.daemon then .daemon else .child, options⟩
     site ∈ supervision program) :=
  at_sub point.path (.eff program) _ [] _ located
    (child_sub _ (.action (.fork body options)) 0 rfl _ _
      (fold_own_mem .action _ _ _ (List.mem_singleton_self _)))

theorem source_forkIn_site_proof (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (scopeTerm : Term) (scope : Nat)
    (located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkIn body options scopeTerm))))
    (_scope : evalTerm point.env scopeTerm = some (Val.scopeHandle scope))
    (_table : RowTable) (_m : Machine) (_parent : Fiber) (_yielding : Bool) :
    (let q := point.child 0
     let site : ForkSite := ⟨q.path, .pinned (some scopeTerm), options⟩
     site ∈ supervision program) :=
  at_sub point.path (.eff program) _ [] _ located
    (child_sub _ (.action (.forkIn body options scopeTerm)) 0 rfl _ _
      (fold_own_mem .action _ _ _ (List.mem_singleton_self _)))

theorem source_forkScoped_site_proof (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (_scope : Nat)
    (located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkScoped body options))))
    (_table : RowTable) (_m : Machine) (_parent : Fiber) (_yielding : Bool) :
    (let q := point.child 0
     let site : ForkSite := ⟨q.path, .pinned none, options⟩
     site ∈ supervision program) :=
  at_sub point.path (.eff program) _ [] _ located
    (child_sub _ (.action (.forkScoped body options)) 0 rfl _ _
      (fold_own_mem .action _ _ _ (List.mem_singleton_self _)))

theorem source_two_race_sites_proof (program first second : NativeEff) (point : Point)
    (located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.raceAll (.cons first (.cons second .nil)))))) :
    (let q := (point.child 0).child 0
     (⟨q.path, .raceEntrant, raceEntrantOptions⟩ : ForkSite) ∈ supervision program ∧
      (⟨(q.child 1).path, .raceEntrant, raceEntrantOptions⟩ : ForkSite) ∈ supervision program) := by
  have toEffs : ∀ s, s ∈ foldNode (.effs (.cons first (.cons second .nil))) (point.path ++ [0] ++ [0]) →
      s ∈ supervision program := fun s hs =>
    at_sub point.path (.eff program) _ [] s located
      (child_sub _ (.action (.raceAll (.cons first (.cons second .nil)))) 0 rfl _ _
        (child_sub _ _ 0 rfl _ _ hs))
  refine ⟨toEffs _ (fold_own_mem .effs _ _ _ (List.mem_singleton_self _)), toEffs _ ?_⟩
  exact child_sub _ (.effs (.cons second .nil)) 1 rfl _ _
    (fold_own_mem .effs _ _ _ (List.mem_singleton_self _))

end M1Origin
end Effect4.Api

namespace Effect4.Api.M1Trace
open Effect4 Effect4.Machine Effect4.Program

end Effect4.Api.M1Trace
namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program

universe u v

/-! ## Origins, machine half: the record each fork appends to the machine ledger -/

@[aesop unsafe 90% apply (rule_sets := [Effect4.Fibers])]
theorem load_origins (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    originEntries (Api.load program fuel answers) = [] ∧
      (Api.load program fuel answers).originOf Api.root = some .root := by
  constructor <;> rfl

section OriginFacts
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]

omit [FiberCore ν β ε δ ι α κ φ] in
theorem originEntries_emit (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (events : List (RunEvent ν σ β ε δ ι α χ κ η)) :
    originEntries (m.emit events) = originEntries m := rfl

omit [FiberCore ν β ε δ ι α κ φ] in
theorem originEntries_updateRace (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (r : Race ν σ β ε δ ι α κ) : originEntries (m.updateRace r) = originEntries m := rfl

theorem spawn_origins (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
    (options : Supervision.ForkOptions) (site : List Nat) :
    originEntries (spawn interp m parent program options site).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked parent.id options.daemon site)] := by
  aesop (add norm simp [spawn, RunMachine.emit, originEntries])

omit [FiberCore ν β ε δ ι α κ φ] in
theorem start_origins (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediate : Bool) :
    originEntries (start m parent child immediate).1 = originEntries m := by
  cases immediate <;>
    aesop (add norm simp [start, RunMachine.emit, RunMachine.arm, originEntries])

theorem launchEntrant_origins (interp : RunInterp ν σ β ε δ ι α χ St κ) (raceId : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (site : List Nat) :
    originEntries (launchEntrant interp raceId m host program site).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked host.id true site)] := by
  aesop (add norm simp [launchEntrant, spawn, RunMachine.emit, originEntries])

omit [FiberCore ν β ε δ ι α κ φ] in
/-- Updating the race found under an id leaves that id finding the update. -/
theorem race?_updateRace_same (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (race r : Race ν σ β ε δ ι α κ) (h : m.race? race.id = some race) (hid : r.id = race.id) :
    (m.updateRace r).race? race.id = some r := by
  unfold RunMachine.race? at h ⊢
  unfold RunMachine.updateRace
  rw [List.find?_map]
  have same : ((fun s : Race ν σ β ε δ ι α κ => decide (s.id = race.id)) ∘
      (fun s => if s.id = r.id then r else s)) = fun s => decide (s.id = race.id) := by
    funext s
    simp only [Function.comp]
    by_cases hs : s.id = r.id
    · simp only [hs, ↓reduceIte]
    · simp only [hs, ↓reduceIte]
  rw [same, h, Option.map_some, if_pos hid.symm]

end OriginFacts

section PrimForks
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

theorem fork_origins (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat) :
    originEntries (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.fork program options site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id options.daemon site)] := by
  rw [withFiber_fork interp m f yielding program options site]
  simp only [start_origins, spawn_origins]
  cases options.daemon <;> rfl

theorem forkIn_origins (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (site : List Nat) :
    originEntries (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkIn program options scope site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true site)] := by
  rw [withFiber_forkIn interp m f yielding program options scope site]
  simp only [start_origins, spawn_origins]

theorem forkScoped_origins (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (site : List Nat) (ambient : interp.ambientScope f.context = some scope) :
    originEntries (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true site)] := by
  rw [withFiber_forkScoped_ambient interp m f yielding program options scope ambient site]
  simp only [start_origins, spawn_origins]

theorem forkScoped_none_origins (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat)
    (ambient : interp.ambientScope f.context = none) :
    originEntries (evaluatePrim.withFiber interp m f yielding
        (WithFiberAction.forkScoped program options site)).machine = originEntries m := by
  simp only [withFiber_forkScoped_none interp m f yielding program options ambient site]

/-- Row 20 at the machine: the four forks record their site on the fiber they create. -/
theorem supervision_static_origins (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (scope raceId : Nat)
    (site entrantSite : List Nat)
    (ambient : interp.ambientScope f.context = some scope) :
    originEntries (evaluatePrim.withFiber interp m f yielding
        (.fork program options site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id options.daemon site)] ∧
    originEntries (evaluatePrim.withFiber interp m f yielding
        (.forkIn program options scope site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true site)] ∧
    originEntries (evaluatePrim.withFiber interp m f yielding
        (.forkScoped program options site)).machine =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true site)] ∧
    originEntries (launchEntrant interp raceId m f program entrantSite).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked f.id true entrantSite)] :=
  ⟨fork_origins interp m f yielding program options site,
   forkIn_origins interp m f yielding program options scope site,
   forkScoped_origins interp m f yielding program options scope site ambient,
   launchEntrant_origins interp raceId m f program entrantSite⟩

end PrimForks

/-! ## Origins, source half: a located fork decodes to its action and stamps its site -/

theorem source_fork_holds (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions)
    (located : Node.at_ (.eff program) point.path = some (.eff (.withFiber (.fork body options))))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) :
    actionAt program point =
        some (.fork (resolve program ((point.child 0).child 0)) options (point.child 0).path) ∧
      originEntries (evaluatePrim.withFiber (interpOf program table) m parent yielding
          (.fork (resolve program ((point.child 0).child 0)) options (point.child 0).path)).machine =
        originEntries m ++ [(⟨m.nextId⟩, .forked parent.id
          (⟨(point.child 0).path, if options.daemon then .daemon else .child, options⟩ : ForkSite).isDaemon
          (point.child 0).path)] := by
  refine ⟨?_, ?_⟩
  · simp only [actionAt, located]
  · rw [fork_origins]
    cases hd : options.daemon <;> rfl

theorem source_forkIn_holds (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (scopeTerm : Term) (scope : Nat)
    (located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkIn body options scopeTerm))))
    (hscope : evalTerm point.env scopeTerm = some (Val.scopeHandle scope))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) :
    actionAt program point =
        some (.forkIn (resolve program ((point.child 0).child 0)) options scope (point.child 0).path) ∧
      originEntries (evaluatePrim.withFiber (interpOf program table) m parent yielding
          (.forkIn (resolve program ((point.child 0).child 0)) options scope (point.child 0).path)).machine =
        originEntries m ++ [(⟨m.nextId⟩, .forked parent.id
          (⟨(point.child 0).path, .pinned (some scopeTerm), options⟩ : ForkSite).isDaemon
          (point.child 0).path)] := by
  refine ⟨?_, ?_⟩
  · simp only [actionAt, located, hscope]
  · rw [forkIn_origins]
    rfl

theorem source_forkScoped_holds (program body : NativeEff) (point : Point)
    (options : Supervision.ForkOptions) (scope : Nat)
    (located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.forkScoped body options))))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) :
    actionAt program point = some .ambientScope ∧
      forkScopedAt program point scope =
        some (.forkIn (resolve program ((point.child 0).child 0)) options scope (point.child 0).path) ∧
      originEntries (evaluatePrim.withFiber (interpOf program table) m parent yielding
          (.forkIn (resolve program ((point.child 0).child 0)) options scope (point.child 0).path)).machine =
        originEntries m ++ [(⟨m.nextId⟩, .forked parent.id
          (⟨(point.child 0).path, .pinned none, options⟩ : ForkSite).isDaemon (point.child 0).path)] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [actionAt, located]
  · simp only [forkScopedAt, located]
  · rw [forkIn_origins]
    rfl

theorem source_race_holds (program : NativeEff) (point : Point) (entrants : Effs NativeOp)
    (located : Node.at_ (.eff program) point.path = some (.eff (.withFiber (.raceAll entrants))))
    (table : RowTable) (m : Machine) (parent : Fiber) (yielding : Bool) :
    actionAt program point =
        some (.raceAll (actionAt.entrants entrants ((point.child 0).child 0))
          (some ((point.child 0).child 0).path)) ∧
      originEntries (beginRace (interpOf program table) m parent yielding
          (actionAt.entrants entrants ((point.child 0).child 0))
          (some ((point.child 0).child 0).path)).machine = originEntries m ∧
      (beginRace (interpOf program table) m parent yielding
          (actionAt.entrants entrants ((point.child 0).child 0))
          (some ((point.child 0).child 0).path)).machine.races.map (fun r => r.nextSite) =
        m.races.map (fun r => r.nextSite) ++ [some ((point.child 0).child 0).path] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [actionAt, located]
  · simp only [beginRace, RunMachine.emit, originEntries]
  · simp only [beginRace, RunMachine.emit, List.map_append, List.map_cons, List.map_nil]

theorem source_two_race_paths_holds (program first second : NativeEff) (point : Point)
    (located : Node.at_ (.eff program) point.path =
      some (.eff (.withFiber (.raceAll (.cons first (.cons second .nil)))))) :
    actionAt program point = some (.raceAll
       [compileEff first (((point.child 0).child 0).child 0),
        compileEff second ((((point.child 0).child 0).child 1).child 0)]
       (some ((point.child 0).child 0).path)) := by
  simp only [actionAt, located, actionAt.entrants]

theorem race_launch_origins_holds
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : Machine) (raceId : Nat) (race : Race EffName EffThunk Val Err Defect FiberId Ann)
    (parent : Fiber) (code : NCode) (remaining : List NCode)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (hrace : m.race? raceId = some race) (hprograms : race.programs = code :: remaining)
    (hopen : race.state.accepted.isSome = false) (hparent : m.fiber? race.host = some parent) :
    originEntries (driveStep interp m (.launch raceId) rest).1 =
      originEntries m ++ [(⟨m.nextId⟩, .forked parent.id true (race.nextSite.getD []))] ∧
      ((driveStep interp m (.launch raceId) rest).1.race? raceId).map (fun r => r.nextSite) =
        some (race.nextSite.map (fun path => path ++ [1])) := by
  have hrace' := hrace
  unfold RunMachine.race? at hrace'
  have hfound := List.find?_some hrace'
  have hid : race.id = raceId := of_decide_eq_true hfound
  rcases hl : launchEntrant interp raceId m parent code (race.nextSite.getD []) with ⟨m', child⟩
  have hentries := launchEntrant_origins interp raceId m parent code (race.nextSite.getD [])
  rw [hl] at hentries
  have hraces : m'.races = m.races := by
    have := congrArg (fun p => p.1.races) hl
    simpa only [launchEntrant, spawn, RunMachine.emit] using this.symm
  simp only [driveStep, hrace, hprograms, hopen, Bool.false_eq_true, ↓reduceIte, hparent, hl]
  refine ⟨?_, ?_⟩
  · rw [originEntries_emit, originEntries_updateRace]
    exact hentries
  · rw [RunMachine.race?_emit]
    subst hid
    have found : m'.race? race.id = some race := by
      unfold RunMachine.race?
      rw [hraces]
      exact hrace
    rw [race?_updateRace_same m' race
      { race with programs := remaining, nextSite := race.nextSite.map (fun site => site ++ [1]) }
      found rfl]
    rfl

attribute [aesop unsafe 90% apply (rule_sets := [Effect4.Fibers])]
  originEntries_emit originEntries_updateRace spawn_origins start_origins launchEntrant_origins
  race?_updateRace_same fork_origins forkIn_origins forkScoped_origins forkScoped_none_origins

attribute [aesop safe -100 apply (rule_sets := [Effect4.Fibers])]
  supervision_static_origins source_fork_holds source_forkIn_holds source_forkScoped_holds
  source_race_holds source_two_race_paths_holds race_launch_origins_holds

end Effect4.Api

-- END M1 PHASE B Api.Supervision
