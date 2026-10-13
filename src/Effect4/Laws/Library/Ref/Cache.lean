import Effect4.Library.Ref.Cache
import Effect4.Library.Ref.CacheModel
import Effect4.Laws.Library.Ref.Operations
import Effect4.Laws.Program.ParamRows
import Effect4.Laws.Program.HostRuns
import Effect4.Laws.Api.SessionMeaning

/-!
# The banked Ref cache refines its model on every tape (decisions row 378 (3) and (5))

The transfer law of the banked cache (`src/Effect4/Library/Ref/Cache.lean`): for every tape of
storage's answers, each observation of the block's code is one its model
(`src/Effect4/Library/Ref/CacheModel.lean`) makes. Each law reads the block's own body,
`bodyOf (block A E) k`, so an edit of the block breaks its proof (row 378 (5)). The observation
is a method's exit, the stores with the cache's cell at the model's next value, and the unread
tape. A cache has no waiter, so its wake order is empty.

* **The meaning** (`make_agrees`, `get_agrees`, `invalidate_agrees`): each body at its request,
  with the cell holding the image of a cached value, under the reply tape of `meaningRows`. The
  loader of `get` is read as a row of any table (`paramsAsRows`,
  `src/Effect4/Laws/Program/ParamRows.lean`).
* **A run** (`get_session`): every recorded run of a fresh cache read once, which is funded, at
  rest and driven by a host, observes the model's read at the run's applied replies. It is
  `get_agrees` through H8 (`Run.denoteRows_eq_session`,
  `src/Effect4/Laws/Api/SessionMeaning.lean`).
* `cache_agrees` assembles the four. The store steps are Ref's operation laws
  (`ref_steps_agree`, `src/Effect4/Laws/Library/Ref/Operations.lean`). No proof here compares two
  folds.

Placement:

- Concept: `translation-simulation`; property: a module's code is simulated by its model, the
  shape of R10's `Agrees` (decisions rows 79 and 378 (3)).
- Question: the registry claim `ref-cache-agrees` (role simulation), witness `cache_agrees`.
  Consumers: the bank entry `refCache` (`Test/Dogfood/Bank.lean`), and the to-do's claims once
  the cache is imposed on its `list` (row 378 (2)).
- Reach: the block's three methods, one fiber, the call tree's meaning, every cached value and
  every tape whose successes lie in the image; `get`'s loader read as a row `n` of any table.
  The run law adds H8's premises and a data row at `n`, on a fresh cache.
- Does not establish: any host's storage behaviour; a run that invokes the block by
  `Eff.invoke` (slice HO-2's `invoke-unfolds`, the inlining law PROC-6); several calls in one
  run; a loader that writes the cache's cell; anything of a fiber-sharing schedule; progress, as
  an empty tape is the frontier; the block's typing, a finite check of the bank's battery.
- Unlocks: R10 for the first banked module (row 378 (1) to (5)).
-/

set_option autoImplicit false

namespace Effect4.Ref.Cache

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Store (Image)
open Effect4.Run (funded atRest hostDriven appliedExits)

/-! ## The observation -/

/-- The body of definition `k` of a program's definition block (`blockOf?`,
`src/Effect4/Laws/Program/Block.lean`). -/
def bodyOf (p : NativeEff) (k : Nat) : Option NativeEff := (blockOf? p).bind fun b => b.2.1[k]?

/-- Storage's answer as the exit that its call takes: a loaded value through the image, or the
failure's cause. -/
def exitOf {L : Type} (I : Image L) : Except CauseV L → ExitV
  | .ok x => .success (I.toVal x)
  | .error cause => .failure cause

/-- The stores with the cache's cell holding a cached value, through the image. -/
def holding {L : Type} (I : Image L) (q : RefKey) (s : Stores) (c : Option L) : Stores :=
  { s with refs := refPoke s.refs q ((Image.option I).toVal c) }

/-- What the code's run observes for one read of the model: the answer's exit, the stores with
the cell at the model's next cached value, and the unread tape's exits. -/
def observed {L : Type} (I : Image L) (q : RefKey) (s : Stores)
    (r : (Except CauseV L × Option L) × List (Except CauseV L)) : (ExitV × Stores) × ReplyTape :=
  ((exitOf I r.1.1, holding I q s r.1.2), r.2.map (exitOf I))

/-- The stores that `make` leaves at the empty stores: one cell, holding the model's empty
cache. -/
def fresh {L : Type} (I : Image L) : Stores :=
  { Stores.empty with refs := [(Image.option I).toVal Model.make] }

/-! ## Steps -/

/-- Writing a cell's own value back leaves the heap. A helper of `ref-cache-agrees`; its consumer
is `holding_self`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem refPoke_peek {heap : RefHeap} {q : RefKey} {v : Val} (h : refPeek heap q = some v) :
    refPoke heap q v = heap := by
  obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp h
  rw [refPoke, ← hv]
  exact List.set_getElem_self hlt

/-- The cell already holds the value: holding it changes nothing. A helper of
`ref-cache-agrees`; its consumers are `get_agrees` and `invalidate_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem holding_self {L : Type} (I : Image L) {q : RefKey} {s : Stores} {c : Option L}
    (held : refPeek s.refs q = some ((Image.option I).toVal c)) : holding I q s c = s := by
  unfold holding
  rw [refPoke_peek held]

/-- A bind whose first program is straight runs its rest at that program's meaning, and the host
is not asked. A helper of `ref-cache-agrees`; its consumers are `get_hit`, `get_miss` and
`get_session`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRun_bind_straight {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) {a : NativeEff} (b : NativeEff) {env : List Val}
    {s : Stores} (st : σ) (ha : Straight a = true) {v : Val} {s' : Stores}
    (hm : meaning a env s = (.success v, s')) :
    hostRun host (.bind a b) env s st = hostRun host b (env ++ [v]) s' st := by
  have h := hostRun_bindExit host a env s st (seqRows fun v => denoteRows table b (env ++ [v]))
  rw [hostRun_straight host a env s st ha, hm] at h
  exact h

/-- A bind whose first program calls a host row asks the host once. Its rest runs at the answer
on a success, and a failure is the exit. A helper of `ref-cache-agrees`; its consumer is
`get_miss`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRun_bind_call {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    {j : Nat} (hj : j < table.length) {r : Term} (b : NativeEff) {env : List Val} (s : Stores)
    (st : σ) {v : Val} (hv : evalTerm env r = some v) :
    hostRun host (.bind (.perform (.external j) r) b) env s st =
      (host.answer ⟨⟨j, hj⟩, v⟩ st).bind fun answer =>
        match answer.1 with
        | .success w => hostRun host b (env ++ [w]) s answer.2
        | .failure c => some (.failure c, (s, answer.2)) := by
  have h := hostRun_bindExit host (.perform (.external j) r) env s st
    (seqRows fun v => denoteRows table b (env ++ [v]))
  rw [hostRun_call host j r env s st hv hj] at h
  refine h.trans ?_
  cases host.answer ⟨⟨j, hj⟩, v⟩ st with
  | none => rfl
  | some answer =>
    obtain ⟨ex, st'⟩ := answer
    cases ex <;> rfl

/-- **A held value**: `get`, its loader the row `n`, answers the value under any host. It asks
the host nothing and changes no store. A helper of `ref-cache-agrees`; its consumer is
`get_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem get_hit {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ) (n : Nat)
    {q : RefKey} {s : Stores} (st : σ) {v : Val}
    (held : refPeek s.refs q = some (Store.Val.some v)) :
    hostRun host (paramsAsRows n getBody) [Val.cell q] s st = some (.success v, (s, st)) := by
  have hm : meaning (.perform .refGet (.var 0)) [Val.cell q] s =
      (.success (Store.Val.some v), s) := by
    rw [meaning_perform_sync .refGet (.var 0) [Val.cell q] s rfl rfl rfl,
      ref_steps_agree.get Image.ident (Store.Val.some v) held]
    rfl
  exact (hostRun_bind_straight host _ st rfl hm).trans rfl

/-- What `get` runs after its loader's success: it writes `some` of the list and answers it. -/
abbrev missRest : NativeEff :=
  .bind (.perform .refSet
      (.app "pair" (.cons (.var 0) (.cons (.app "some" (.cons (.var 2) .nil)) .nil))))
    (.succeed (.var 2))

/-- **An empty cache**: `get`, its loader the row `n`, asks the host once at the row, from no
request. On a success it holds `some` of the answer and answers it. A failure is the exit, and
the stores stay. A helper of `ref-cache-agrees`; its consumer is `get_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem get_miss {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    {n : Nat} (hn : n < table.length) {q : RefKey} {s : Stores} (st : σ)
    (held : refPeek s.refs q = some Store.Val.none) :
    hostRun host (paramsAsRows n getBody) [Val.cell q] s st =
      (host.answer ⟨⟨n, hn⟩, Val.unit⟩ st).map fun answer =>
        match answer.1 with
        | .success w =>
          (.success w, ({ s with refs := refPoke s.refs q (Store.Val.some w) }, answer.2))
        | .failure c => (.failure c, (s, answer.2)) := by
  have hm : meaning (.perform .refGet (.var 0)) [Val.cell q] s = (.success Store.Val.none, s) := by
    rw [meaning_perform_sync .refGet (.var 0) [Val.cell q] s rfl rfl rfl,
      ref_steps_agree.get Image.ident Store.Val.none held]
    rfl
  have h1 := hostRun_bind_straight host
    (.select (.var 1) .option (.bind (.perform (.external n) (.lit .unit)) missRest)
      (.succeed (.var 2))) st rfl hm
  have h2 : hostRun host
      (.select (.var 1) .option (.bind (.perform (.external n) (.lit .unit)) missRest)
        (.succeed (.var 2))) ([Val.cell q] ++ [Store.Val.none]) s st =
      hostRun host (.bind (.perform (.external n) (.lit .unit)) missRest)
        [Val.cell q, Store.Val.none] s st := rfl
  have hcall := hostRun_bind_call host hn missRest s st (env := [Val.cell q, Store.Val.none])
    (r := .lit .unit) rfl
  refine (h1.trans (h2.trans hcall)).trans ?_
  cases host.answer ⟨⟨n, hn⟩, Val.unit⟩ st with
  | none => rfl
  | some answer =>
    obtain ⟨ex, st'⟩ := answer
    cases ex with
    | failure c => rfl
    | success w =>
      have hstep : syncOpStep (.refSet q (Store.Val.some w)) s =
          some ({ s with refs := refPoke s.refs q (Store.Val.some w) }, Val.cell q) :=
        ref_steps_agree.set Image.ident Store.Val.none held (Store.Val.some w)
      have hset : meaning (.perform .refSet
          (.app "pair" (.cons (.var 0) (.cons (.app "some" (.cons (.var 2) .nil)) .nil))))
          [Val.cell q, Store.Val.none, w] s =
          (.success (Val.cell q), { s with refs := refPoke s.refs q (Store.Val.some w) }) := by
        rw [meaning_perform_sync .refSet _ _ s rfl rfl rfl (o := .refSet q (Store.Val.some w)),
          hstep]
      exact (hostRun_bind_straight host _ st' rfl hset).trans rfl

/-! ## The transfer law -/

/-- **`make` makes the model's empty cache**: at any table, environment, stores and reply tape,
the block's first body allocates one cell holding the image of `Model.make` and answers it. It
reads no tape. Placement: as `cache_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem make_agrees {L : Type} (I : Image L) (A E : Ty) {body : NativeEff}
    (hbody : bodyOf (block A E) 0 = some body) (table : RowTable) (env : List Val) (s : Stores)
    (tape : ReplyTape) :
    meaningRows table body env s tape =
      some ((.success (Val.cell ⟨s.refs.length⟩),
        { s with refs := s.refs ++ [(Image.option I).toVal Model.make] }), tape) := by
  have hb : makeBody A = body := Option.some.inj hbody
  subst hb
  have hstep : syncOpStep (.refMake Store.Val.none) s =
      some ({ s with refs := s.refs ++ [(Image.option I).toVal Model.make] },
        Val.cell ⟨s.refs.length⟩) :=
    ref_steps_agree.make (Image.option I) Model.make s
  rw [meaningRows, meaningUnder_straight _ _ _ _ _ rfl, makeBody,
    meaning_perform_sync .refMake _ env s rfl rfl rfl (o := .refMake Store.Val.none), hstep]

/-- **`get` reads through the cache as the model reads**: the block's second body, its loader
the row `n` of any table, at a cell holding the image of `c`, under every tape of storage's
answers in the image, observes the model's read of `c` on that tape. A held value reads no
answer. An empty cache reads one, holds a loaded value, and stays empty on a failure. An empty
tape is the frontier on both sides. Placement: as `cache_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem get_agrees {L : Type} (I : Image L) (A E : Ty) {body : NativeEff}
    (hbody : bodyOf (block A E) 1 = some body) {table : RowTable} {n : Nat}
    (hn : n < table.length) (c : Option L) {q : RefKey} {s : Stores}
    (held : refPeek s.refs q = some ((Image.option I).toVal c)) (tape : List (Except CauseV L)) :
    meaningRows table (paramsAsRows n body) [Val.cell q] s (tape.map (exitOf I)) =
      (Model.read c tape).map (observed I q s) := by
  have hb : getBody = body := Option.some.inj hbody
  subst hb
  rw [meaningRows_eq_hostRun]
  cases c with
  | some x =>
    rw [get_hit (tapeHost table) n _ held]
    show some ((Exit.success (I.toVal x), s), tape.map (exitOf I)) =
      some ((Exit.success (I.toVal x), holding I q s (some x)), tape.map (exitOf I))
    rw [holding_self I held]
  | none =>
    rw [get_miss (tapeHost table) hn _ held]
    cases tape with
    | nil => rfl
    | cons answer rest =>
      cases answer with
      | ok y => rfl
      | error e =>
        show some ((Exit.failure e, s), rest.map (exitOf I)) =
          some ((Exit.failure e, holding I q s none), rest.map (exitOf I))
        rw [holding_self I held]

/-- **`invalidate` empties the cache**: the block's third body, at a cell holding the image of
any cached value, under any reply tape, leaves the cell at the model's empty cache and answers
`unit`. It reads no tape. Placement: as `cache_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem invalidate_agrees {L : Type} (I : Image L) (A E : Ty) {body : NativeEff}
    (hbody : bodyOf (block A E) 2 = some body) (table : RowTable) (c : Option L) {q : RefKey}
    {s : Stores} (held : refPeek s.refs q = some ((Image.option I).toVal c)) (tape : ReplyTape) :
    meaningRows table body [Val.cell q] s tape =
      some ((.success Val.unit, holding I q s (Model.invalidate c)), tape) := by
  have hb : invalidateBody = body := Option.some.inj hbody
  subst hb
  have hstep : syncOpStep (.refSet q Store.Val.none) s = some (holding I q s none, Val.cell q) :=
    ref_steps_agree.set (Image.option I) c held none
  rw [meaningRows, meaningUnder_straight _ _ _ _ _ rfl, invalidateBody, meaning_bind,
    meaning_perform_sync .refSet _ _ s rfl rfl rfl (o := .refSet q Store.Val.none), hstep]
  rfl

/-- **A fresh cache read once, on every recorded run**: a run of `make` then `get`, its loader a
data row `n` of the run's table, that is funded, at rest and driven by a host, and whose applied
replies are a tape of storage's answers in the image, observes the model's read of `Model.make`
on that tape. The run's exit and stores are that read's answer and cell, and the read leaves no
answer unread. It is `get_agrees` through H8 (`Run.denoteRows_eq_session`). Placement: as
`cache_agrees`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem get_session {L : Type} (I : Image L) (A E : Ty) {body : NativeEff}
    (hbody : bodyOf (block A E) 1 = some body) {n : Nat} (s : Run) (hreach : Run.Reached s)
    (hprog : s.built.program = .bind (makeBody A) (paramsAsRows n body))
    (hdata : dataRow s.built.table n = true) (hfund : funded s = true) (hrest : atRest s = true)
    (hhost : hostDriven s = true) (tape : List (Except CauseV L))
    (htape : appliedExits s = tape.map (exitOf I)) :
    s.exit.map (fun ex => ((ex, s.machine.state), ([] : ReplyTape))) =
      (Model.read Model.make tape).map (observed I ⟨0⟩ (fresh I)) := by
  have hb : getBody = body := Option.some.inj hbody
  subst hb
  have hfrag : StraightRows s.built.table s.built.program = true := by
    rw [hprog]
    show ((dataRow s.built.table n && true) && true) = true
    rw [hdata]
    rfl
  have hmake : meaning (makeBody A) [] Stores.empty = (.success (Val.cell ⟨0⟩), fresh I) := by
    have hstep : syncOpStep (.refMake Store.Val.none) Stores.empty =
        some (fresh I, Val.cell ⟨0⟩) :=
      ref_steps_agree.make (Image.option I) Model.make Stores.empty
    rw [makeBody, meaning_perform_sync .refMake _ [] Stores.empty rfl rfl rfl
      (o := .refMake Store.Val.none), hstep]
  rw [← Run.denoteRows_eq_session s hreach hfund hrest hhost hfrag, hprog, htape,
    meaningRows_eq_hostRun, hostRun_bind_straight (tapeHost _) _ _ rfl hmake,
    ← meaningRows_eq_hostRun]
  exact get_agrees I A E rfl (lt_of_dataRow hdata) Model.make (q := ⟨0⟩) (s := fresh I) rfl tape

/-- **The banked cache's code refines its model**: one field for each law above, at the law's
own statement (`type_of%`), so no statement is written twice. -/
structure Agrees : Prop where
  /-- `make`: `make_agrees`. -/
  make : type_of% @make_agrees
  /-- `get`: `get_agrees`. -/
  get : type_of% @get_agrees
  /-- `invalidate`: `invalidate_agrees`. -/
  invalidate : type_of% @invalidate_agrees
  /-- A fresh cache read once, on every recorded run: `get_session`. -/
  session : type_of% @get_session

/-- **The transfer law of the banked cache** (the registry claim `ref-cache-agrees`, role
simulation; decisions row 378 (3) and (5)). Placement: concept `translation-simulation`,
requirement R10; the module docstring gives its reach and what it does not establish. Consumer:
the bank entry `refCache` (`Test/Dogfood/Bank.lean`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cache_agrees : Agrees :=
  ⟨@make_agrees, @get_agrees, @invalidate_agrees, @get_session⟩

end Effect4.Ref.Cache
