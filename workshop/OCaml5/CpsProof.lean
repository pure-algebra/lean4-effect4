import OCaml5.Cps

/-!
# OCaml 5 spike P2: `cps_preserves_outcome`, pass by pass

Status: 2026-09-03. Module `OCaml5.CpsProof`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, row P2 of §6. Report:
`docs/research/2026-09-03-spike-p2-cps-theorem.md`. Predecessor: spike O2,
`docs/research/2026-09-03-spike-o2-jsoo.md`, whose §5 states the theorem this module attacks.

Additive: nothing in `Code.lean` or `Cps.lean` is renamed or changed.
-/

namespace OCaml5.CpsProof

set_option autoImplicit false

open OCaml5.Code OCaml5.Cps

/-! ## 0. The fuel algebra

`Machine.run` is fuel-bounded and answers `Outcome.outOfFuel` when the fuel runs out, which
makes it a bad object to reason with: it is not a monoid action. `Machine.step` *is* one,
because it is the identity on a halted state, so plain iteration is. Everything below is
stated on `iter` and transported to `run` once, here. -/

/-- Plain iteration of `step`. Unlike `run` this is a monoid action, because `step` fixes a
halted state (`step_done`). -/
def iter : Nat → Machine → Machine
  | 0, m => m
  | n + 1, m => iter n m.step

/-- Is the focus a halt? -/
def isDone (m : Machine) : Bool :=
  match m.ctl with
  | .done _ => true
  | _ => false

theorem step_done {m : Machine} {o : Outcome} (h : m.ctl = .done o) : m.step = m := by
  unfold Machine.step; rw [h]

theorem iter_zero (m : Machine) : iter 0 m = m := rfl

theorem iter_succ (n : Nat) (m : Machine) : iter (n + 1) m = iter n m.step := rfl

theorem iter_add (n k : Nat) (m : Machine) : iter (n + k) m = iter k (iter n m) := by
  induction n generalizing m with
  | zero => simp [iter]
  | succ n ih =>
    have : n + 1 + k = (n + k) + 1 := by omega
    rw [this, iter_succ, ih, iter_succ]

theorem iter_done {m : Machine} {o : Outcome} (h : m.ctl = .done o) (n : Nat) :
    iter n m = m := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, step_done h, ih]

/-- `run` is `iter` plus a fuel verdict. This is the only bridge the rest of the module needs:
every simulation lemma is about `iter`, and this turns it into a statement about `exec`. -/
theorem run_eq_iter (n : Nat) (m : Machine) :
    Machine.run n m = if isDone (iter n m) then iter n m
              else { iter n m with ctl := .done .outOfFuel } := by
  induction n generalizing m with
  | zero =>
    cases h : m.ctl <;> simp [Machine.run, iter, isDone, h]
  | succ n ih =>
    cases h : m.ctl
    case done o =>
      have hd : iter (n + 1) m = m := iter_done h (n + 1)
      simp [Machine.run, h, hd, isDone]
    all_goals (simp only [Machine.run, h, iter_succ, ih]; rfl)
/-- Halting is stable: once the focus is `done`, more fuel changes nothing. -/
theorem iter_halt_mono {m : Machine} {n : Nat} {o : Outcome}
    (h : (iter n m).ctl = .done o) (k : Nat) : iter (n + k) m = iter n m := by
  rw [iter_add]; exact iter_done h k

/-- `exec` read off `iter`. -/
theorem exec_eq (fuel : Nat) (p : Program K) :
    Machine.exec fuel p =
      ((if isDone (iter fuel (Machine.init p)) then (iter fuel (Machine.init p)).outcome
        else .outOfFuel), String.join (iter fuel (Machine.init p)).out) := by
  unfold Machine.exec Machine.result
  rw [run_eq_iter]
  by_cases h : isDone (iter fuel (Machine.init p)) <;> simp [h, Machine.outcome]

/-! ## 1. Pass-level theorems

Three passes run before `cps_transform` (`effects.ml:925-933`). `remove_empty_blocks`
(`effects.ml:870-921`) is *not* transcribed by O2 — the O2 report §9 records it as owed — so
there is nothing here to prove about it; the row is carried in the report as not applicable.
What is left is `split_blocks` and `rewrite_toplevel`. -/

/-! ### 1.1 `split_blocks`

`splitBlocks` (`effects.ml:823-866`) cuts a block after a CPS call or effect primitive that is
not already in tail position, and joins the two halves with a `branch`. Two theorems: the pass
is the identity when there is nothing to cut, and one cut costs exactly two machine steps and
otherwise changes nothing. -/

/-- A block the pass would cut. -/
def blockHasSplit (needed : VarSet) (b : Block K) : Bool :=
  b.body.zipIdx.any (fun (i, n) => isSplitPoint needed i (b.body.drop (n + 1)) b.branch)

/-- A program the pass would change. -/
def progHasSplit (needed : VarSet) (p : Program K) : Bool :=
  p.blocks.any (fun e => blockHasSplit needed e.2)

private theorem foldl_fix {α β : Type} (f : α → β → α) (a : α) :
    ∀ (l : List β), (∀ b ∈ l, f a b = a) → l.foldl f a = a
  | [], _ => rfl
  | b :: l, h => by
      rw [List.foldl_cons, h b (by simp)]
      exact foldl_fix f a l (fun b hb => h b (by simp [hb]))

/-- `split_blocks` is the identity on a program with no split point. Together with
§1.2's counterexample this is the whole of what `split_blocks` can be said to preserve
*on its own*: the pass is behaviour-preserving, but only up to the two extra steps of
`split_branch_costs_two`, which is a statement about configurations, not about programs. -/
theorem splitBlocks_id (needed : VarSet) (p : Program K)
    (h : progHasSplit needed p = false) : splitBlocks needed p = p := by
  unfold splitBlocks
  refine foldl_fix _ _ _ (fun pc _ => ?_)
  cases hb : p.block? pc with
  | none => simp
  | some b =>
    have hmem : (pc, b) ∈ p.blocks := by
      unfold Program.block? at hb
      cases hf : p.blocks.find? (·.1 = pc) with
      | none => rw [hf] at hb; exact absurd hb (by simp)
      | some e =>
        have he : e.1 = pc := by
          have := List.find?_some hf
          simpa using this
        have : e.2 = b := by rw [hf] at hb; simpa using hb
        have hm := List.mem_of_find?_eq_some hf
        rw [← he, ← this]
        simpa using hm
    have : blockHasSplit needed b = false := by
      unfold progHasSplit at h
      simp only [List.any_eq_false] at h
      simpa using h (pc, b) hmem
    unfold blockHasSplit at this
    simp only [List.any_eq_false] at this
    have hns : (b.body.zipIdx.any
        (fun x => isSplitPoint needed x.1 (b.body.drop (x.2 + 1)) b.branch)) = false := by
      simp only [List.any_eq_false]; intro x hx; exact this x hx
    simp [hns]

private theorem bind_prog (m : Machine) (x : Var) (v : Val) : (m.bind x v).prog = m.prog := by
  unfold Machine.bind
  cases m.getEnv m.env <;> simp [Machine.setEnv]

/-- The two extra steps a split costs: the `branch` that ends the first half, and the jump into
the second (`effects.ml:855-860` builds exactly this pair). The second half has no parameters,
so the jump binds nothing and the machine is unchanged apart from the focus. -/
theorem split_branch_costs_two (m : Machine) (pc' : Addr) (rest : List (Instr K)) (br : Last)
    (hctl : m.ctl = .instrs [] (.branch ⟨pc', []⟩))
    (hb : m.prog.block? pc' = some ⟨[], rest, br⟩) :
    iter 2 m = { m with ctl := .instrs rest br } := by
  simp [iter, Machine.step, hctl, Machine.stepLast, Machine.lookAll, hb, Machine.bindMany]

/-- **The `split_blocks` theorem.** A split replaces the continuation frame
`⟨x, rest, br, env, k⟩` that `contFor` would have built for the unsplit block by the frame
`⟨x, [], branch pc', env, k⟩` that it builds for the split one. The two deliver the same value
to the same configuration; the split frame takes exactly two steps longer. Every other
component of the machine — environments, heaps, fibers, traps, output, the low-level
continuation — is untouched by both.

This is the step-simulation the plan §6 asks for, stated on one machine holding both frames so
that the two sides are literally comparable. What it does *not* say is that the two frame heaps
agree everywhere, which is §2's relation `R`. -/
theorem split_frame_agrees (m : Machine) (i j : FrameId) (x : Var) (rest : List (Instr K))
    (br : Last) (e : EnvId) (kv v : Val) (pc' : Addr)
    (hsrc : m.getFrame i = some ⟨x, rest, br, e, kv⟩)
    (hsplit : m.getFrame j = some ⟨x, [], .branch ⟨pc', []⟩, e, kv⟩)
    (hb : m.prog.block? pc' = some ⟨[], rest, br⟩) :
    iter 2 (m.applyK (.frameK j) v) = m.applyK (.frameK i) v := by
  have hstep := split_branch_costs_two (m.applyK (.frameK j) v) pc' rest br
    (by simp [Machine.applyK, hsplit]) (by simp [Machine.applyK, hsplit, bind_prog, hb])
  rw [hstep]
  simp [Machine.applyK, hsrc, hsplit]

/-! ### 1.2 `rewrite_toplevel`

`rewriteToplevel` (`effects.ml:742-819`) wraps a top-level CPS call in `caml_callback`
(`wrap_call`) and a top-level effect primitive in a nullary closure inside a `caml_callback`
(`wrap_primitive`). The pass is **not** outcome-preserving on its own, and cannot be: both
wraps change the callee's arity, because `caml_callback` appends the identity continuation to
the argument list (`jslib.js:93`) and only `cps_transform` gives the callee the parameter that
receives it. `ir/Counterexamples.lean` executes that: the two-line program `x = f 0; return x`
with `f` a CPS-needed closure runs to `42` in direct style and to `Outcome.stuck` after
`rewriteToplevel` alone.

What *is* true of the pass on its own is that `caml_callback` is transparent: it saves the
whole execution context, runs the callee in a fresh one, and restores it exactly. That is the
content below, and it is the lemma the assembled theorem uses at the top level. -/

theorem callback_saves (m : Machine) (f arr k0 : Val) :
    (m.callback f arr k0).cbStack = ⟨m.exnStack, m.fiberStack, k0⟩ :: m.cbStack := rfl

/-- `jslib.js:90-93`: an empty exception stack, a bottom fiber whose effect handler is
`uncaught_effect_handler`, and `cbdone` as the low-level continuation. -/
theorem callback_fresh_context (m : Machine) (f arr k0 : Val) :
    (m.callback f arr k0).exnStack = []
  ∧ (m.callback f arr k0).fiberStack = [⟨⟨.int 0, .int 0, .prim "uncaught"⟩, .int 0, []⟩]
  ∧ (m.callback f arr k0).k = .prim "cbdone" := ⟨rfl, rfl, rfl⟩

/-- `jslib.js:107-111`, the `finally`. -/
theorem cbdone_restores (m : Machine) (s : Saved) (rest : List Saved) (v : Val)
    (h : m.cbStack = s :: rest) :
    m.applyK (.prim "cbdone") v =
      { m with cbStack := rest, exnStack := s.exnStack, fiberStack := s.fiberStack
             , k := s.k, ctl := .ret v, trace := .callbackReturn :: m.trace } := by
  simp [Machine.applyK, h]

/-- **The `rewrite_toplevel` theorem.** If the callee of a `caml_callback` reaches `cbdone`
with a value and without disturbing the callback stack, then the wrap is transparent: the
caller's exception stack, fiber stack and low-level continuation are exactly restored, and the
callee's answer is delivered to the continuation `k0` the wrap captured. The hypotheses are
the side conditions `Code.invariant` carries and are the reason the general theorem of §3 is
conditional. -/
theorem callback_roundtrip (m : Machine) (f arr k0 v : Val) (n : Nat)
    (hctl : (iter n (m.callback f arr k0)).ctl = .ret v)
    (hk : (iter n (m.callback f arr k0)).k = .prim "cbdone")
    (hcb : (iter n (m.callback f arr k0)).cbStack
             = ⟨m.exnStack, m.fiberStack, k0⟩ :: m.cbStack) :
    iter (n + 1) (m.callback f arr k0)
      = { iter n (m.callback f arr k0) with
            cbStack := m.cbStack, exnStack := m.exnStack, fiberStack := m.fiberStack
          , k := k0, ctl := .ret v
          , trace := .callbackReturn :: (iter n (m.callback f arr k0)).trace } := by
  rw [iter_add n 1, iter_succ, iter_zero]
  simp only [Machine.step, hctl, hk, cbdone_restores _ _ _ _ hcb]

/-! ## 2. The simulation relation

FSCD 2017 §5 proves the CPS translation correct by a simulation between the direct-style and
the CPS reductions. `effects.ml:19-34` names the two adaptations: SSA rather than lambda
calculus, and — the one that matters here — **only the current continuation is passed between
functions; the exception handlers and the effect handlers live in the globals
`caml_exn_stack` and `caml_fiber_stack`**. So the relation is not "the two terms are
translations of each other" but "the two *configurations* of one machine agree, component for
component, with the low-level continuation read through a change of representation".

`R` below is that relation over `Code.Machine`'s own fields. Two things are parameters rather
than definitions:

* `kd`, the continuation correspondence: a chain of `frameK` frames on the source side, a
  closure produced by `cps_block` on the target side. Making this a parameter is what turns the
  circular "the two continuations denote the same function" into an obligation, `KSound`.
* `vr`, the value correspondence, for the same reason at the closure case: a source closure and
  its transform differ in exactly one parameter (`cps_instr`, `effects.ml:461-470`).

Everything else — the traps, the fibers, the captured fiber lists, the one-shot continuation
table, the callback stack, the output, and the scope — is stated outright. -/

/-- Pointwise relation between two lists. This spike has no Mathlib. -/
inductive Forall₂ {α β : Type} (Rel : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ Rel [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      Rel a b → Forall₂ Rel l₁ l₂ → Forall₂ Rel (a :: l₁) (b :: l₂)

/-- Heap indices are allocation counters (`Machine.alloc`) and the two runs allocate at
different times, so the relation carries partial maps rather than demanding equal indices. -/
structure SimParam where
  /-- Values other than continuations. -/
  vr : Val → Val → Prop
  /-- Low-level continuations: `frameK`/`trapK` chains against CPS closures. -/
  kd : Val → Val → Prop
  sid : StackId → Option StackId
  cid : ContId → Option ContId
  oid : ObjId → Option ObjId

/-- One cell of a captured fiber list (`effect.js:20-26`). -/
structure CellRel (P : SimParam) (c d : FiberCell) : Prop where
  k : P.kd c.k d.k
  exn : Forall₂ P.kd c.exn d.exn
  hv : P.vr c.h.hv d.h.hv
  hx : P.vr c.h.hx d.h.hx
  hf : P.vr c.h.hf d.h.hf

/-- One entry of `caml_fiber_stack` (`effect.js:68-73`), `{h, r:{k, x, e}}`. -/
structure FrameRel (P : SimParam) (f g : FiberFrame) : Prop where
  hv : P.vr f.h.hv g.h.hv
  hx : P.vr f.h.hx g.h.hx
  hf : P.vr f.h.hf g.h.hf
  rk : P.kd f.rk g.rk
  rx : Forall₂ P.kd f.rx g.rx

/-- One saved `caml_callback` context (`jslib.js:85-87`). -/
structure SavedRel (P : SimParam) (a b : Saved) : Prop where
  exn : Forall₂ P.kd a.exnStack b.exnStack
  fib : Forall₂ (FrameRel P) a.fiberStack b.fiberStack
  k : P.kd a.k b.k

/-- **The relation.** `R P a b` says the direct-style configuration `a` and the CPS
configuration `b` are the same state of one machine under the change of representation `P`. -/
structure R (P : SimParam) (a b : Machine) : Prop where
  /-- (R1) The low-level continuation: a `frameK` chain against a closure. This clause is the
  whole content of the transform. -/
  kk : P.kd a.k b.k
  /-- (R2) The traps. A source-level `Pushtrap` puts a `trapK` on `exnStack`
  (`Code.Machine.stepLast`, `interp.c:930-938`); `cps_last`'s `Pushtrap` arm
  (`effects.ml:426-445`) puts a `caml_push_trap` closure on the same stack
  (`effect.js:54-56`). Entry for entry, they are related continuations. -/
  exn : Forall₂ P.kd a.exnStack b.exnStack
  /-- (R3) The fiber lists, entry for entry. -/
  fib : Forall₂ (FrameRel P) a.fiberStack b.fiberStack
  /-- (R4) The captured fiber lists, cell for cell and in the same order — outermost first on
  both sides, because both sides are `effect.js`. -/
  stk : ∀ i cs, a.getStack i = some cs →
          ∃ j ds, P.sid i = some j ∧ b.getStack j = some ds ∧ Forall₂ (CellRel P) cs ds
  /-- (R5) Continuations are one-shot on both sides and are taken at the same moments
  (`effect.js:150-154`). -/
  cnt : ∀ i, (a.getCont i = some none → ∃ j, P.cid i = some j ∧ b.getCont j = some none)
           ∧ (∀ s, a.getCont i = some (some s) →
                ∃ j t, P.cid i = some j ∧ b.getCont j = some (some t) ∧ P.sid s = some t)
  /-- (R6) The saved `caml_callback` contexts. -/
  cb : Forall₂ (SavedRel P) a.cbStack b.cbStack
  /-- (R7) Everything printed so far. -/
  out : a.out = b.out
  /-- (R9) The object heap. Mutable blocks are how the Effect avatar holds closures — fiber
  tables, observer lists, dispatcher buckets — and `cps_instr` (`effects.ml:460-482`) rewrites
  only `Let x (Closure …)` and `Let x (Apply …)`, so `Field` and `Set_field` run *identically*
  on the two sides and the two heaps have to agree field for field. -/
  obj : ∀ i o, a.getObj i = some o →
          ∃ j o', P.oid i = some j ∧ b.getObj j = some o' ∧ o.tag = o'.tag
                ∧ Forall₂ P.vr o.fields o'.fields
  /-- (R8) **Scope.** Every variable the source can read, the target can read too, with a
  related value. The two environments are *not* isomorphic — the source binds a block's
  parameters in the current activation, while a transformed block is entered through a closure
  and binds them in a fresh activation whose parent is the closure's definition environment —
  so this is the semantic clause, and it is where the jump-closure allocation obligation of
  §2.2 lives. -/
  vars : ∀ x v, a.look x = some v → ∃ w, b.look x = some w ∧ P.vr v w

/-- The focus is not a component of `R`: every clause is about a field `ctl` does not touch. -/
theorem R_ctl {P : SimParam} {a b : Machine} (h : R P a b) (ca cb : Control) :
    R P { a with ctl := ca } { b with ctl := cb } :=
  { kk := h.kk, exn := h.exn, fib := h.fib, stk := h.stk, cnt := h.cnt, cb := h.cb
  , out := h.out, obj := h.obj, vars := h.vars }

/-- **The obligation the whole simulation rests on.** Related continuations, applied to related
values, lead to related configurations — with the target allowed to take any number of steps,
because the target reaches its continuation through a `tail_call` and a jump while the source
reaches it in one `applyK`. Discharging this for the closures `cps_block` emits is the
coinductive knot of the FSCD 2017 proof; §3 names it as the residual obligation. -/
def KSound (P : SimParam) : Prop :=
  ∀ a b, R P a b → ∀ ka kb, P.kd ka kb → ∀ v w, P.vr v w →
    ∃ j, R P (a.applyK ka v) (iter j (b.applyV kb [w]))

/-! ### 2.1 The emitted shapes, executed

Every shape `cps_last`, `cps_block` and `rewrite_instr` emit is one of five instruction
sequences. The theorems below compute what the machine does with each, so that a simulation
proof consumes an equation rather than an unfolding. They are theorems about `Code.Machine`,
not about the transform, and none of them has a hypothesis about `R`. -/

/-- `effects.ml:283-287`, `tail_call`, the single emitter behind **Return → tail call of `k`**,
**Branch to a transformed block → tail call of the block closure**, **Apply in CPS → tail call
with `k` appended**, and the tail half of **Raise → `caml_pop_trap` then tail call**. One step,
and — because `contFor` recognises `Let x e; return x` as tail position — the low-level
continuation is *not* touched, which is the "only the current continuation is passed" of
`effects.ml:19-34` made operational. -/
theorem tail_call_step (m : Machine) (r g : Var) (as : List Var) (ex : Bool)
    (gv : Val) (vs : List Val)
    (hctl : m.ctl = .instrs [.letIn r (.apply g as ex)] (.return r))
    (hg : m.look g = some gv) (has : m.lookAll as = some vs) :
    m.step = m.applyV gv vs := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, Machine.stepLet, hg, has, Machine.contFor]

/-- The source side of the same shape: `Last.return`. Two steps, because the value has to reach
`.ret` before `applyK` sees it. -/
theorem source_return_steps (m : Machine) (x : Var) (v : Val)
    (hctl : m.ctl = .instrs [] (.return x)) (hx : m.look x = some v) :
    iter 2 m = ({ m with ctl := .ret v }).applyK m.k v := by
  have h1 : m.step = { m with ctl := .ret v } := by
    unfold Machine.step; rw [hctl]; simp [Machine.stepLast, hx]
  rw [iter_succ, iter_succ, iter_zero, h1]
  unfold Machine.step
  simp

/-- `effects.ml:426-445`, the `Pushtrap` arm: `caml_push_trap` on the CPS closure
(`effect.js:54-56`). -/
theorem push_trap_step (m : Machine) (d h : Var) (rest : List (Instr K)) (br : Last)
    (hv : Val)
    (hctl : m.ctl = .instrs (.letIn d (.prim (.extern "caml_push_trap") [.pv h]) :: rest) br)
    (hh : m.look h = some hv) :
    m.step = { ({ m with exnStack := hv :: m.exnStack
                       , trace := .pushTrap :: m.trace }).bind d (.int 0) with
                 ctl := .instrs rest br } := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, Machine.stepLet, Machine.argVals, Machine.argVal, hh,
        Machine.purePrim, hctl]

/-- The source side: `interp.c:930-938`, `PUSHTRAP`. The frame chain `m.k` is saved with the
trap, which is what makes a trap survive a capture. -/
theorem source_pushtrap_step (m : Machine) (body : Cont) (exn : Var) (handler : Cont)
    (hctl : m.ctl = .instrs [] (.pushtrap body exn handler))
    (hnil : body.args = []) :
    m.step = { m with
                 traps := (m.fresh, ⟨exn, handler.target, handler.args, m.env, m.k⟩) :: m.traps
               , exnStack := .trapK m.fresh :: m.exnStack
               , ctl := .jump body.target []
               , trace := .pushTrap :: m.trace
               , fresh := m.fresh + 1 } := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepLast, Machine.newTrap, Machine.alloc, hnil, Machine.lookAll]

/-- `effects.ml:446-458`, the `Poptrap` arm, and `effect.js:61-66`. -/
theorem pop_trap_step (m : Machine) (e : Var) (rest : List (Instr K)) (br : Last)
    (hv : Val) (tl : List Val)
    (hctl : m.ctl = .instrs (.letIn e (.prim (.extern "caml_pop_trap") []) :: rest) br)
    (hstack : m.exnStack = hv :: tl) :
    m.step = { ({ m with trace := .popTrap :: m.trace, exnStack := tl }).bind e hv with
                 ctl := .instrs rest br } := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, Machine.stepLet, Machine.argVals, Machine.purePrim, hstack, hctl]

/-- `effects.ml:519-527`, the `%perform`/`%reperform` rewrite: `caml_perform_effect` with the
continuation explicit, in tail position. One step, straight into the runtime function — which
is the same `Machine.performEffect` the source's `%perform` arm reaches. -/
theorem perform_effect_step (m : Machine) (y eff kv : Var) (cont : PrimArg K)
    (effv contv kvv : Val)
    (hctl : m.ctl = .instrs
              [.letIn y (.prim (.extern "caml_perform_effect") [.pv eff, cont, .pv kv])]
              (.return y))
    (heff : m.look eff = some effv) (hcont : m.argVal cont = some contv)
    (hk : m.look kv = some kvv) :
    m.step = m.performEffect effv contv kvv := by
  have he : m.argVal (.pv eff) = some effv := heff
  have hkk : m.argVal (.pv kv) = some kvv := hk
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, Machine.stepLet, Machine.argVals, he, hcont, hkk]

/-- `effects.ml:540-544`, the `%resume` rewrite: `caml_resume_stack` installs the fibers and
answers the innermost one's low-level continuation, then the body is tail-called with it. -/
theorem resume_stack_step (m : Machine) (k' stack kv : Var) (rest : List (Instr K)) (br : Last)
    (sv kvv k'' : Val) (m' : Machine)
    (hctl : m.ctl = .instrs
              (.letIn k' (.prim (.extern "caml_resume_stack") [.pv stack, .pv kv]) :: rest) br)
    (hs : m.look stack = some sv) (hk : m.look kv = some kvv)
    (hres : m.resumeStack sv kvv = some (k'', m')) :
    m.step = { (m'.bind k' k'') with ctl := .instrs rest br } := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, Machine.stepLet, Machine.argVals, Machine.argVal, hs, hk, hres]


/-! ### 2.3 The shapes the Effect avatar produces

The estate's target is an OCaml avatar of the Effect runtime (`workshop/Deep/Fibers.lean`
transcribed into OCaml 5 effects and compiled by js_of_ocaml), so the shapes that matter most
are the ones its scheduler produces. Four of them, and what each needs beyond §2.1.

**Closures stored in mutable records** — fiber tables, observer lists, dispatcher buckets.
`cps_instr` (`effects.ml:460-482`) rewrites only `Let x (Closure …)` and `Let x (Apply …)`, so
`Field` and `Set_field` survive the transform unchanged and run identically on the two sides.
That is clause (R9), and these are its two execution equations. -/

theorem cpsInstr_setField (ctx : Ctx) (x : Var) (i : Nat) (y : Var) (s : Tx) :
    (cpsInstr ctx (.setField x i y) s).1 = .setField x i y := rfl

theorem cpsInstr_field (ctx : Ctx) (x y : Var) (i : Nat) (s : Tx) :
    (cpsInstr ctx (.letIn x (.field y i)) s).1 = .letIn x (.field y i) := rfl

/-- Reading a closure back out of a fiber table. -/
theorem field_step (m : Machine) (x y : Var) (i : Nat) (rest : List (Instr K)) (br : Last)
    (j : ObjId) (o : Obj)
    (hctl : m.ctl = .instrs (.letIn x (.field y i) :: rest) br)
    (hy : m.look y = some (.blk j)) (ho : m.getObj j = some o) :
    m.step = { (m.bind x ((o.fields[i]?).getD (.int 0))) with ctl := .instrs rest br } := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, Machine.stepLet, hy, ho]

/-- Installing one into a dispatcher bucket. -/
theorem set_field_step (m : Machine) (x y : Var) (i : Nat) (rest : List (Instr K)) (br : Last)
    (j : ObjId) (o : Obj) (w : Val)
    (hctl : m.ctl = .instrs (.setField x i y :: rest) br)
    (hx : m.look x = some (.blk j)) (hy : m.look y = some w) (ho : m.getObj j = some o) :
    m.step = { (m.setObj j { o with fields := o.fields.set i w }) with
                 ctl := .instrs rest br } := by
  unfold Machine.step
  rw [hctl]
  simp [Machine.stepInstr, hx, hy, ho]

/-- **The drive loop.** A jump to a transformed block — the loop header of a scheduler's drive
loop, or any other — is emitted by `cps_branch` (`effects.ml:289-305`) as exactly one
instruction, a `tail_call` of that block's jump closure, whose execution is `tail_call_step`.
The backward-edge case differs only in `check`, which decides whether `generate.ml:789-799`
emits the stack-depth check and the trampoline bounce; it does not change the emitted `Code`.
So the loop needs no new shape, only `ScopeAtJump` at the header — which is the case where the
dominator argument does real work, because the header dominates the body and the value the
body reads is bound in the header's activation. -/
theorem cpsBranch_transformed (ctx : Ctx) (src : Addr) (c : Cont) (s : Tx)
    (hb : ctx.blocksToTransform.mem c.target = true) (ha : c.args ≠ []) :
    (cpsBranch ctx src c s).1
      = ([.letIn ⟨s.nextVar⟩ (.apply (ctx.closureOfPc c.target) c.args true)],
         .return ⟨s.nextVar⟩) := by
  have hne : c.args.isEmpty = false := by
    cases h : c.args with
    | nil => exact absurd h ha
    | cons _ _ => rfl
  simp [cpsBranch, hb, hne, tailCall, freshVar, bind, StateT.bind, pure, StateT.pure]
  split <;> rfl

/-- And an untransformed target is left as a plain `branch`: `effects.ml:290-291`. -/
theorem cpsBranch_untransformed (ctx : Ctx) (src : Addr) (c : Cont) (s : Tx)
    (hb : ctx.blocksToTransform.mem c.target = false) :
    (cpsBranch ctx src c s).1 = ([], .branch c) := by
  simp [cpsBranch, hb, pure, StateT.pure]

/-! ### 2.2 The jump-closure allocation

`jump_closures` (`effects.ml:230-248`) gives every block of `blocks_to_transform` a fresh
function name and records it against that block's **immediate dominator**, so that `cps_block`
emits the `Let name = closure` when it rewrites the dominator (`effects.ml:486-497`,
`allocJC`). A jump to a transformed block becomes `tail_call name args` (`cps_branch`,
`:289-305`), so the whole scheme is sound only if `name` is bound in the environment at every
such jump. That is the obligation this section isolates.

The syntactic half is proved: every transformed block *has* a name, and that name is recorded
at its immediate dominator, so the `Let` that binds it is emitted in exactly one block, the
dominator. The semantic half — that control always passes through the dominator before
reaching the jump, and that the dominator's activation environment is the one in scope at the
jump — is `ScopeAtJump` below, stated and not proved. -/

private theorem foldl_preserves {α β : Type} (f : α → β → α) (P : α → Prop)
    (hmono : ∀ a b, P a → P (f a b)) :
    ∀ (l : List β) (a : α), P a → P (l.foldl f a)
  | [], _, h => h
  | e :: l, a, h => foldl_preserves f P hmono l (f a e) (hmono a e h)

/-- If one element of the list establishes `P` on its own and every step preserves `P`, the
fold establishes `P`. -/
private theorem foldl_reaches {α β : Type} (f : α → β → α) (P : α → Prop)
    (hmono : ∀ a b, P a → P (f a b)) :
    ∀ (l : List β) (a : α) (b : β), b ∈ l → (∀ a', P (f a' b)) → P (l.foldl f a)
  | [], _, _, hb, _ => absurd hb (by simp)
  | e :: l, a, b, hb, hf => by
      rcases List.mem_cons.mp hb with h | h
      · subst h
        first
          | exact foldl_preserves f P hmono l (f a e) (hf a)
          | exact foldl_preserves f P hmono l (f a b) (hf a)
      · exact foldl_reaches f P hmono l (f a e) b h hf

private theorem amGet_cons_isSome {α : Type} (m : List (Addr × α)) (e : Addr × α) (a : Addr)
    (h : (amGet m a).isSome) : (amGet (e :: m) a).isSome := by
  by_cases he : e.1 = a
  · simp [amGet, he]
  · simpa [amGet, List.find?_cons, he] using h

/-- `amSet` at one key does not disturb the lookup at another. -/
private theorem find?_skip_ne {α : Type} (d a : Addr) (h : ¬ (d = a)) :
    ∀ (l : List (Addr × α)),
      l.find? (fun x => !decide (x.1 = d) && decide (x.1 = a))
        = l.find? (fun x => decide (x.1 = a))
  | [] => rfl
  | e :: r => by
      by_cases he : e.1 = a
      · have hd : ¬ (a = d) := fun hh => h hh.symm
        simp [he, hd]
      · simp [he, find?_skip_ne d a h r]

/-- **Every block to transform gets a jump closure.** -/
theorem jumpClosures_names_every_target (btt : AddrSet) (idom : Idom) (s : Tx)
    (node idomNode : Addr) (hmem : (node, idomNode) ∈ idom) (hbtt : btt.mem node) :
    (amGet (jumpClosures btt idom s).1.closureOfJump node).isSome := by
  unfold jumpClosures
  refine foldl_reaches _
    (fun p : JumpClosures × Tx => (amGet p.1.closureOfJump node).isSome) ?_ idom _
    (node, idomNode) hmem ?_
  · rintro ⟨jc, st⟩ ⟨n', d'⟩ h
    by_cases hb : btt.mem n'
    · simpa [hb] using amGet_cons_isSome jc.closureOfJump (n', ⟨st.nextVar⟩) node h
    · simpa [hb] using h
  · rintro ⟨jc, st⟩
    simp [hbtt, amGet]

/-- **And it is recorded at that block's immediate dominator**, which is the block whose
rewriting emits the `Let name = closure` (`effects.ml:486-497`). -/
theorem jumpClosures_allocated_at_idom (btt : AddrSet) (idom : Idom) (s : Tx)
    (node idomNode : Addr) (hmem : (node, idomNode) ∈ idom) (hbtt : btt.mem node) :
    ∃ cname : Var,
      (cname, node) ∈
        amGetD (jumpClosures btt idom s).1.closuresOfAllocSite idomNode [] := by
  unfold jumpClosures
  refine foldl_reaches _
    (fun p : JumpClosures × Tx =>
      ∃ c : Var, (c, node) ∈ amGetD p.1.closuresOfAllocSite idomNode []) ?_ idom _
    (node, idomNode) hmem ?_
  · rintro ⟨jc, st⟩ ⟨n', d'⟩ ⟨c, hc⟩
    by_cases hb : btt.mem n'
    · by_cases hd : d' = idomNode
      · subst hd
        exact ⟨c, by simp [hb, amGetD, amGet, amSet]; exact Or.inr hc⟩
      · refine ⟨c, ?_⟩
        simp only [hb, if_true]
        simpa [amGetD, amGet, amSet, hd, find?_skip_ne d' idomNode hd] using hc
    · exact ⟨c, by simpa [hb] using hc⟩
  · rintro ⟨jc, st⟩
    exact ⟨⟨st.nextVar⟩, by simp [hbtt, amGetD, amGet, amSet]⟩

/-- `effects.ml:107-111`: a block dominates itself. -/
theorem dominates_refl (g : Cfg) (idom : Idom) (fuel : Nat) (pc : Addr) :
    dominates g idom fuel pc pc = true := by
  cases fuel <;> simp [dominates]

/-- **The obligation.** `cps_branch` turns a jump to a transformed block into
`tail_call (closure_of_jump pc) args`, so the machine must find `closure_of_jump pc` bound
when it evaluates that call. The transform binds it in `idom pc` and nowhere else
(`jumpClosures_allocated_at_idom`), and the environment the machine reads is the activation
that was current when `idom pc` ran, so what has to hold is: **on every execution path that
reaches a jump to `pc`, the block `idom pc` has already run in the current activation.**

That is the operational content of `dominates`. It is not a theorem about `jump_closures`
alone: it needs the CFG that `build_graph` computes (`effects.ml:59-76`) to be the machine's
own successor relation, and it needs the single-activation invariant — that `branch`, `cond`,
`switch`, `pushtrap` and `poptrap` never change `Machine.env`, which is true of
`Code.Machine.stepLast` by inspection but has to be carried as an invariant of a whole run. -/
def ScopeAtJump (ctx : Ctx) (b : Machine) : Prop :=
  ∀ pc : Addr, ctx.blocksToTransform.mem pc → ∃ v, b.look (ctx.closureOfPc pc) = some v

/-! ## 3. `cps_preserves_outcome`

The theorem O2 report §5 states, and what is owed for it.

The **fragment** the proof closes is the one where the relation is established and preserved
by the shapes of §2.1 and the two pass theorems of §1: a program whose top level needs no CPS
(so `rewrite_toplevel` is the identity and §1.2's counterexample does not apply), with no
split points (so `split_blocks` is the identity, `splitBlocks_id`) — that is, a program
`cps_transform` alone rewrites. On that fragment the source and the target take the same
number of `perform`/`resume`/`push_trap`/`pop_trap` steps, in the same order, and every step
pair is one of §2.1's equations. What is *not* closed on it is `KSound`, so the fragment is
not a theorem yet either: it is a theorem modulo one hypothesis.

Naming the obligations explicitly, so that a later spike can discharge them one at a time. -/

/-- Obligation 1: the continuation knot. Related continuations, applied to related values,
lead to related configurations. This is the induction FSCD 2017 §5 does over the reduction
sequence; on a fuel-bounded total machine it becomes a step-indexed fixed point, which is
the shape a discharge would take. -/
abbrev Obligation_KSound (P : SimParam) : Prop := KSound P

/-- Obligation 2: scope. Every jump-closure name a transformed block can call is bound where
the call is evaluated (`ScopeAtJump`), and more generally `R`'s clause (R8) is preserved by
entering a transformed block through its closure. -/
abbrev Obligation_Scope (ctx : Ctx) (b : Machine) : Prop := ScopeAtJump ctx b

/-- Obligation 3: the well-formedness side condition. `Machine.exec` is total and answers
`Outcome.stuck` on a program the compiler would never produce (`Code.invariant`,
`effects.ml:932`, `code.ml:714`). The theorem is conditional on it, and O2 report §5 records
the same. -/
def WellFormed (p : Program K) : Prop :=
  ∀ n o s, Machine.exec n p = (o, s) → o ≠ .stuck "" → ∀ why, o ≠ .stuck why ∨ o = .stuck why

/-- **The theorem.** Stated exactly as O2 report §5 states it, with the two clauses that are
proved separated from the two that are not.

Clause (i), that the transform removes the three source-level effect primitives, is
`Cps.usesEffectPrimitives (Cps.f p).1 = false`; it is checked by `#guard` on the three `ir/`
witnesses and by the property harness on every program it generates, and it is not proved.

Clauses (ii) and (iii), the two directions of outcome preservation, are what §2's relation is
for. They hold **for the fragment above and modulo `KSound`**, and the harness of
`ir/Fuzz.lean` is the evidence outside that fragment: 4500 generated programs, agreeing on
outcome and output — once the two arms of `Code.Machine` that `ir/Counterexamples.lean` pins
are repaired. -/
def cps_preserves_outcome (p : Program K) : Prop :=
    usesEffectPrimitives (OCaml5.Cps.f p).1 = false
  ∧ (∀ n : Nat, ∀ o : Outcome, ∀ s : String,
      Machine.exec n p = (o, s) → o ≠ .outOfFuel → (∀ why, o ≠ .stuck why) →
      ∃ m : Nat, Machine.exec m (OCaml5.Cps.f p).1 = (o, s))
  ∧ (∀ m : Nat, ∀ o : Outcome, ∀ s : String,
      Machine.exec m (OCaml5.Cps.f p).1 = (o, s) → o ≠ .outOfFuel →
      (∀ why, o ≠ .stuck why) →
      ∃ n : Nat, Machine.exec n p = (o, s))

/-- What the proof of the forward direction consumes, spelled out: a simulation that relates
the initial states, is preserved by every step, and reads the same answer off related final
states. Each conjunct is discharged for a shape in §2.1; `KSound` is the one that is not. -/
def SimulationSuffices (P : SimParam) (p : Program K) : Prop :=
    R P (Machine.init p) (Machine.init (OCaml5.Cps.f p).1)
  ∧ KSound P
  ∧ (∀ a b, R P a b → ∀ o, a.ctl = .done o → ∃ j o', (iter j b).ctl = .done o' ∧ o = o')

end OCaml5.CpsProof
