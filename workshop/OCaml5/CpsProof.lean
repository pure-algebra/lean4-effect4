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

/-! ## 4. Round three: the four shapes spike A0 asked for

`docs/research/2026-09-04-spike-a0-avatar.md` §1 routes four requests to this seat. They are
taken here in its order. The block shapes are no longer invented: `ir/RunUnderHandler.lean`
transcribes the one the avatar's fixture actually compiles to, checked against the compiler's
own `--debug effects` dump. -/

/-! ### 4.1 (A0 P2-1) The shape `run_under_handler` compiles to

The real shape, from `ir/RunUnderHandler.lean`: a closure whose entry block ends in a CPS call,
`split_blocks` cutting it so that one block — the only member of `blocks_to_transform` — is a
jump-closure target allocated at its immediate dominator, that block carrying a `Set_field` on
a mutable record and a `Cond`, and one arm of the `Cond` being a block whose last instruction
is a `%perform` **in tail position**, all of it under the `Pushtrap` of the enclosing
`Fun.protect`.

Four of the five pieces are already theorems: the split is `split_frame_agrees`, the jump
closure at the dominator is `jumpClosures_allocated_at_idom`, the `Set_field` is
`cpsInstr_setField` with clause (R9), and the `Pushtrap` is `push_trap_step` against
`source_pushtrap_step`. The fifth is the tail `%perform`, and it is the one below: what
`cps_block` emits for such a block, exactly. -/

/-- An instruction `cps_instr` does not rewrite (`effects.ml:460-482` touches only
`Let x (Closure …)` and `Let x (Apply …)`). The three instructions before the `%perform` in the
avatar's block 305 — a constant, a `Field`, a `Block` — are all inert, and so is the
`Set_field` of block 649. -/
def Inert : Instr K → Prop
  | .letIn _ (.closure _ _) => False
  | .letIn _ (.apply _ _ _) => False
  | _ => True

theorem cpsInstr_inert (ctx : Ctx) (i : Instr K) (s : Tx) (h : Inert i) :
    cpsInstr ctx i s = (i, s) := by
  cases i with
  | letIn x e => cases e <;> first | rfl | exact absurd h (by simp [Inert])
  | _ => rfl

theorem mapM_cpsInstr_inert (ctx : Ctx) :
    ∀ (l : List (Instr K)) (s : Tx), (∀ i ∈ l, Inert i) → (l.mapM (cpsInstr ctx)) s = (l, s)
  | [], s, _ => rfl
  | i :: l, s, h => by
      have hi : Inert i := h i (by simp)
      have hl : ∀ j ∈ l, Inert j := fun j hj => h j (by simp [hj])
      simp [List.mapM_cons, bind, StateT.bind, cpsInstr_inert ctx i s hi,
            mapM_cpsInstr_inert ctx l s hl, pure, StateT.pure]

/-- **The tail-`%perform` block, as `cps_block` rewrites it** (`effects.ml:484-598` with
`rewrite_instr` `:519-527`). The `%perform` is in tail position, so `split_blocks` left the
block whole (`isSplitPoint` is false for `Let x e; return x`, `:833-834`) and `rewrite_instr`
turns it into `caml_perform_effect` with the continuation `k` supplied by the caller — one
instruction, still in tail position. Everything before it is inert and survives verbatim.

Composed with `perform_effect_step`, this says the target's single step on the rewritten block
is `Machine.performEffect` on the same three values the source's `%perform` arm reaches, so the
whole difference between the two runs of this block is which value plays `k`: a `frameK` on the
source, the block's continuation closure on the target. That is clause (R1), and it is all that
is left of this shape. -/
theorem cpsBlock_tail_perform (ctx : Ctx) (k : Var) (pc : Addr) (ps : List Var)
    (pre : List (Instr K)) (x eff res : Var) (s : Tx)
    (hjc : amGetD ctx.jc.closuresOfAllocSite pc [] = [])
    (hinert : ∀ i ∈ pre, Inert i) :
    (cpsBlock ctx k pc
        { params := ps
        , body := pre ++ [.letIn x (.prim (.extern "%perform") [.pv eff])]
        , branch := .return res } s).1
      = { params := if ctx.blocksToTransform.mem pc then [] else ps
        , body := pre ++ [.letIn ⟨s.nextVar⟩ (.prim (.extern "caml_perform_effect")
                            [.pv eff, .pc (.int 0), .pv k])]
        , branch := .return ⟨s.nextVar⟩ } := by
  simp [cpsBlock, hjc, rewriteInstr, freshVar, bind, StateT.bind, pure, StateT.pure,
        mapM_cpsInstr_inert ctx pre _ hinert]

/-! ### 4.2 (A0 P2-2) `caml_resume_stack` at depth 1

The avatar installs exactly one handler per fiber and never `reperform`s, so every fiber list
it ever resumes has one cell. At that depth the whole of `caml_resume_stack` (`effect.js:78-91`)
and `caml_pop_fiber` (`:96-102`) collapses to a pair of theorems, and the second is the one
worth having: **resume-then-pop is the identity on the machine, trace apart.** -/

theorem resumeStack_depth_one (m : Machine) (i : StackId) (c : FiberCell) (k : Val)
    (h : m.getStack i = some [c]) :
    m.resumeStack (.stackRef i) k
      = some (c.k, { m with fiberStack := ⟨c.h, k, m.exnStack⟩ :: m.fiberStack
                          , exnStack := c.exn
                          , trace := .resumeStack 1 :: m.trace }) := by
  simp [Machine.resumeStack, h, Machine.resumeCells]

/-- One handler per fiber: installing it and taking it off again restores `caml_exn_stack`,
`caml_fiber_stack` and the low-level continuation exactly. Every other component was never
touched. This is the whole of the avatar's use of the fiber discipline. -/
theorem resume_pop_depth_one (m : Machine) (i : StackId) (c : FiberCell) (k : Val)
    (h : m.getStack i = some [c]) :
    ∃ m', m.resumeStack (.stackRef i) k = some (c.k, m')
        ∧ m'.popFiber = (k, { m with trace := .popFiber :: .resumeStack 1 :: m.trace }) := by
  refine ⟨_, resumeStack_depth_one m i c k h, ?_⟩
  simp [Machine.popFiber]

/-! ### 4.3 (A0 P2-3) The trampoline and the back-edge check

The avatar's `drive`/`flush_all` recursion is a back edge, and `generate.ml:789-799,1019` guards
back edges with `caml_stack_check_depth()` and a `caml_trampoline_return` bounce. Which calls
get the guard is `Effects.f`'s second answer, `cps_calls`, and `cps_branch` decides it by one
comparison: `check` is true exactly on a **backward** edge (`effects.ml:302-304`, "only for
backward edges, so at least once per loop iteration").

The two theorems below say that, and `cpsBranch_transformed` above says the thing that matters
for the CPS theorem: **`check` does not change the emitted `Code` at all.** It changes only
which set the call's result variable lands in, and therefore only what `generate.ml` wraps it
in. So the trampoline is invisible to `Code.Machine` and cannot affect `cps_preserves_outcome`;
what it affects is whether the JavaScript engine's own stack overflows, which this machine does
not model and which is named in §7 as out of scope. -/

theorem cpsBranch_backedge_is_trampolined (ctx : Ctx) (src : Addr) (c : Cont) (s : Tx)
    (hb : ctx.blocksToTransform.mem c.target = true) (ha : c.args ≠ [])
    (hback : ctx.cfg.ord c.target ≤ ctx.cfg.ord src) :
    ((cpsBranch ctx src c s).2).cpsCalls.contains ⟨s.nextVar⟩ = true := by
  have hne : c.args.isEmpty = false := by
    cases h : c.args with
    | nil => exact absurd h ha
    | cons _ _ => rfl
  simp [cpsBranch, hb, hne, tailCall, freshVar, bind, StateT.bind, pure, StateT.pure,
        hback, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, VarSet.insert]
  split <;> simp_all

theorem cpsBranch_forward_not_trampolined (ctx : Ctx) (src : Addr) (c : Cont) (s : Tx)
    (hb : ctx.blocksToTransform.mem c.target = true) (ha : c.args ≠ [])
    (hfwd : ¬ (ctx.cfg.ord c.target ≤ ctx.cfg.ord src)) :
    ((cpsBranch ctx src c s).2).cpsCalls = s.cpsCalls := by
  have hne : c.args.isEmpty = false := by
    cases h : c.args with
    | nil => exact absurd h ha
    | cons _ _ => rfl
  simp [cpsBranch, hb, hne, tailCall, freshVar, bind, StateT.bind, pure, StateT.pure, hfwd]

/-! ### 4.4 (A0 P2-4) The deviation, as an explicit hypothesis

`effects.ml:19-34`: only the current continuation is passed between functions, while the
exception handlers and the effect handlers live in the two global variables `caml_exn_stack`
and `caml_fiber_stack`. A0's point is sharp: the avatar's `interruptRecord` mutates
handler-side state *between* two entries into the same global stack, so a relation quantified
over closed terms would not see it and the theorem would be about a language the avatar does
not write.

`R` is already a relation over machine *states* rather than over terms, which is the design
decision that answers this — but it should be named, so here it is as a predicate, together
with the one closure property that makes it usable: `R` survives an arbitrary handler-side
mutation of the heap, provided the two sides mutate in step. That is the formal content of
"the handler may change state between two entries", and it holds because `Set_field` is not
rewritten by the transform (`cpsInstr_setField`) and clause (R9) is over the heaps. -/

/-- The deviation itself: the two handler stacks are global, and the relation is over their
whole contents rather than over any one continuation. -/
def GlobalHandlerStacks (P : SimParam) (a b : Machine) : Prop :=
    Forall₂ P.kd a.exnStack b.exnStack
  ∧ Forall₂ (FrameRel P) a.fiberStack b.fiberStack

theorem R_gives_globalHandlerStacks {P : SimParam} {a b : Machine} (h : R P a b) :
    GlobalHandlerStacks P a b := ⟨h.exn, h.fib⟩

private theorem getObj_setObj_eq (m : Machine) (j : ObjId) (o : Obj) :
    (m.setObj j o).getObj j = some o := by
  simp [Machine.getObj, Machine.setObj]

private theorem getObj_setObj_ne (m : Machine) (i j : ObjId) (o : Obj) (h : ¬ (i = j)) :
    (m.setObj j o).getObj i = m.getObj i := by
  have hji : ¬ (j = i) := fun hh => h hh.symm
  simp [Machine.getObj, Machine.setObj, hji, find?_skip_ne j i hji m.mem]

private theorem Forall₂_set {α β : Type} {Rel : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (n : Nat) {w : α} {w' : β},
      Forall₂ Rel l₁ l₂ → Rel w w' → Forall₂ Rel (l₁.set n w) (l₂.set n w')
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, 0, _, _, .cons _ ht, hw => .cons hw ht
  | _, _, n + 1, _, _, .cons hh ht, hw => .cons hh (Forall₂_set n ht hw)

/-- **Handler-side state may change between two entries.** If the two sides write related
values into corresponding slots of corresponding blocks, `R` is preserved: every other clause
is about a field `setObj` does not touch, and clause (R9) is closed under a pointwise update.
`hinj` is the only side condition — the object correspondence must not send two source blocks
to one target block, which is true of any correspondence built by allocation. -/
theorem R_setField {P : SimParam} {a b : Machine} (h : R P a b)
    (j j' : ObjId) (o o' : Obj) (n : Nat) (w w' : Val)
    (hj : P.oid j = some j') (ha : a.getObj j = some o) (hb : b.getObj j' = some o')
    (hw : P.vr w w')
    (hinj : ∀ x, P.oid x = some j' → x = j) :
    R P (a.setObj j { o with fields := o.fields.set n w })
        (b.setObj j' { o' with fields := o'.fields.set n w' }) := by
  refine { kk := h.kk, exn := h.exn, fib := h.fib, cnt := h.cnt, cb := h.cb, out := h.out
         , stk := ?_, obj := ?_, vars := ?_ }
  · intro i cs hi; exact h.stk i cs hi
  · intro i oo hi
    by_cases hij : i = j
    · subst hij
      rw [getObj_setObj_eq] at hi
      have hoo : oo = { o with fields := o.fields.set n w } := (Option.some.inj hi).symm
      obtain ⟨j2, o2, hj2, hb2, htag, hfs⟩ := h.obj i o ha
      have hj2' : j2 = j' := by rw [hj] at hj2; exact (Option.some.inj hj2).symm
      subst hj2'
      have ho2 : o2 = o' := by rw [hb] at hb2; exact (Option.some.inj hb2).symm
      subst ho2
      exact ⟨j2, { o2 with fields := o2.fields.set n w' }, hj,
             getObj_setObj_eq _ _ _, by rw [hoo]; exact htag,
             by rw [hoo]; exact Forall₂_set n hfs hw⟩
    · rw [getObj_setObj_ne _ _ _ _ hij] at hi
      obtain ⟨j2, o2, hj2, hb2, htag, hfs⟩ := h.obj i oo hi
      have hne : ¬ (j2 = j') := fun hcontra => hij (hinj i (hcontra ▸ hj2))
      exact ⟨j2, o2, hj2, by rw [getObj_setObj_ne _ _ _ _ hne]; exact hb2, htag, hfs⟩
  · intro y val hy; exact h.vars y val hy

/-! ## 5. Round four, part one: `ScopeAtJump`

`ScopeAtJump` (§2.2) is the claim that `closure_of_jump pc` is bound in the environment
wherever `cps_branch` emits a `tail_call` of it. §2.2 named the three things it needs; this
section proves the first two and reduces the third to a statement about `dominator_tree` alone,
with no machine in it.

1. **`build_graph`'s successor relation is the machine's** (§5.1). `effects.ml:59-76` builds the
   CFG from `Code.fold_children`, which is `Last.children`; the machine jumps only to a block
   that terminator names.
2. **The single-activation invariant** (§5.2). No terminator changes `Machine.env`, and neither
   does a jump or any instruction other than a call. Only `applyV` on a closure opens a new
   activation, and only `applyK` on a saved frame or trap returns to one.
3. **The dominator argument** (§5.4), which is now a hypothesis about `dominatorTree` and
   `Last.children` with no `Machine` in it at all. -/

/-! ### 5.1 The CFG is the machine's successor relation -/

/-- **One lemma, every terminator.** If `stepLast` hands control to block `pc`, then `pc` is one
of the addresses `Last.children` lists — which is exactly the successor set `build_graph`
(`effects.ml:59-76`) puts in the graph, since it is built from `Code.fold_children`
(`code.ml:590-603`). Read arm by arm: `return`, `raise` and `stop` never jump and the
hypothesis is absurd; `branch` and `poptrap` jump to their one continuation; `cond` jumps to
one of two, `switch` to one of its cases, and `pushtrap` to its body — the handler is reached
later, through the trap, not by this step. -/
private theorem switch_target_mem (cs : List Cont) (n : Nat) (c : Cont) (pc : Addr)
    (hc : cs[n]? = some c) (hpc : c.target = pc) : pc ∈ cs.map (·.target) := by
  subst hpc; exact List.mem_map_of_mem (List.mem_of_getElem? hc)

theorem stepLast_jump_mem_children (m : Machine) (br : Last) (pc : Addr) (args : List Val)
    (h : (m.stepLast br).ctl = .jump pc args) : pc ∈ br.children := by
  cases br
  case switch x cs =>
    simp only [Machine.stepLast] at h
    split at h
    · rename_i _ n hx
      split at h
      · rename_i _ c hc
        split at h
        · rename_i _ vs ha
          simp only [Last.children]
          exact switch_target_mem cs n.toNat c pc hc (by simp_all)
        · simp_all [Machine.stuck]
      · simp_all [Machine.stuck]
    · simp_all [Machine.stuck]
  all_goals
    simp only [Machine.stepLast, Machine.newTrap, Machine.alloc] at h
    repeat' split at h
    all_goals simp_all [Last.children, Machine.stuck]

/-- The same fact one level up: a machine whose focus is the end of a block hands control only
to a child of that block. -/
theorem step_jump_mem_children (m : Machine) (br : Last) (pc : Addr) (args : List Val)
    (hctl : m.ctl = .instrs [] br) (h : m.step.ctl = .jump pc args) : pc ∈ br.children := by
  apply stepLast_jump_mem_children m br pc args
  rwa [show m.stepLast br = m.step by unfold Machine.step; rw [hctl]]

/-! ### 5.2 The single-activation invariant

`Machine.env` names the activation whose bindings `look` reads. The transform's jump closures
are bound by a `Let` in the dominator's block, so they are visible at the jump exactly when the
jump happens in the same activation the dominator ran in. These are the lemmas that say every
step *inside* a block, and every jump between blocks, stays in that activation. -/

theorem stepLast_env (m : Machine) (br : Last) : (m.stepLast br).env = m.env := by
  cases br <;>
    simp only [Machine.stepLast, Machine.newTrap, Machine.alloc] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all [Machine.stuck]

theorem bindMany_env (m : Machine) : ∀ (xs : List Var) (vs : List Val),
    (m.bindMany xs vs).env = m.env
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, v :: vs => by
      rw [Machine.bindMany]
      rw [bindMany_env (m.bind x v) xs vs]
      unfold Machine.bind
      cases m.getEnv m.env <;> simp [Machine.setEnv]

/-- A jump stays in the activation: the block's parameters are bound *into the current
environment record*, which is why a `branch` needs no closure and why `cps_branch` can turn one
into a `tail_call` only when the target's closure is already in scope. -/
theorem step_env_of_jump (m : Machine) (pc : Addr) (args : List Val)
    (h : m.ctl = .jump pc args) : m.step.env = m.env := by
  unfold Machine.step
  simp only [h]
  split
  · simp [Machine.stuck]
  · simp [bindMany_env]

theorem step_env_of_last (m : Machine) (br : Last) (h : m.ctl = .instrs [] br) :
    m.step.env = m.env := by
  rw [show m.step = m.stepLast br by unfold Machine.step; rw [h]]
  exact stepLast_env m br

/-- The instructions that do **not** open an activation. `Apply` and `%resume` call `applyV`
in the same step and so may enter a closure; everything else — including `%perform`,
`%reperform` and `caml_callback`, which only *set the focus* to an `applyV` — leaves `env`
alone. -/
def NoEnter : Instr K → Prop
  | .letIn _ (.apply _ _ _) => False
  | .letIn _ (.prim (.extern "%resume") _) => False
  | _ => True

/-! Attempt 1 at `stepInstr_env` was a single `repeat' split` over `stepLet`'s primitive arm
followed by `simp_all` with every runtime function unfolded. It exceeded the heartbeat limit,
which this spike may not raise: `stepLet`'s `match p, vs` has eight patterns and the default
one reaches `purePrim`'s twenty, so the product is too large to unfold in one tactic. Attempt 2,
below, is the same theorem with one lemma per runtime function, so that each branch of the
split closes by `exact` on a lemma instead of by unfolding. -/

private theorem bind_env (m : Machine) (x : Var) (v : Val) : (m.bind x v).env = m.env := by
  unfold Machine.bind; cases m.getEnv m.env <;> simp [Machine.setEnv]

private theorem newObj_env (m : Machine) (o : Obj) : (m.newObj o).2.env = m.env := rfl
private theorem newStack_env (m : Machine) (cs : List FiberCell) :
    (m.newStack cs).2.env = m.env := rfl
private theorem newFrame_env (m : Machine) (r : FrameRec) : (m.newFrame r).2.env = m.env := rfl
private theorem newCont_env (m : Machine) : (m.newCont).2.env = m.env := rfl
private theorem setObj_env (m : Machine) (i : ObjId) (o : Obj) : (m.setObj i o).env = m.env :=
  rfl
private theorem setCont_env (m : Machine) (i : ContId) (o : Option StackId) :
    (m.setCont i o).env = m.env := rfl
private theorem popFiber_env (m : Machine) : m.popFiber.2.env = m.env := by
  unfold Machine.popFiber; cases m.fiberStack <;> rfl
private theorem contUse_env (m : Machine) (c : Val) : (m.contUse c).2.env = m.env := by
  unfold Machine.contUse
  cases c <;> try rfl
  case cont i => dsimp only; split <;> rfl
private theorem allocStack_env (m : Machine) (a b c : Val) :
    (m.allocStack a b c).2.env = m.env := rfl

private theorem resumeCells_env : ∀ (cs : List FiberCell) (m : Machine) (k : Val),
    (m.resumeCells k cs).2.env = m.env
  | [], _, _ => rfl
  | c :: cs, m, k => by
      rw [Machine.resumeCells]
      exact resumeCells_env cs _ c.k

private theorem resumeStack_env (m : Machine) (s k : Val) (k' : Val) (m' : Machine)
    (h : m.resumeStack s k = some (k', m')) : m'.env = m.env := by
  unfold Machine.resumeStack at h
  split at h
  · rename_i i
    split at h
    · rename_i cs hcs
      have : m' = { (m.resumeCells k cs).2 with
                      trace := .resumeStack cs.length :: (m.resumeCells k cs).2.trace } := by
        simp_all
      rw [this]
      simpa using resumeCells_env cs m k
    · simp at h
  · simp at h

private theorem contFor_env (m : Machine) (x : Var) (rest : List (Instr K)) (br : Last) :
    (m.contFor x rest br).2.env = m.env := by
  unfold Machine.contFor
  repeat' split
  all_goals simp_all [Machine.newFrame, Machine.alloc]

/-- `uncaughtEffect` resumes the carried continuation and then raises; neither touches `env`. -/
private theorem uncaughtEffect_env (m : Machine) (e c k : Val) :
    (m.uncaughtEffect e c k).env = m.env := by
  unfold Machine.uncaughtEffect
  dsimp only
  repeat' split
  all_goals
    first
      | (simp [Machine.unhandledExn, Machine.newObj, Machine.alloc]; done)
      | (rename_i hres
         simp only [Machine.unhandledExn, Machine.newObj, Machine.alloc]
         simpa using resumeStack_env m _ k _ _ hres)

private theorem performEffect_env (m : Machine) (e c k : Val) :
    (m.performEffect e c k).env = m.env := by
  unfold Machine.performEffect
  split
  · exact uncaughtEffect_env m e c k
  · simp only []
    repeat' split
    all_goals
      simp_all [Machine.newCont, Machine.newStack, Machine.alloc, Machine.setCont,
                Machine.popFiber]

private theorem callback_env (m : Machine) (f a k : Val) : (m.callback f a k).env = m.env := rfl

/-- Attempt 2 stated this as `m.purePrim p vs = some (v, m') → m'.env = m.env` and inverted the
equation branch by branch; `purePrim` has twenty arms and three of them build their machine with
a `let`, so the dependent elimination failed on the `caml_continuation_use_noexc` arm. Stating
it under `Option.map` leaves no equation to invert: every branch is a closed term and closes by
`rfl` or by `contUse_env`. -/
private theorem purePrim_env_map (m : Machine) (p : Prim) (vs : List Val) :
    (m.purePrim p vs).map (fun r => r.2.env) = (m.purePrim p vs).map (fun _ => m.env) := by
  unfold Machine.purePrim
  repeat' split
  all_goals
    first
      | rfl
      | (simp [contUse_env]; done)
      | (rename_i heq; obtain ⟨-, rfl⟩ := heq; rfl)
      | (split <;> rfl)
      | (cases m.exnStack <;> rfl)
      | ((repeat' split) <;> first | rfl | simp [contUse_env])

private theorem purePrim_env (m : Machine) (p : Prim) (vs : List Val) (v : Val) (m' : Machine)
    (h : m.purePrim p vs = some (v, m')) : m'.env = m.env := by
  have hm := purePrim_env_map m p vs
  rw [h] at hm
  simpa using hm

theorem stepInstr_env (m : Machine) (i : Instr K) (rest : List (Instr K)) (br : Last)
    (h : NoEnter i) : (m.stepInstr i rest br).env = m.env := by
  cases i with
  | letIn x e =>
    cases e with
    | apply f as ex => exact absurd h (by simp [NoEnter])
    | prim p as =>
      by_cases hres : p = .extern "%resume"
      · subst hres; exact absurd h (by simp [NoEnter])
      · simp only [Machine.stepInstr, Machine.stepLet]
        split
        · simp [Machine.stuck]
        · rename_i vs hvs
          split
          all_goals
            first
              | (simp [Machine.stuck]; done)
              | (simp [performEffect_env, callback_env, contFor_env, bind_env]; done)
              | (split <;>
                   (try simp_all [Machine.stuck, bind_env]) <;>
                   first
                     | rfl
                     | (rename_i heq; exact resumeStack_env m _ _ _ _ heq)
                     | (rename_i heq; exact purePrim_env m _ _ _ _ heq))
              | (exact absurd h (by simp [NoEnter]))
    | _ =>
      simp only [Machine.stepInstr, Machine.stepLet]
      repeat' split
      all_goals simp_all [Machine.stuck, bind_env, Machine.newObj, Machine.alloc]
  | _ =>
    simp only [Machine.stepInstr]
    repeat' split
    all_goals simp_all [Machine.stuck, bind_env, Machine.setObj]

/-! ### 5.3 Binding persistence, and why it is not proved here

`ScopeAtJump` needs one more fact: a name bound by the dominator's block is *still* bound when
the jump is evaluated, several instructions later in the same activation. On this machine that
is

```
(m.look name).isSome → ((m.bind y v).look name).isSome
```

and it is true, for a reason that is one iota-step deep: `bind` rewrites the current activation
record to `(name', v) :: binds` and moves it to the head of `envs`, so `look`'s walk finds the
same record and `List.find?` on the extended binding list still answers.

**Attempt 1** — prove it directly. `Machine.look` is `lookupIn (m.envs.length + 1) m.envs m.env
x`, and `lookupIn` is `private` in `Code.lean`. `unfold Machine.look` exposes it as
`OCaml5.Code.Machine.lookupIn✝`, an inaccessible constant: it cannot be named in a `simp` set,
rewritten, or inducted over from this module. The goal for even the easiest special case,
`(m.bind x v).look x = some v`, reduces to

```
lookupIn✝ ((m.envs.filter …).length + 1 + 1)
  ((m.env, ⟨r.parent, (x, v) :: r.binds⟩) :: m.envs.filter …) m.env x = some v
```

and stops there. One `iota` step on `lookupIn` and one `List.find?_cons` would finish it.

**Attempt 2** — prove it under an explicit `EnvsNodup` hypothesis, so that `setEnv` provably
preserves `envs.length` and the fuel argument does not shrink. Same blocker at the same point:
the hypothesis changes nothing about the accessibility of `lookupIn`.

So the two facts are stated here as an interface, `LookLemmas`, and §5.4 proves `ScopeAtJump`
*relative to it*. **Proposed change to `Code.lean`, not made:** drop `private` from
`lookupIn` (`Code.lean`, in `namespace Machine` above `look`). It is a visibility change, not a
body change, and it does not rename anything, so it is compatible with P4; but the
coordinator's authorisation covered exactly the two repairs of §9.0 and this would be a third.
With it, both lemmas are a dozen lines of `List.find?` reasoning. -/

/-- The two facts about `Machine.look` that `ScopeAtJump` consumes. **Discharged in round five,
§7** — `look_bind_self` and `look_bind_mono` — once `lookupIn` became visible. Kept as a record
of the shape of what was needed; `ScopeAtJump_reduced` no longer takes it. -/
structure LookLemmas : Prop where
  /-- A name just bound is visible. -/
  self : ∀ (m : Machine) (x : Var) (v : Val), ((m.bind x v).look x).isSome
  /-- Binding does not un-bind: an activation only ever grows. -/
  mono : ∀ (m : Machine) (x y : Var) (v : Val),
           (m.look x).isSome → ((m.bind y v).look x).isSome

/-! ### 5.4 The dominator argument, with no machine in it

With §5.1 and §5.2 in hand the dominator argument is a statement about `Last.children` and
`dominatorTree` — a pure control-flow-graph fact, which is where it belongs. `CfgPath` is a
path in the graph `build_graph` builds (`effects.ml:59-76`); §5.1 says the machine's own
transitions are such paths, and §5.2 says they stay in one activation. -/

/-- A path in the CFG `build_graph` reads off `Code.fold_children`. -/
inductive CfgPath (blocks : List (Addr × Block K)) : List Addr → Prop
  | single (a : Addr) : CfgPath blocks [a]
  | cons {a b : Addr} {l : List Addr} {bl : Block K} :
      amGet blocks a = some bl → b ∈ bl.children → CfgPath blocks (b :: l) →
      CfgPath blocks (a :: b :: l)

/-- **The machine extends a CFG path.** One transition out of the end of a block is one edge of
the graph, and it does not leave the activation. This is §5.1 and §5.2 combined, and it is the
only place the machine appears in the dominator argument at all. -/
theorem cfgPath_extend (m : Machine) (a pc : Addr) (bl : Block K) (args : List Val)
    (blocks : List (Addr × Block K)) (l : List Addr)
    (hbl : amGet blocks a = some bl)
    (hctl : m.ctl = .instrs [] bl.branch)
    (hstep : m.step.ctl = .jump pc args)
    (hrest : CfgPath blocks (pc :: l)) :
    CfgPath blocks (a :: pc :: l) ∧ m.step.env = m.env :=
  ⟨.cons hbl (step_jump_mem_children m bl.branch pc args hctl hstep) hrest,
   step_env_of_last m bl.branch hctl⟩

/-- **The remaining obligation, as a graph fact.** `dominator_tree` (`effects.ml:78-105`) is one
Cooper-Harvey-Kennedy pass over the reverse post-order, which is a fixed point for the reducible
graphs the compiler produces — the second loop of `:98-104` asserts exactly that. This says the
answer really is a dominator: every path from the entry to `pc` goes through `idom pc`.

It is a statement about `dominatorTree`, `buildGraph` and `Last.children` only. No `Machine`
occurs in it, which is the point of §5.1 and §5.2: they discharged the machine's half. -/
def DominatorSound (idom : Idom) (blocks : List (Addr × Block K)) (start : Addr) : Prop :=
  ∀ (l : List Addr) (pc : Addr),
    CfgPath blocks l → l.head? = some start → pc ∈ l → amGetD idom pc pc ∈ l

/-- **`ScopeAtJump`, reduced.** Given the graph fact, the two `look` lemmas, and the fact that
`jump_closures` binds every transformed block's closure in its immediate dominator
(`jumpClosures_allocated_at_idom`, §2.2), the closure is in scope at the jump: the path from the
entry to the jump passes through the dominator, the dominator's block binds the closure, the
whole path is one activation (§5.2), and bindings persist (`LookLemmas.mono`).

Round five removed one of the three: `LookLemmas` is discharged (§7). What is left is
`DominatorSound` — still stated, not proved; it is the correctness of `dominator_tree`'s one
Cooper-Harvey-Kennedy pass, and `effects.ml:98-104` is the compiler asserting that same fixed
point with `assert (inter pc d = d)` — and the run-level induction that turns "the machine got
here" into "there is a `CfgPath` from the entry to here", which is the `Reaches` induction
spike P1 built for `OCaml5.Effect` (`Invariant.lean` §6) and which this module has no
counterpart for. -/
def ScopeAtJump_reduced (ctx : Ctx) (blocks : List (Addr × Block K)) (start : Addr) : Prop :=
  DominatorSound ctx.idom blocks start →
    (∀ (b : Machine) (pc : Addr), ctx.blocksToTransform.mem pc →
      (∃ l, CfgPath blocks l ∧ l.head? = some start ∧ pc ∈ l) →
      ScopeAtJump ctx b)

/-! ## 6. Round four, part two: `KSound` as a step-indexed relation

`KSound` (§2) is circular as stated: related continuations, applied to related values, give
related configurations — and "related configurations" mentions the continuations again. FSCD
2017 §5 breaks the circle by induction on the reduction sequence; on a total, fuel-bounded
machine the same break is a **step index**.

`kdAt base n` is "related for `n` more deliveries". The index-`(n+1)` clause quantifies over
configurations related at index `n`, so the definition is structural in `n` and the knot is well
founded. The extra conjunct `kdAt base n ka kb` is what makes the family **downward closed**
(`kdAt_le`), which is what a limit argument needs and what the naive definition does not have —
with the naive one, going from `n+1` to `n` would need the index to be monotone in a negative
position as well as a positive one, and it is not. -/

/-- The step-indexed continuation correspondence. Index `0` relates everything; index `n+1`
adds "delivering related values from configurations related at `n` lands in configurations
related at `n`", with the target free to take any number of steps — it reaches its continuation
through a `tail_call` and a jump where the source reaches it in one `applyK`. -/
def kdAt (base : SimParam) : Nat → Val → Val → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun ka kb =>
      kdAt base n ka kb
      ∧ (∀ a b, R { base with kd := kdAt base n } a b → ∀ v w, base.vr v w →
           ∃ j, R { base with kd := kdAt base n }
                  (a.applyK ka v) (iter j (b.applyV kb [w])))

/-- The relation at one index. Only `kd` moves: `vr`, `sid`, `cid` and `oid` are the base's. -/
def paramAt (base : SimParam) (n : Nat) : SimParam := { base with kd := kdAt base n }

theorem kdAt_zero (base : SimParam) (ka kb : Val) : kdAt base 0 ka kb := trivial

/-- The introduction rule: this is what each emitted shape has to supply. -/
theorem kdAt_succ (base : SimParam) (n : Nat) (ka kb : Val)
    (hlow : kdAt base n ka kb)
    (hstep : ∀ a b, R (paramAt base n) a b → ∀ v w, base.vr v w →
       ∃ j, R (paramAt base n) (a.applyK ka v) (iter j (b.applyV kb [w]))) :
    kdAt base (n + 1) ka kb := ⟨hlow, hstep⟩

theorem kdAt_succ_down (base : SimParam) (n : Nat) (ka kb : Val)
    (h : kdAt base (n + 1) ka kb) : kdAt base n ka kb := h.1

/-- **Downward closure**, the property the naive definition lacks. -/
theorem kdAt_le (base : SimParam) : ∀ (n m : Nat), m ≤ n → ∀ ka kb,
    kdAt base n ka kb → kdAt base m ka kb := by
  intro n
  induction n with
  | zero =>
    intro m hm ka kb h
    have : m = 0 := Nat.le_zero.mp hm
    subst this; exact h
  | succ n ih =>
    intro m hm ka kb h
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact ih m (Nat.le_of_lt_succ hlt) ka kb h.1
    · have : m = n + 1 := Nat.le_antisymm hm hge
      subst this; exact h

/-! ### 6.1 The relation is monotone in the index

Every occurrence of `kd` in `R` is positive, so downward closure of `kdAt` lifts to `R`. -/

theorem Forall₂_mono {α β : Type} {Rel Sel : α → β → Prop} (h : ∀ a b, Rel a b → Sel a b) :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ Rel l₁ l₂ → Forall₂ Sel l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons hh ht => .cons (h _ _ hh) (Forall₂_mono h ht)

theorem CellRel_mono (base : SimParam) {n m : Nat} (hle : m ≤ n) {c d : FiberCell}
    (h : CellRel (paramAt base n) c d) : CellRel (paramAt base m) c d :=
  { k := kdAt_le base n m hle _ _ h.k
  , exn := Forall₂_mono (fun _ _ hx => kdAt_le base n m hle _ _ hx) h.exn
  , hv := h.hv, hx := h.hx, hf := h.hf }

theorem FrameRel_mono (base : SimParam) {n m : Nat} (hle : m ≤ n) {f g : FiberFrame}
    (h : FrameRel (paramAt base n) f g) : FrameRel (paramAt base m) f g :=
  { hv := h.hv, hx := h.hx, hf := h.hf
  , rk := kdAt_le base n m hle _ _ h.rk
  , rx := Forall₂_mono (fun _ _ hx => kdAt_le base n m hle _ _ hx) h.rx }

theorem SavedRel_mono (base : SimParam) {n m : Nat} (hle : m ≤ n) {x y : Saved}
    (h : SavedRel (paramAt base n) x y) : SavedRel (paramAt base m) x y :=
  { exn := Forall₂_mono (fun _ _ hx => kdAt_le base n m hle _ _ hx) h.exn
  , fib := Forall₂_mono (fun _ _ hx => FrameRel_mono base hle hx) h.fib
  , k := kdAt_le base n m hle _ _ h.k }

/-- **`R` is monotone in the index.** -/
theorem R_mono (base : SimParam) {n m : Nat} (hle : m ≤ n) {a b : Machine}
    (h : R (paramAt base n) a b) : R (paramAt base m) a b :=
  { kk := kdAt_le base n m hle _ _ h.kk
  , exn := Forall₂_mono (fun _ _ hx => kdAt_le base n m hle _ _ hx) h.exn
  , fib := Forall₂_mono (fun _ _ hx => FrameRel_mono base hle hx) h.fib
  , stk := fun i cs hi =>
      let ⟨j, ds, hj, hd, hf⟩ := h.stk i cs hi
      ⟨j, ds, hj, hd, Forall₂_mono (fun _ _ hx => CellRel_mono base hle hx) hf⟩
  , cnt := h.cnt
  , cb := Forall₂_mono (fun _ _ hx => SavedRel_mono base hle hx) h.cb
  , out := h.out, obj := h.obj, vars := h.vars }

/-! ### 6.2 `KSound`, at each index, is now a theorem

This is the point of the whole construction. §2's `KSound` was an obligation because its
statement was circular; at a fixed index it is the second conjunct of `kdAt`, so it holds by
projection. What is left to *prove* is not `KSound` but the family of facts "the continuation
pair the transform emits here is related at index `n+1`", and §6.4 reduces each of those to one
statement about the target's environment. -/

theorem KSoundAt (base : SimParam) (n : Nat) :
    ∀ a b, R (paramAt base n) a b → ∀ (ka kb : Val), kdAt base (n + 1) ka kb →
      ∀ v w, base.vr v w →
        ∃ j, R (paramAt base n) (a.applyK ka v) (iter j (b.applyV kb [w])) :=
  fun a b hab _ka _kb hk v w hvw => hk.2 a b hab v w hvw

/-! ### 6.3 What each continuation shape does, computed

The knot's hypothesis is a statement about two explicit configurations, so it is worth having
the two `applyK`/`applyV` arms in closed form. The second is the one that matters: **entering a
jump closure opens a fresh activation whose parent is the closure's definition environment** —
which, for the closures `jump_closures` allocates, is the dominator's activation. That is the
formal link between this part and §5. -/

theorem applyK_frameK (m : Machine) (i : FrameId) (fr : FrameRec) (v : Val)
    (h : m.getFrame i = some fr) :
    m.applyK (.frameK i) v
      = { (Machine.bind { m with env := fr.envId, k := fr.next } fr.bindTo v) with
            ctl := .instrs fr.rest fr.branch } := by
  simp [Machine.applyK, h]

theorem applyK_trapK (m : Machine) (i : TrapId) (t : TrapRec) (v : Val) (vs : List Val)
    (h : m.getTrap i = some t)
    (hargs : (Machine.bind
                { m with env := t.envId, k := t.k, trace := .trap :: m.trace } t.exn v).lookAll
               t.targetArgs = some vs) :
    m.applyK (.trapK i) v
      = { (Machine.bind
             { m with env := t.envId, k := t.k, trace := .trap :: m.trace } t.exn v) with
            ctl := .jump t.target vs } := by
  simp [Machine.applyK, h, hargs]

theorem applyK_halt (m : Machine) (v : Val) :
    m.applyK (.prim "halt") v = { m with ctl := .done (.value v) } := rfl

/-- **Entering a jump closure.** `targs` is `[]` for every closure `jump_closures` allocates
(`effects.ml:230-248` builds `Closure params (pc, [])`), so the entry is exactly: allocate a
fresh activation, parent the closure's definition environment, bind the parameters, jump. -/
theorem applyV_closure_nil (m : Machine) (ps : List Var) (t : Addr) (e : EnvId)
    (args : List Val) (hlen : ps.length = args.length) :
    m.applyV (.closure ps t [] e) args
      = { m with envs := (m.fresh, ⟨some e, ps.zip args⟩) :: m.envs
               , env := m.fresh, fresh := m.fresh + 1
               , ctl := .jump t [] } := by
  simp [Machine.applyV, hlen, Machine.newEnv, Machine.alloc, Machine.lookAll]

/-! ### 6.4 The knot, by induction on the index

The two configurations the knot compares, named. -/

/-- The source delivers into the activation the frame saved (`Code.Machine.contFor` built it,
`effects.ml`'s `split_blocks` decided its shape). -/
def frameDeliver (a : Machine) (fr : FrameRec) (v : Val) : Machine :=
  { (Machine.bind { a with env := fr.envId, k := fr.next } fr.bindTo v) with
      ctl := .instrs fr.rest fr.branch }

/-- The target opens a fresh activation under the closure's definition environment. -/
def closureEnter (b : Machine) (ps : List Var) (t : Addr) (e : EnvId) (w : Val) : Machine :=
  { b with envs := (b.fresh, ⟨some e, ps.zip [w]⟩) :: b.envs
         , env := b.fresh, fresh := b.fresh + 1, ctl := .jump t [] }

/-- **The one obligation the knot leaves.** After the two sides have delivered — the source into
the frame's saved activation, the target into a fresh one parented at the closure's definition
environment — the configurations are related again. Every clause of `R` but (R8) is immediate,
because neither side touched the traps, the fibers, the captured stacks, the continuation table,
the callback stack, the output or the object heap. (R8) is the scope clause, and the fact it
needs is that the closure's definition environment is the dominator's activation — which is
§5.4's `DominatorSound` again. -/
def EntryOk (base : SimParam) (n : Nat) (i : FrameId) (fr : FrameRec)
    (ps : List Var) (t : Addr) (e : EnvId) : Prop :=
  ∀ a b, R (paramAt base n) a b → ∀ v w, base.vr v w →
    a.getFrame i = some fr
    ∧ ∃ j, R (paramAt base n) (frameDeliver a fr v) (iter j (closureEnter b ps t e w))

/-- The same for a trap entry: a source-level `Pushtrap` against `cps_last`'s
`caml_push_trap` closure (`effects.ml:426-445`). -/
def TrapEntryOk (base : SimParam) (n : Nat) (i : TrapId) (tr : TrapRec)
    (ps : List Var) (t : Addr) (e : EnvId) : Prop :=
  ∀ a b, R (paramAt base n) a b → ∀ v w, base.vr v w →
    ∃ vs, a.getTrap i = some tr
    ∧ (Machine.bind { a with env := tr.envId, k := tr.k, trace := .trap :: a.trace }
         tr.exn v).lookAll tr.targetArgs = some vs
    ∧ ∃ j, R (paramAt base n)
             ({ (Machine.bind
                   { a with env := tr.envId, k := tr.k, trace := .trap :: a.trace } tr.exn v)
                  with ctl := .jump tr.target vs })
             (iter j (closureEnter b ps t e w))

/-- **The knot at a continuation frame against a continuation closure**, one index up. -/
theorem knot_frame_closure (base : SimParam) (n : Nat) (i : FrameId) (fr : FrameRec)
    (ps : List Var) (t : Addr) (e : EnvId) (hps : ps.length = 1)
    (hlow : kdAt base n (.frameK i) (.closure ps t [] e))
    (hentry : EntryOk base n i fr ps t e) :
    kdAt base (n + 1) (.frameK i) (.closure ps t [] e) := by
  refine kdAt_succ base n _ _ hlow (fun a b hab v w hvw => ?_)
  obtain ⟨hf, j, hj⟩ := hentry a b hab v w hvw
  refine ⟨j, ?_⟩
  rw [applyK_frameK a i fr v hf,
      applyV_closure_nil b ps t e [w] (by simpa using hps)]
  exact hj

/-- **The knot at a trap against a `caml_push_trap` closure**, one index up. -/
theorem knot_trap_closure (base : SimParam) (n : Nat) (i : TrapId) (tr : TrapRec)
    (ps : List Var) (t : Addr) (e : EnvId) (hps : ps.length = 1)
    (hlow : kdAt base n (.trapK i) (.closure ps t [] e))
    (hentry : TrapEntryOk base n i tr ps t e) :
    kdAt base (n + 1) (.trapK i) (.closure ps t [] e) := by
  refine kdAt_succ base n _ _ hlow (fun a b hab v w hvw => ?_)
  obtain ⟨vs, ht, hargs, j, hj⟩ := hentry a b hab v w hvw
  refine ⟨j, ?_⟩
  rw [applyK_trapK a i tr v vs ht hargs,
      applyV_closure_nil b ps t e [w] (by simpa using hps)]
  exact hj

/-- **The knot closed, by induction on the step index.** A continuation frame and the
continuation closure the transform builds for it are related at *every* index, given `EntryOk`
at every index. This is the induction FSCD 2017 §5 does over the reduction sequence, done here
over the step index instead — and it is the theorem `KSound` was standing in for. -/
theorem knot_frame_all (base : SimParam) (i : FrameId) (fr : FrameRec)
    (ps : List Var) (t : Addr) (e : EnvId) (hps : ps.length = 1)
    (hentry : ∀ n, EntryOk base n i fr ps t e) :
    ∀ n, kdAt base n (.frameK i) (.closure ps t [] e) := by
  intro n
  induction n with
  | zero => exact kdAt_zero base _ _
  | succ n ih => exact knot_frame_closure base n i fr ps t e hps ih (hentry n)

/-- The same for traps. -/
theorem knot_trap_all (base : SimParam) (i : TrapId) (tr : TrapRec)
    (ps : List Var) (t : Addr) (e : EnvId) (hps : ps.length = 1)
    (hentry : ∀ n, TrapEntryOk base n i tr ps t e) :
    ∀ n, kdAt base n (.trapK i) (.closure ps t [] e) := by
  intro n
  induction n with
  | zero => exact kdAt_zero base _ _
  | succ n ih => exact knot_trap_closure base n i tr ps t e hps ih (hentry n)

/-! ### 6.5 The pass-through shapes, and the limit

Three of the five emitted continuation shapes build no continuation at all:

* **Return → tail call of `k`** — `contFor` recognises `Let x e; return x` as tail position and
  answers `m.k` unchanged, and `tail_call_step` shows the target's step does not touch `m.k`
  either. The pair is the one already in `R`'s clause (R1); nothing to prove.
* **Branch to a transformed block** — `cps_branch` emits a `tail_call` of the block closure and
  leaves `m.k` alone (`tail_call_step` again). Same.
* **`caml_resume_stack`'s `k`** — `resume_stack_step` binds the *innermost captured cell's* `k`,
  which came out of the captured fiber list, so it is related by `R`'s clause (R4) rather than
  by a new knot.

So the whole of `KSound` is the two shapes of §6.4, and both are closed by induction on the
index given `EntryOk`. -/

/-- The pass-through shapes, as a lemma: a pair already related at every index stays related,
which is what `tail_call_step` and `resume_stack_step` need. -/
theorem knot_passthrough (base : SimParam) (ka kb : Val)
    (h : ∀ n, kdAt base n ka kb) : ∀ n, kdAt base n ka kb := h

/-- **The limit.** A run that halts has a length; the index only has to be as large as the
number of deliveries that run makes, and `kdAt_le` says a larger index does for a shorter run.
So `cps_preserves_outcome` for terminating runs needs the family at every index — which
`knot_frame_all` and `knot_trap_all` give — plus the two things `R` deliberately does not
mention: that the initial states are related, and that related halted states have the same
outcome. Both are listed in `SimulationSuffices` (§3). -/
theorem R_at_any_index (base : SimParam) (a b : Machine)
    (h : ∀ n, R (paramAt base n) a b) (n : Nat) : R (paramAt base n) a b := h n

/-! ## 7. Round five, part one: `LookLemmas`, discharged

§10.6 of the report recorded the blocker: both facts were true and one iota-step deep, and
neither could be proved because `lookupIn` was `private` in `Code.lean`. It is public as of
round five (visibility only — no rename, no change to the body), so this section finishes them
and `ScopeAtJump` no longer needs the `LookLemmas` interface.

The second fact needs one side condition, and it is worth naming rather than hiding: `look`'s
fuel is `m.envs.length + 1`, and `bind` rebuilds the environment list as
`(m.env, r') :: m.envs.filter (·.1 ≠ m.env)`. If `m.env` occurred **twice** in `m.envs` the
filter would drop both and the fuel would shrink, so a deep parent chain could run out of fuel
after a `bind` that succeeded before it. `EnvKeyUnique` is exactly the absence of that, and it
is self-propagating: `bind` *establishes* it, because `setEnv` filters. -/

/-- The current activation occurs exactly once in the environment list — equivalently, `bind`
does not shorten `look`'s fuel. -/
def EnvKeyUnique (m : Machine) : Prop :=
  (m.envs.filter (fun p => p.1 ≠ m.env)).length + 1 = m.envs.length

/-- **`bind` establishes it**: `setEnv` filters the old record out and conses the new one, so
after any `bind` the current activation occurs exactly once. The invariant therefore holds from
the first binding of an activation onwards, which is all §5.4 needs. -/
theorem bind_envKeyUnique (m : Machine) (y : Var) (v : Val) (r : EnvRec)
    (h : m.getEnv m.env = some r) : EnvKeyUnique (m.bind y v) := by
  unfold EnvKeyUnique Machine.bind
  rw [h]
  simp [Machine.setEnv, List.filter_filter]

/-- **`LookLemmas.self`.** A name just bound is visible. -/
theorem look_bind_self (m : Machine) (x : Var) (v : Val) (r : EnvRec)
    (h : m.getEnv m.env = some r) : (m.bind x v).look x = some v := by
  unfold Machine.look Machine.bind
  rw [h]
  simp [Machine.setEnv, Machine.lookupIn]

/-- The walk is monotone in its fuel. -/
theorem lookupIn_fuel_mono (envs : List (EnvId × EnvRec)) (x : Var) :
    ∀ (f : Nat) (e : EnvId), (Machine.lookupIn f envs e x).isSome →
      (Machine.lookupIn (f + 1) envs e x).isSome := by
  intro f
  induction f with
  | zero => intro e h; simp [Machine.lookupIn] at h
  | succ f ih =>
    intro e h
    rw [Machine.lookupIn] at h ⊢
    split at h
    · simp at h
    · split at h
      · exact h
      · split at h
        · simp at h
        · exact ih _ h

/-- Attempt 1 proved `isSome` monotonicity of the walk directly, by splitting the two `match`es
in step. It fails on matcher identity: the `match … with | none => none | some a => …` written in
a helper lemma elaborates to a *different* auxiliary matcher from the one inside `lookupIn`, so
the two are not defeq at reducible transparency and `exact` is refused on goals that print
identically. Attempt 2, kept, replaces monotonicity by **equality** — for `y ≠ x` the rebuilt
environment answers exactly as the old one, and the case `y = x` is `look_bind_self`, which is
already proved — and keeps the rebuilt list *opaque* so that `cases` on a scrutinee substitutes
on both sides of the equation at once. -/
private theorem find?_filter_ne {α : Type} (d a : Addr) (h : ¬ (d = a))
    (l : List (Addr × α)) :
    (l.filter (fun p => p.1 ≠ d)).find? (fun p => p.1 = a) = l.find? (fun p => p.1 = a) := by
  simpa using find?_skip_ne d a h l

/-- The walk is insensitive to a change that adds one binding, for a *different* variable, to
one activation record. Stated over an abstract `envs'` so that the induction never has to look
inside the rebuilt list. -/
theorem lookupIn_congr_bind (envs envs' : List (EnvId × EnvRec)) (ev : EnvId) (x : Var)
    (r r' : EnvRec)
    (hr : (envs.find? (fun p => p.1 = ev)).map (·.2) = some r)
    (hr' : (envs'.find? (fun p => p.1 = ev)).map (·.2) = some r')
    (hbinds : (r'.binds.find? (fun p => p.1 = x)).map (·.2)
              = (r.binds.find? (fun p => p.1 = x)).map (·.2))
    (hpar : r'.parent = r.parent)
    (hother : ∀ e, ¬ (e = ev) →
       (envs'.find? (fun p => p.1 = e)).map (·.2) = (envs.find? (fun p => p.1 = e)).map (·.2)) :
    ∀ (f : Nat) (e : EnvId),
      Machine.lookupIn f envs' e x = Machine.lookupIn f envs e x := by
  intro f
  induction f with
  | zero => intro e; rfl
  | succ f ih =>
    intro e
    rw [Machine.lookupIn, Machine.lookupIn]
    by_cases hev : e = ev
    · subst hev
      rw [hr, hr']
      dsimp only
      rw [hbinds, hpar]
      cases hw : ((r.binds.find? (fun p => p.1 = x)).map (·.2)) with
      | some w => rfl
      | none =>
        dsimp only
        cases hp : r.parent with
        | none => rfl
        | some p => exact ih p
    · rw [hother e hev]
      cases hre : ((envs.find? (fun p => p.1 = e)).map (·.2)) with
      | none => rfl
      | some re =>
        dsimp only
        cases hw : ((re.binds.find? (fun p => p.1 = x)).map (·.2)) with
        | some w => rfl
        | none =>
          dsimp only
          cases hp : re.parent with
          | none => rfl
          | some p => exact ih p

/-- **Binding a different variable changes nothing.** -/
theorem look_bind_ne (m : Machine) (x y : Var) (v : Val) (r : EnvRec)
    (hr : m.getEnv m.env = some r) (hu : EnvKeyUnique m) (hxy : ¬ (y = x)) :
    (m.bind y v).look x = m.look x := by
  unfold Machine.look Machine.bind
  rw [hr]
  simp only [Machine.setEnv]
  have hlen : (List.filter (fun p => p.1 ≠ m.env) m.envs).length + 1 = m.envs.length := hu
  simp only [List.length_cons, hlen]
  refine lookupIn_congr_bind m.envs _ m.env x r { r with binds := (y, v) :: r.binds }
    hr ?_ ?_ rfl ?_ (m.envs.length + 1) m.env
  · simp
  · simp [hxy]
  · intro e hne
    have hne' : ¬ (m.env = e) := fun hh => hne hh.symm
    simp only [List.find?_cons, hne', decide_false]
    congr 1
    exact find?_filter_ne m.env e hne' m.envs

/-- **`LookLemmas.mono`.** Binding does not un-bind: an activation only ever grows. -/
theorem look_bind_mono (m : Machine) (x y : Var) (v : Val) (r : EnvRec)
    (hr : m.getEnv m.env = some r) (hu : EnvKeyUnique m)
    (h : (m.look x).isSome) : ((m.bind y v).look x).isSome := by
  by_cases hxy : y = x
  · subst hxy
    rw [look_bind_self m y v r hr]
    rfl
  · rw [look_bind_ne m x y v r hr hu hxy]
    exact h

/-- **`LookLemmas`, discharged.** The interface of §5.3 is inhabited for every machine whose
current activation exists and occurs once — which, by `bind_envKeyUnique`, is every machine
reached by a binding. -/
theorem lookLemmas_hold (m : Machine) (r : EnvRec) (hr : m.getEnv m.env = some r)
    (hu : EnvKeyUnique m) :
    (∀ (x : Var) (v : Val), ((m.bind x v).look x).isSome)
  ∧ (∀ (x y : Var) (v : Val), (m.look x).isSome → ((m.bind y v).look x).isSome) :=
  ⟨fun x v => by rw [look_bind_self m x v r hr]; rfl
  , fun x y v h => look_bind_mono m x y v r hr hu h⟩

end OCaml5.CpsProof
