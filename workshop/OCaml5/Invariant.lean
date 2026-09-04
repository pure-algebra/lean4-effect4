import OCaml5.Effect
import OCaml5.Compiler

/-!
# OCaml 5 spike: the run-level invariant and the induction principle

Status: spike P1, 2026-09-03. Module `OCaml5.Invariant` of the non-default `OCaml5` library
(`lakefile.toml`, `srcDir = "workshop"`). Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6 row P1. Report:
`docs/research/2026-09-03-spike-p1-invariant.md`.

Predecessors: `OCaml5.Effect` (spike O1: the machine, the eight transitions, the heap-lemma
toolkit) and `OCaml5.Compiler` (spike O5: the `bytegen.ml:796-804` admission clause). Both are
imported read-only; nothing in either file is changed by this module.

This module supplies the one piece of infrastructure the O1 report §5 names as the common
blocker of every theorem it could not close:

* `Machine.WF`, a well-formedness invariant on the whole machine state — `current` is live,
  every parent pointer is live, the parent relation is acyclic, every live continuation names a
  live stack, the running stack has no children, and the parent relation is injective;
* `Machine.step_wf`, its preservation by `step`, arm by arm, under the discipline predicate
  `Machine.Safe` (§4 below: exactly the facts about a primitive's *arguments* that OCaml's type
  system and the runtime's own calling discipline guarantee and the term language cannot);
* `Machine.Reaches` and `Machine.reaches_induction` / `Machine.run_reaches`, the induction
  principle over `run`.

and then discharges, with them, the theorems O1 §5 and O5 §9 left stated but unproved.

## The layout

| § | Contents |
| --- | --- |
| 1 | list and arithmetic lemmas: a `Nodup` list of naturals below `L` is no longer than `L` |
| 2 | the parent chain: `chainList`, `Grounded`, `depth`, and the two directions between a rank and a grounding bound |
| 3 | `WF`, and `outermost_terminates` |
| 4 | `Safe`, the runtime's calling discipline as a side condition |
| 5 | preservation: the heap toolkit extended, `SameHeap`, and the arm lemmas up to `step_wf` |
| 6 | `Reaches`, its induction principle, and `run` |
| 7 | the behavioural theorems: traps survive capture, the `reperform` root route, the `Stdlib` corollaries |
| 8 | `admissibleAt` monotonicity (O5 §9 item 1) |

Constraints, from the plan and the spike brief: Lean 4.33.1, no Mathlib, no `sorry`, no `axiom`,
no `partial`, no `unsafe`, no `native_decide`, no `implemented_by`, and no `Classical.choice` —
every `#print axioms` in the report shows `propext` and `Quot.sound` only, so every case split in
this file is on a decidable proposition.
-/


namespace OCaml5

universe u

/-! ## 1. Counting

One arithmetic fact is needed and it is the only place a "there are only `stacks.length` slots"
argument appears: a duplicate-free list of naturals, each below `L`, has at most `L` entries.
Lean 4.33's core has `List.Nodup`, `List.Pairwise.filter` and `List.filter_eq_self`, and nothing
else that is needed here, so the two steps are spelled out. -/

namespace Counting

/-- Removing every occurrence of one value from a duplicate-free list shortens it by at most
one, because there is at most one occurrence. -/
theorem length_le_filter_succ (a : Nat) :
    ∀ l : List Nat, l.Nodup → l.length ≤ (l.filter (fun x => x != a)).length + 1
  | [], _ => by simp
  | x :: t, h => by
    have ht : t.Nodup := (List.nodup_cons.mp h).2
    have hx : x ∉ t := (List.nodup_cons.mp h).1
    by_cases hxa : x = a
    · subst hxa
      have hself : t.filter (fun y => y != x) = t := by
        refine List.filter_eq_self.mpr ?_
        intro b hb
        have : b ≠ x := by
          intro hbx; exact hx (hbx ▸ hb)
        simpa using this
      simp [hself]
    · have hne : (x != a) = true := by simpa using hxa
      have ih := length_le_filter_succ a t ht
      simp only [List.filter_cons, hne, if_true, List.length_cons]
      omega

/-- A duplicate-free list of naturals all below `L` has at most `L` entries. -/
theorem length_le_of_nodup_lt :
    ∀ (L : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < L) → l.length ≤ L
  | 0, [], _, _ => by simp
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (Nat.not_lt_zero x)
  | L + 1, l, hnd, hlt => by
    have hnd' : (l.filter (fun x => x != L)).Nodup := List.Pairwise.filter _ hnd
    have hlt' : ∀ x ∈ l.filter (fun x => x != L), x < L := by
      intro x hx
      have hx' := List.mem_filter.mp hx
      have hne : x ≠ L := by simpa using hx'.2
      have := hlt x hx'.1
      omega
    have ih := length_le_of_nodup_lt L _ hnd' hlt'
    have := length_le_filter_succ L l hnd
    omega

end Counting

namespace Machine

variable {ν : Type u}

/-! ## 2. The parent chain

`Machine.outermost` (`fiber.c:644`, `interp.c:1295`, `amd64.S:935-940`) walks parent pointers
under a fuel bound. This section says when that walk is the real thing.

`Grounded m n s` is "the walk from `s` reaches a live parentless stack within `n` steps".
`chainList m n s` is the list of stacks it visits, which the counting argument of §1 measures.
`depth` is the walk's length, which is the canonical rank of the parent relation. -/

/-- The walk from `s` reaches a live stack with no parent within `n` steps: `outermost` with
that fuel has already arrived. -/
def Grounded (m : Machine ν) (n : Nat) (s : StackId) : Prop :=
  ∃ info, m.stack? (m.outermost n s) = Option.some info ∧ info.handler.parent = Option.none

/-- `Grounded` is decidable, so the counting argument below can be run by contradiction
without `Classical.choice`. -/
instance instDecidableGrounded (m : Machine ν) (n : Nat) (s : StackId) :
    Decidable (m.Grounded n s) :=
  match h : m.stack? (m.outermost n s) with
  | Option.none => isFalse (by rintro ⟨info, hi, -⟩; rw [h] at hi; simp at hi)
  | Option.some info =>
    if hp : info.handler.parent = Option.none then
      isTrue ⟨info, h, hp⟩
    else
      isFalse (by rintro ⟨info', hi, hp'⟩; rw [h] at hi; cases hi; exact hp hp')

/-- A dead stack grounds nothing: `outermost` stops there and the slot is empty. -/
theorem not_grounded_of_dead {m : Machine ν} {s : StackId} (h : m.stack? s = Option.none) :
    ∀ n, ¬ m.Grounded n s := by
  intro n
  have hout : m.outermost n s = s := by
    cases n with
    | zero => rfl
    | succ k => simp [outermost, h]
  rintro ⟨info, hi, -⟩
  rw [hout, h] at hi
  simp at hi

/-- A live parentless stack is its own outermost, at any fuel. -/
theorem grounded_of_parent_none {m : Machine ν} {s : StackId} {info : StackInfo ν}
    (h : m.stack? s = Option.some info) (hp : info.handler.parent = Option.none) :
    ∀ n, m.Grounded n s := by
  intro n
  have hout : m.outermost n s = s := by
    cases n with
    | zero => rfl
    | succ k => simp [outermost, h, hp]
  exact ⟨info, by rw [hout]; exact h, hp⟩

/-- One step of the walk: with a parent, grounding at `n+1` is grounding of the parent at `n`. -/
theorem grounded_succ_iff {m : Machine ν} {s p : StackId} {info : StackInfo ν}
    (h : m.stack? s = Option.some info) (hp : info.handler.parent = Option.some p) (n : Nat) :
    m.Grounded (n + 1) s ↔ m.Grounded n p := by
  unfold Grounded
  have : m.outermost (n + 1) s = m.outermost n p := by simp [outermost, h, hp]
  rw [this]

/-- More fuel never un-grounds a walk. -/
theorem grounded_mono {m : Machine ν} : ∀ (n : Nat) (s : StackId), m.Grounded n s →
    m.Grounded (n + 1) s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rcases hs with ⟨info, hi, hp⟩
    have hout : m.outermost 0 s = s := rfl
    rw [hout] at hi
    exact grounded_of_parent_none hi hp 1
  | succ k ih =>
    intro s hs
    cases hst : m.stack? s with
    | none => exact absurd hs (not_grounded_of_dead hst _)
    | some info =>
      cases hp : info.handler.parent with
      | none => exact grounded_of_parent_none hst hp _
      | some p =>
        rw [grounded_succ_iff hst hp] at hs ⊢
        exact ih p hs

theorem grounded_le {m : Machine ν} {n k : Nat} {s : StackId} (h : m.Grounded n s) (hle : n ≤ k) :
    m.Grounded k s := by
  induction k with
  | zero =>
    have hz : n = 0 := Nat.le_zero.mp hle
    exact hz ▸ h
  | succ j ih =>
    rcases Nat.lt_or_ge n (j + 1) with hlt | hge
    · exact grounded_mono j s (ih (by omega))
    · have : n = j + 1 := by omega
      exact this ▸ h

/-- The stacks the walk visits, `s` first. -/
def chainList (m : Machine ν) : Nat → StackId → List StackId
  | 0, s => [s]
  | n + 1, s =>
    s :: (match m.stack? s with
      | Option.none => []
      | Option.some info =>
        match info.handler.parent with
        | Option.none => []
        | Option.some p => m.chainList n p)

theorem chainList_succ_parent {m : Machine ν} {s p : StackId} {info : StackInfo ν}
    (h : m.stack? s = Option.some info) (hp : info.handler.parent = Option.some p) (n : Nat) :
    m.chainList (n + 1) s = s :: m.chainList n p := by
  simp [chainList, h, hp]

/-- If the walk has *not* grounded after `n` steps then it visited `n+1` stacks: it never met a
dead slot and never met a parentless one. -/
theorem chainList_length_of_not_grounded {m : Machine ν}
    (hpl : ∀ s p, m.parentOf s = Option.some p → (m.stack? p).isSome) :
    ∀ (n : Nat) (s : StackId), (m.stack? s).isSome → ¬ m.Grounded n s →
      (m.chainList n s).length = n + 1 := by
  intro n
  induction n with
  | zero => intro s _ _; simp [chainList]
  | succ k ih =>
    intro s hlive hng
    cases hst : m.stack? s with
    | none => rw [hst] at hlive; exact absurd hlive (by simp)
    | some info =>
      cases hp : info.handler.parent with
      | none => exact absurd (grounded_of_parent_none hst hp _) hng
      | some p =>
        have hpar : m.parentOf s = Option.some p := by
          unfold parentOf handlerOf; rw [hst]; exact hp
        have hplive := hpl s p hpar
        rw [grounded_succ_iff hst hp] at hng
        rw [chainList_succ_parent hst hp, List.length_cons, ih p hplive hng]

/-- Every stack the walk visits is live. -/
theorem chainList_live {m : Machine ν}
    (hpl : ∀ s p, m.parentOf s = Option.some p → (m.stack? p).isSome) :
    ∀ (n : Nat) (s : StackId), (m.stack? s).isSome →
      ∀ x ∈ m.chainList n s, (m.stack? x).isSome := by
  intro n
  induction n with
  | zero => intro s hlive x hx; simp [chainList] at hx; exact hx ▸ hlive
  | succ k ih =>
    intro s hlive x hx
    cases hst : m.stack? s with
    | none => rw [hst] at hlive; exact absurd hlive (by simp)
    | some info =>
      cases hp : info.handler.parent with
      | none =>
        rw [show m.chainList (k + 1) s = [s] by simp [chainList, hst, hp]] at hx
        simp at hx; exact hx ▸ hlive
      | some p =>
        rw [chainList_succ_parent hst hp] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hlive
        · have hpar : m.parentOf s = Option.some p := by
            unfold parentOf handlerOf; rw [hst]; exact hp
          exact ih p (hpl s p hpar) x hx'

/-- Along the walk the rank never rises. -/
theorem chainList_rank_le {m : Machine ν} {r : StackId → Nat}
    (hdec : ∀ s p, m.parentOf s = Option.some p → r p < r s) :
    ∀ (n : Nat) (s : StackId), ∀ x ∈ m.chainList n s, r x ≤ r s := by
  intro n
  induction n with
  | zero => intro s x hx; simp [chainList] at hx; exact hx ▸ Nat.le_refl _
  | succ k ih =>
    intro s x hx
    cases hst : m.stack? s with
    | none =>
      rw [show m.chainList (k + 1) s = [s] by simp [chainList, hst]] at hx
      simp at hx; exact hx ▸ Nat.le_refl _
    | some info =>
      cases hp : info.handler.parent with
      | none =>
        rw [show m.chainList (k + 1) s = [s] by simp [chainList, hst, hp]] at hx
        simp at hx; exact hx ▸ Nat.le_refl _
      | some p =>
        rw [chainList_succ_parent hst hp] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.le_refl _
        · have hpar : m.parentOf s = Option.some p := by
            unfold parentOf handlerOf; rw [hst]; exact hp
          exact Nat.le_trans (ih p x hx') (Nat.le_of_lt (hdec s p hpar))

/-- **The chain has no cycle**: a strictly decreasing rank makes the visited stacks pairwise
distinct. -/
theorem chainList_nodup {m : Machine ν} {r : StackId → Nat}
    (hdec : ∀ s p, m.parentOf s = Option.some p → r p < r s) :
    ∀ (n : Nat) (s : StackId), (m.chainList n s).Nodup := by
  intro n
  induction n with
  | zero => intro s; simp [chainList]
  | succ k ih =>
    intro s
    cases hst : m.stack? s with
    | none => rw [show m.chainList (k + 1) s = [s] by simp [chainList, hst]]; simp
    | some info =>
      cases hp : info.handler.parent with
      | none => rw [show m.chainList (k + 1) s = [s] by simp [chainList, hst, hp]]; simp
      | some p =>
        have hpar : m.parentOf s = Option.some p := by
          unfold parentOf handlerOf; rw [hst]; exact hp
        rw [chainList_succ_parent hst hp]
        refine List.nodup_cons.mpr ⟨?_, ih p⟩
        intro hmem
        have := chainList_rank_le hdec k p s hmem
        have := hdec s p hpar
        omega

/-- The walk's length, the canonical rank of the parent relation. -/
def depth (m : Machine ν) : Nat → StackId → Nat
  | 0, _ => 0
  | n + 1, s =>
    match m.stack? s with
    | Option.none => 0
    | Option.some info =>
      match info.handler.parent with
      | Option.none => 0
      | Option.some p => m.depth n p + 1

theorem depth_succ_parent {m : Machine ν} {s p : StackId} {info : StackInfo ν}
    (h : m.stack? s = Option.some info) (hp : info.handler.parent = Option.some p) (n : Nat) :
    m.depth (n + 1) s = m.depth n p + 1 := by
  simp [depth, h, hp]

/-- Past the grounding fuel the walk's length stops changing. -/
theorem depth_stable {m : Machine ν} :
    ∀ (n : Nat) (s : StackId), m.Grounded n s → ∀ k, m.depth (n + k) s = m.depth n s := by
  intro n
  induction n with
  | zero =>
    intro s hs k
    rcases hs with ⟨info, hi, hp⟩
    have hi' : m.stack? s = Option.some info := hi
    cases k with
    | zero => rfl
    | succ j => simp [depth, hi', hp]
  | succ i ih =>
    intro s hs k
    cases hst : m.stack? s with
    | none => exact absurd hs (not_grounded_of_dead hst _)
    | some info =>
      cases hp : info.handler.parent with
      | none =>
        have he : i + 1 + k = (i + k) + 1 := by omega
        rw [he]
        simp [depth, hst, hp]
      | some p =>
        rw [grounded_succ_iff hst hp] at hs
        have h1 : m.depth (i + 1 + k) s = m.depth (i + k) p + 1 := by
          have : i + 1 + k = (i + k) + 1 := by omega
          rw [this, depth_succ_parent hst hp]
        rw [h1, depth_succ_parent hst hp, ih p hs k]

/-- **A uniform grounding bound gives a rank.** The rank is the walk's own length. -/
theorem acyclic_rank_of_grounded {m : Machine ν} {N : Nat}
    (hpl : ∀ s p, m.parentOf s = Option.some p → (m.stack? p).isSome)
    (hg : ∀ s, (m.stack? s).isSome → m.Grounded N s) :
    ∀ s p, m.parentOf s = Option.some p → m.depth (N + 1) p < m.depth (N + 1) s := by
  intro s p hpar
  have hst : ∃ info, m.stack? s = Option.some info ∧ info.handler.parent = Option.some p := by
    unfold parentOf handlerOf at hpar
    cases h : m.stack? s with
    | none => rw [h] at hpar; simp at hpar
    | some info =>
      refine ⟨info, rfl, ?_⟩
      rw [h] at hpar; simpa using hpar
  rcases hst with ⟨info, hi, hp⟩
  have hplive := hpl s p hpar
  have hgp : m.Grounded N p := hg p hplive
  have h1 : m.depth (N + 1) s = m.depth N p + 1 := depth_succ_parent hi hp N
  have h2 : m.depth (N + 1) p = m.depth N p := depth_stable N p hgp 1
  omega

/-- **Acyclic implies grounded within `stacks.length`.** The counting argument of §1: the walk
visits live stacks, all of them indices into `stacks`, and a strictly decreasing rank makes them
pairwise distinct, so it cannot take more than `stacks.length` steps without arriving. -/
theorem grounded_of_rank {m : Machine ν}
    (hpl : ∀ s p, m.parentOf s = Option.some p → (m.stack? p).isSome)
    {r : StackId → Nat} (hdec : ∀ s p, m.parentOf s = Option.some p → r p < r s) :
    ∀ s, (m.stack? s).isSome → m.Grounded m.stacks.length s := by
  intro s hlive
  refine Decidable.byContradiction (fun hng => ?_)
  have hlen := chainList_length_of_not_grounded hpl m.stacks.length s hlive hng
  have hnd := chainList_nodup (m := m) hdec m.stacks.length s
  have hlt : ∀ x ∈ m.chainList m.stacks.length s, x < m.stacks.length := by
    intro x hx
    have hxl := chainList_live hpl m.stacks.length s hlive x hx
    cases hst : m.stack? x with
    | none => rw [hst] at hxl; exact absurd hxl (by simp)
    | some info => exact lt_length_of_stack? hst
  have := Counting.length_le_of_nodup_lt m.stacks.length _ hnd hlt
  omega

/-! ## 3. `WF`

The well-formedness invariant. Each field is one sentence of `fiber.h:165-235`'s operational
description read as a state predicate:

* `currentLive` — `Caml_state->current_stack` is a live `struct stack_info*`.
* `parentLive` — `Stack_parent` of a live stack is live: the runtime frees a stack only when it
  is nobody's parent (`fiber.c:378`, called from `do_return`/`fiber_exn_handler` on the stack
  that is *finishing*, and from `caml_drop_continuation` on one that has been detached).
* `contLive` — a `Cont_tag` block whose field is not NULL names a live stack.
* `acyclic` — the parent relation admits a strictly decreasing rank, so no chain loops. With
  `parentLive` this is exactly "`Stack_parent` walks terminate", which is what the runtime's
  `while (Stack_parent(stk) != NULL)` loops (`interp.c:1295`, `fiber.c:644`, `amd64.S:935-940`)
  assume without checking.
* `noChildOfCurrent` — nothing points at the running stack. The runtime maintains this by
  nulling the performer's parent at `PERFORM` (`interp.c:1345`) before switching to the parent,
  and by only ever creating a child while switching *into* it.
* `parentInj` — a stack has at most one child. Children are created only at `RESUME`
  (`interp.c:1296`), `caml_runstack` and `REPERFORMTERM` (`interp.c:1387`), each time on the
  stack that is being left, which by `noChildOfCurrent` has none yet.
-/

/-- The machine is well formed. -/
structure WF (m : Machine ν) : Prop where
  /-- `Caml_state->current_stack` is live. -/
  currentLive : (m.stack? m.current).isSome
  /-- `Stack_parent` of a live stack is live. -/
  parentLive : ∀ s p, m.parentOf s = Option.some p → (m.stack? p).isSome
  /-- A live `Cont_tag` block names a live stack. -/
  contLive : ∀ (c : ContId) (s : StackId),
    m.conts[c]? = Option.some (Option.some s) → (m.stack? s).isSome
  /-- The parent relation is acyclic. -/
  acyclic : ∃ r : StackId → Nat, ∀ s p, m.parentOf s = Option.some p → r p < r s
  /-- Nothing points at the running stack. -/
  noChildOfCurrent : ∀ s, m.parentOf s ≠ Option.some m.current
  /-- A stack has at most one child. -/
  parentInj : ∀ s t p, m.parentOf s = Option.some p → m.parentOf t = Option.some p → s = t

/-- Under `WF`, every live stack's chain grounds within `stacks.length` steps — the fuel
`outermostOf` gives it. -/
theorem wf_grounded {m : Machine ν} (h : m.WF) {s : StackId} (hlive : (m.stack? s).isSome) :
    m.Grounded m.stacks.length s := by
  obtain ⟨r, hdec⟩ := h.acyclic
  exact grounded_of_rank h.parentLive hdec s hlive

/-- **`outermost_terminates`** (O1 report §5, first blocked statement). `Machine.outermostOf` —
`outermost` with fuel `stacks.length` — really is the outermost stack of the chain: the slot it
names is live and its `Stack_parent` is NULL. This is the fact `interp.c:1295`,
`fiber.c:644` and `amd64.S:935-940` assume when they walk the chain with no bound at all. -/
theorem outermost_terminates {m : Machine ν} (h : m.WF) {sid : StackId}
    (hlive : (m.stack? sid).isSome) :
    (m.stack? (m.outermostOf sid)).map (·.handler.parent) = Option.some Option.none := by
  obtain ⟨info, hi, hp⟩ := wf_grounded h hlive
  unfold outermostOf
  rw [hi]
  simp [hp]

/-- The same fact in the form the preservation proofs use. -/
theorem outermost_live_parent_none {m : Machine ν} (h : m.WF) {sid : StackId}
    (hlive : (m.stack? sid).isSome) :
    (m.stack? (m.outermostOf sid)).isSome ∧ m.parentOf (m.outermostOf sid) = Option.none := by
  obtain ⟨info, hi, hp⟩ := wf_grounded h hlive
  refine ⟨by rw [show m.outermostOf sid = m.outermost m.stacks.length sid from rfl, hi]; simp, ?_⟩
  unfold parentOf handlerOf
  rw [show m.outermostOf sid = m.outermost m.stacks.length sid from rfl, hi]
  exact hp

/-! ## 4. The heap toolkit, extended

O1's toolkit (`lt_length_of_stack?`, `stack?_setStack_self/_ne`, `stack?_freeStack_self/_ne`,
`stack?_setParent_self/_ne`, `frames_withFrames`, `parentOf_withFrames`, and the
`emit`/`setCurrent`/`applyOne`/`applyThree` preservation lemmas) is used verbatim. What it does
not have is the heap *length* and the *liveness* of a slot under each operation, and those are
what `WF` needs. -/

@[simp] theorem stacks_length_setStack (m : Machine ν) (sid : StackId) (info : StackInfo ν) :
    (m.setStack sid info).stacks.length = m.stacks.length := by
  simp [setStack]

@[simp] theorem stacks_length_freeStack (m : Machine ν) (sid : StackId) :
    (m.freeStack sid).stacks.length = m.stacks.length := by
  simp [freeStack]

@[simp] theorem stacks_length_setParent (m : Machine ν) (sid : StackId) (p : Option StackId) :
    (m.setParent sid p).stacks.length = m.stacks.length := by
  unfold setParent; cases m.stack? sid <;> simp

@[simp] theorem stacks_length_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).stacks.length = m.stacks.length := by
  unfold withFrames; cases m.stack? m.current <;> simp

@[simp] theorem stacks_length_emit (m : Machine ν) (e : Event) :
    (m.emit e).stacks.length = m.stacks.length := rfl

@[simp] theorem stacks_length_setCurrent (m : Machine ν) (s : StackId) :
    (m.setCurrent s).stacks.length = m.stacks.length := rfl

@[simp] theorem stacks_length_setControl (m : Machine ν) (c : Control ν) :
    (m.setControl c).stacks.length = m.stacks.length := rfl

/-- Setting a live slot keeps every slot's liveness. -/
theorem isSome_setStack {m : Machine ν} {sid : StackId} {info0 : StackInfo ν}
    (info : StackInfo ν) (h : m.stack? sid = Option.some info0) (t : StackId) :
    ((m.setStack sid info).stack? t).isSome = (m.stack? t).isSome := by
  by_cases ht : sid = t
  · subst ht; rw [stack?_setStack_self info h, h]; simp
  · rw [stack?_setStack_ne info ht]

theorem parentOf_setStack_ne {m : Machine ν} {sid t : StackId} (info : StackInfo ν)
    (h : sid ≠ t) : (m.setStack sid info).parentOf t = m.parentOf t := by
  unfold parentOf handlerOf; rw [stack?_setStack_ne info h]

theorem parentOf_setParent_ne {m : Machine ν} {sid t : StackId} (p : Option StackId)
    (h : sid ≠ t) : (m.setParent sid p).parentOf t = m.parentOf t := by
  unfold parentOf handlerOf; rw [stack?_setParent_ne p h]

theorem parentOf_setParent_self {m : Machine ν} {sid : StackId} {info : StackInfo ν}
    (p : Option StackId) (h : m.stack? sid = Option.some info) :
    (m.setParent sid p).parentOf sid = p := by
  unfold parentOf handlerOf; rw [stack?_setParent_self p h]; rfl

theorem isSome_setParent {m : Machine ν} (sid : StackId) (p : Option StackId) (t : StackId) :
    ((m.setParent sid p).stack? t).isSome = (m.stack? t).isSome := by
  unfold setParent
  cases h : m.stack? sid with
  | none => rfl
  | some info => exact isSome_setStack _ h t

theorem isSome_withFrames {m : Machine ν} (fs : List (Frame ν)) (t : StackId) :
    ((m.withFrames fs).stack? t).isSome = (m.stack? t).isSome := by
  unfold withFrames
  cases h : m.stack? m.current with
  | none => rfl
  | some info => exact isSome_setStack _ h t

theorem isSome_freeStack_ne {m : Machine ν} {sid t : StackId} (h : sid ≠ t) :
    ((m.freeStack sid).stack? t).isSome = (m.stack? t).isSome := by
  rw [stack?_freeStack_ne h]

theorem parentOf_freeStack_ne {m : Machine ν} {sid t : StackId} (h : sid ≠ t) :
    (m.freeStack sid).parentOf t = m.parentOf t := by
  unfold parentOf handlerOf; rw [stack?_freeStack_ne h]

theorem stack?_freeStack (m : Machine ν) (sid : StackId) :
    (m.freeStack sid).stack? sid = Option.none := by
  unfold freeStack stack?
  by_cases hlt : sid < m.stacks.length
  · simp [List.getElem?_set_self hlt]
  · have hge : m.stacks.length ≤ sid := Nat.le_of_not_lt hlt
    have : (m.stacks.set sid Option.none)[sid]? = Option.none :=
      List.getElem?_eq_none (by simpa using hge)
    simp [this]

theorem parentOf_freeStack_self (m : Machine ν) (sid : StackId) :
    (m.freeStack sid).parentOf sid = Option.none := by
  unfold parentOf handlerOf; rw [stack?_freeStack]; rfl

theorem isSome_freeStack_self (m : Machine ν) (sid : StackId) :
    ((m.freeStack sid).stack? sid).isSome = false := by
  rw [stack?_freeStack]; rfl

/-- A stack is live only if its index is in range; the converse needs the slot. -/
theorem lt_length_of_isSome {m : Machine ν} {sid : StackId} (h : (m.stack? sid).isSome) :
    sid < m.stacks.length := by
  cases hst : m.stack? sid with
  | none => rw [hst] at h; exact absurd h (by simp)
  | some info => exact lt_length_of_stack? hst

theorem isSome_iff_exists {m : Machine ν} {sid : StackId} :
    (m.stack? sid).isSome ↔ ∃ info, m.stack? sid = Option.some info := by
  cases h : m.stack? sid with
  | none => simp
  | some info => simp

/-! ### `SameHeap`

Most of `step`'s arms change the control, the trace, the mutable cell and the frames of the
current stack, and nothing else. `SameHeap` is exactly what `WF` can see, so one lemma carries
all of them. -/

/-- `m'` has the parent forest `m` has: the same number of slots, the same slots live, and the
same parent pointers. This is everything `outermost`, `Grounded` and `ChainReaches` read. -/
structure SameParents (m m' : Machine ν) : Prop where
  length : m'.stacks.length = m.stacks.length
  live : ∀ s, (m'.stack? s).isSome = (m.stack? s).isSome
  parent : ∀ s, m'.parentOf s = m.parentOf s

/-- `SameParents` and the same running stack. Frames, control, trace, cell and the continuation
heap are free. -/
structure SameStacks (m m' : Machine ν) : Prop extends SameParents m m' where
  current : m'.current = m.current

/-- `SameStacks` and the same continuation heap: everything `WF` can see. -/
structure SameHeap (m m' : Machine ν) : Prop extends SameStacks m m' where
  conts : m'.conts = m.conts

theorem SameParents.rfl' (m : Machine ν) : SameParents m m :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem SameParents.trans {a b c : Machine ν} (h1 : SameParents a b) (h2 : SameParents b c) :
    SameParents a c :=
  ⟨by rw [h2.length, h1.length], fun s => by rw [h2.live s, h1.live s],
    fun s => by rw [h2.parent s, h1.parent s]⟩

/-- Switching the running stack leaves the parent forest alone. -/
theorem sameParents_setCurrent (m : Machine ν) (s : StackId) : SameParents m (m.setCurrent s) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem SameStacks.rfl' (m : Machine ν) : SameStacks m m := ⟨SameParents.rfl' m, rfl⟩

theorem SameStacks.trans {a b c : Machine ν} (h1 : SameStacks a b) (h2 : SameStacks b c) :
    SameStacks a c :=
  ⟨h1.toSameParents.trans h2.toSameParents, by rw [h2.current, h1.current]⟩

theorem SameHeap.rfl' (m : Machine ν) : SameHeap m m := ⟨SameStacks.rfl' m, rfl⟩

theorem SameHeap.trans {a b c : Machine ν} (h1 : SameHeap a b) (h2 : SameHeap b c) :
    SameHeap a c :=
  ⟨h1.toSameStacks.trans h2.toSameStacks, by rw [h2.conts, h1.conts]⟩

theorem SameHeap.setControl {m a : Machine ν} (h : SameHeap m a) (c : Control ν) :
    SameHeap m (a.setControl c) :=
  ⟨⟨⟨h.length, h.live, h.parent⟩, h.current⟩, h.conts⟩

theorem SameHeap.emit {m a : Machine ν} (h : SameHeap m a) (e : Event) :
    SameHeap m (a.emit e) :=
  ⟨⟨⟨h.length, h.live, h.parent⟩, h.current⟩, h.conts⟩

theorem SameHeap.setCell {m a : Machine ν} (h : SameHeap m a) (v : Value ν) :
    SameHeap m ({ a with cell := v } : Machine ν) :=
  ⟨⟨⟨h.length, h.live, h.parent⟩, h.current⟩, h.conts⟩

theorem SameHeap.withFrames {m a : Machine ν} (h : SameHeap m a) (fs : List (Frame ν)) :
    SameHeap m (a.withFrames fs) :=
  ⟨⟨⟨by rw [stacks_length_withFrames, h.length],
    fun s => by rw [isSome_withFrames, h.live s],
    fun s => by rw [parentOf_withFrames, h.parent s]⟩,
    by rw [current_withFrames, h.current]⟩, by rw [conts_withFrames, h.conts]⟩

theorem SameHeap.pushFrame {m a : Machine ν} (h : SameHeap m a) (f : Frame ν) :
    SameHeap m (a.pushFrame f) := h.withFrames _

theorem SameHeap.applyOne {m a : Machine ν} (h : SameHeap m a) (f v : Value ν) :
    SameHeap m (a.applyOne f v) := (h.pushFrame _).setControl _

theorem SameHeap.applyThree {m a : Machine ν} (h : SameHeap m a) (f x y z : Value ν) :
    SameHeap m (a.applyThree f x y z) := (h.withFrames _).setControl _

/-! `setTriple` (`fiber.c:645-647`) rewrites a handler's three closures and leaves the parent
pointer and the liveness of every slot alone. -/

theorem current_setTriple (m : Machine ν) (sid : StackId) (hv hx hf : Value ν) :
    (m.setTriple sid hv hx hf).current = m.current := by
  unfold setTriple; cases m.stack? sid <;> rfl

theorem conts_setTriple (m : Machine ν) (sid : StackId) (hv hx hf : Value ν) :
    (m.setTriple sid hv hx hf).conts = m.conts := by
  unfold setTriple; cases m.stack? sid <;> rfl

theorem stacks_length_setTriple (m : Machine ν) (sid : StackId) (hv hx hf : Value ν) :
    (m.setTriple sid hv hx hf).stacks.length = m.stacks.length := by
  unfold setTriple; cases m.stack? sid <;> simp

theorem isSome_setTriple (m : Machine ν) (sid : StackId) (hv hx hf : Value ν) (t : StackId) :
    ((m.setTriple sid hv hx hf).stack? t).isSome = (m.stack? t).isSome := by
  unfold setTriple
  cases h : m.stack? sid with
  | none => rfl
  | some info => exact isSome_setStack _ h t

theorem parentOf_setTriple (m : Machine ν) (sid : StackId) (hv hx hf : Value ν) (t : StackId) :
    (m.setTriple sid hv hx hf).parentOf t = m.parentOf t := by
  unfold setTriple
  cases h : m.stack? sid with
  | none => rfl
  | some info =>
    by_cases ht : sid = t
    · subst ht
      unfold parentOf handlerOf
      rw [stack?_setStack_self _ h, h]
      rfl
    · exact parentOf_setStack_ne _ ht

theorem SameHeap.triple {m a : Machine ν} (h : SameHeap m a) (sid : StackId)
    (hv hx hf : Value ν) : SameHeap m (a.setTriple sid hv hx hf) :=
  ⟨⟨⟨by rw [stacks_length_setTriple, h.length],
    fun s => by rw [isSome_setTriple, h.live s],
    fun s => by rw [parentOf_setTriple, h.parent s]⟩,
    by rw [current_setTriple, h.current]⟩, by rw [conts_setTriple, h.conts]⟩

/-- `WF` sees only what `SameHeap` preserves. -/
theorem WF.sameHeap {m m' : Machine ν} (h : m.WF) (hs : SameHeap m m') : m'.WF := by
  obtain ⟨r, hdec⟩ := h.acyclic
  refine ⟨?_, ?_, ?_, ⟨r, ?_⟩, ?_, ?_⟩
  · rw [hs.current, hs.live]; exact h.currentLive
  · intro s p hp
    rw [hs.parent] at hp
    rw [hs.live]
    exact h.parentLive s p hp
  · intro c s hc
    rw [hs.conts] at hc
    rw [hs.live]
    exact h.contLive c s hc
  · intro s p hp; rw [hs.parent] at hp; exact hdec s p hp
  · intro s hp
    rw [hs.parent, hs.current] at hp
    exact h.noChildOfCurrent s hp
  · intro s t p hs' ht'
    rw [hs.parent] at hs' ht'
    exact h.parentInj s t p hs' ht'

/-! ### Grounding, read through `parentOf`

The `parentOf` spelling of §2's lemmas; every preservation proof below uses these rather than
unfolding a `StackInfo`. -/

theorem exists_info_of_parentOf {m : Machine ν} {s p : StackId} (h : m.parentOf s = Option.some p) :
    ∃ info, m.stack? s = Option.some info ∧ info.handler.parent = Option.some p := by
  unfold parentOf handlerOf at h
  cases hst : m.stack? s with
  | none => rw [hst] at h; simp at h
  | some info => refine ⟨info, rfl, ?_⟩; rw [hst] at h; simpa using h

theorem isSome_of_parentOf {m : Machine ν} {s p : StackId} (h : m.parentOf s = Option.some p) :
    (m.stack? s).isSome := by
  obtain ⟨info, hi, -⟩ := exists_info_of_parentOf h
  rw [hi]; rfl

theorem grounded_succ_iff' {m : Machine ν} {s p : StackId} (h : m.parentOf s = Option.some p)
    (n : Nat) : m.Grounded (n + 1) s ↔ m.Grounded n p := by
  obtain ⟨info, hi, hp⟩ := exists_info_of_parentOf h
  exact grounded_succ_iff hi hp n

theorem grounded_root {m : Machine ν} {s : StackId} (hlive : (m.stack? s).isSome)
    (hp : m.parentOf s = Option.none) (n : Nat) : m.Grounded n s := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp hlive
  refine grounded_of_parent_none hi ?_ n
  unfold parentOf handlerOf at hp
  rw [hi] at hp
  simpa using hp

theorem live_of_grounded {m : Machine ν} {n : Nat} {s : StackId} (h : m.Grounded n s) :
    (m.stack? s).isSome := by
  cases hst : m.stack? s with
  | none => exact absurd h (not_grounded_of_dead hst n)
  | some info => rfl

/-- A stack is never its own parent. -/
theorem parent_ne_self {m : Machine ν} (h : m.WF) {s p : StackId}
    (hp : m.parentOf s = Option.some p) : p ≠ s := by
  obtain ⟨r, hdec⟩ := h.acyclic
  intro hpe
  have hlt := hdec s p hp
  rw [hpe] at hlt
  omega

/-! ### Congruence along `SameParents` -/

theorem outermost_congr {m m' : Machine ν} (hs : SameParents m m') :
    ∀ (n : Nat) (s : StackId), m'.outermost n s = m.outermost n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    cases hst : m.stack? s with
    | none =>
      have h' : m'.stack? s = Option.none := by
        have hl := hs.live s
        rw [hst] at hl
        cases hs' : m'.stack? s with
        | none => rfl
        | some i => rw [hs'] at hl; simp at hl
      simp [outermost, hst, h']
    | some info =>
      cases hs' : m'.stack? s with
      | none =>
        have hl := hs.live s
        rw [hst, hs'] at hl
        simp at hl
      | some info' =>
        have hp : info'.handler.parent = info.handler.parent := by
          have hpp := hs.parent s
          unfold parentOf handlerOf at hpp
          rw [hst, hs'] at hpp
          simpa using hpp
        cases hpar : info.handler.parent with
        | none => simp [outermost, hst, hs', hp, hpar]
        | some p =>
          rw [show m'.outermost (k + 1) s = m'.outermost k p by simp [outermost, hs', hp, hpar],
              show m.outermost (k + 1) s = m.outermost k p by simp [outermost, hst, hpar]]
          exact ih p

theorem outermostOf_congr {m m' : Machine ν} (hs : SameParents m m') (s : StackId) :
    m'.outermostOf s = m.outermostOf s := by
  unfold outermostOf
  rw [hs.length]
  exact outermost_congr hs _ s

/-- `Grounded`, read as a pair of `parentOf`/liveness facts about the walk's endpoint. -/
theorem grounded_iff' (m : Machine ν) (n : Nat) (s : StackId) :
    m.Grounded n s ↔
      ((m.stack? (m.outermost n s)).isSome ∧ m.parentOf (m.outermost n s) = Option.none) := by
  constructor
  · rintro ⟨info, hi, hp⟩
    refine ⟨by rw [hi]; rfl, ?_⟩
    unfold parentOf handlerOf
    rw [hi]
    simpa using hp
  · rintro ⟨hlive, hp⟩
    obtain ⟨info, hi⟩ := isSome_iff_exists.mp hlive
    refine ⟨info, hi, ?_⟩
    unfold parentOf handlerOf at hp
    rw [hi] at hp
    simpa using hp

theorem grounded_congr {m m' : Machine ν} (hs : SameParents m m') (n : Nat) (s : StackId) :
    m'.Grounded n s ↔ m.Grounded n s := by
  rw [grounded_iff', grounded_iff', outermost_congr hs n s, hs.live, hs.parent]

/-! ### `ChainReaches`

"The parent chain from `s` passes through `t`". It is the hypothesis the attach transitions need:
`%resume`, `%runstack` and `%reperform` each make one stack the parent of another, and that is a
cycle exactly when the new parent's own chain already contains the new child. -/

/-- The parent chain from `s` reaches `t`. -/
inductive ChainReaches (m : Machine ν) : StackId → StackId → Prop
  | refl (s : StackId) : ChainReaches m s s
  | step {s p t : StackId} :
      m.parentOf s = Option.some p → ChainReaches m p t → ChainReaches m s t

theorem chainReaches_congr {m m' : Machine ν} (hs : SameParents m m') (s t : StackId) :
    m'.ChainReaches s t ↔ m.ChainReaches s t := by
  constructor
  · intro h
    induction h with
    | refl s => exact ChainReaches.refl s
    | step hp _ ih => exact ChainReaches.step (by rw [← hs.parent]; exact hp) ih
  · intro h
    induction h with
    | refl s => exact ChainReaches.refl s
    | step hp _ ih => exact ChainReaches.step (by rw [hs.parent]; exact hp) ih

theorem outermost_zero (m : Machine ν) (s : StackId) : m.outermost 0 s = s := rfl

/-- Off the node whose parent is rewritten, nothing changes. -/
theorem grounded_setParent_off (m : Machine ν) (x : StackId) (p : Option StackId) :
    ∀ (n : Nat) (y : StackId), ¬ m.ChainReaches y x → m.Grounded n y →
      (m.setParent x p).Grounded n y := by
  intro n
  induction n with
  | zero =>
    intro y hnr hg
    have hne : x ≠ y := by intro hxy; subst hxy; exact hnr (ChainReaches.refl _)
    rw [grounded_iff', outermost_zero] at hg
    exact grounded_root (by rw [isSome_setParent]; exact hg.1)
      (by rw [parentOf_setParent_ne p hne]; exact hg.2) 0
  | succ k ih =>
    intro y hnr hg
    have hne : x ≠ y := by intro hxy; subst hxy; exact hnr (ChainReaches.refl _)
    have hlive := live_of_grounded hg
    cases hpy : m.parentOf y with
    | none =>
      exact grounded_root (by rw [isSome_setParent]; exact hlive)
        (by rw [parentOf_setParent_ne p hne]; exact hpy) _
    | some q =>
      have hgq : m.Grounded k q := (grounded_succ_iff' hpy k).mp hg
      have hnrq : ¬ m.ChainReaches q x := fun hr => hnr (ChainReaches.step hpy hr)
      exact (grounded_succ_iff' (m := m.setParent x p) (s := y) (p := q)
        (by rw [parentOf_setParent_ne p hne]; exact hpy) k).mpr (ih q hnrq hgq)

/-- **Attaching a stack to a chain that does not contain it keeps every walk terminating.**
This is the acyclicity half of `%resume` (`interp.c:1296`), `%runstack` and `%reperform`
(`interp.c:1387`). -/
theorem grounded_setParent_attach (m : Machine ν) {x c : StackId} {kc : Nat}
    (hnr : ¬ m.ChainReaches c x) (hcg : m.Grounded kc c) :
    ∀ (n : Nat) (y : StackId), m.Grounded n y →
      (m.setParent x (Option.some c)).Grounded (n + 1 + kc) y := by
  have hcg' : (m.setParent x (Option.some c)).Grounded kc c :=
    grounded_setParent_off m x _ kc c hnr hcg
  intro n
  induction n with
  | zero =>
    intro y hg
    rw [grounded_iff', outermost_zero] at hg
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨info, hi⟩ := isSome_iff_exists.mp hg.1
      have hpx : (m.setParent x (Option.some c)).parentOf x = Option.some c :=
        parentOf_setParent_self _ hi
      have : (m.setParent x (Option.some c)).Grounded (kc + 1) x :=
        (grounded_succ_iff' hpx kc).mpr hcg'
      exact grounded_le this (by omega)
    · exact grounded_root (by rw [isSome_setParent]; exact hg.1)
        (by rw [parentOf_setParent_ne _ hxy]; exact hg.2) _
  | succ k ih =>
    intro y hg
    have hlive := live_of_grounded hg
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨info, hi⟩ := isSome_iff_exists.mp hlive
      have hpx : (m.setParent x (Option.some c)).parentOf x = Option.some c :=
        parentOf_setParent_self _ hi
      have : (m.setParent x (Option.some c)).Grounded (kc + 1) x :=
        (grounded_succ_iff' hpx kc).mpr hcg'
      exact grounded_le this (by omega)
    · cases hpy : m.parentOf y with
      | none =>
        exact grounded_root (by rw [isSome_setParent]; exact hlive)
          (by rw [parentOf_setParent_ne _ hxy]; exact hpy) _
      | some q =>
        have hgq : m.Grounded k q := (grounded_succ_iff' hpy k).mp hg
        have hstep : (m.setParent x (Option.some c)).Grounded (k + 1 + kc + 1) y :=
          (grounded_succ_iff' (m := m.setParent x (Option.some c)) (s := y) (p := q)
            (by rw [parentOf_setParent_ne _ hxy]; exact hpy) (k + 1 + kc)).mpr (ih q hgq)
        exact grounded_le hstep (by omega)

/-- **Freeing a childless stack keeps every other walk terminating** (`fiber.c:378`, called from
`do_return`, `fiber_exn_handler` and `caml_drop_continuation`). -/
theorem grounded_freeStack (m : Machine ν) {x : StackId}
    (hchild : ∀ q, m.parentOf q ≠ Option.some x) :
    ∀ (n : Nat) (y : StackId), y ≠ x → m.Grounded n y → (m.freeStack x).Grounded n y := by
  intro n
  induction n with
  | zero =>
    intro y hne hg
    rw [grounded_iff', outermost_zero] at hg
    exact grounded_root (by rw [isSome_freeStack_ne (Ne.symm hne)]; exact hg.1)
      (by rw [parentOf_freeStack_ne (Ne.symm hne)]; exact hg.2) 0
  | succ k ih =>
    intro y hne hg
    have hlive := live_of_grounded hg
    cases hpy : m.parentOf y with
    | none =>
      exact grounded_root (by rw [isSome_freeStack_ne (Ne.symm hne)]; exact hlive)
        (by rw [parentOf_freeStack_ne (Ne.symm hne)]; exact hpy) _
    | some q =>
      have hgq : m.Grounded k q := (grounded_succ_iff' hpy k).mp hg
      have hqx : q ≠ x := by intro hq; exact hchild y (hq ▸ hpy)
      exact (grounded_succ_iff' (m := m.freeStack x) (s := y) (p := q)
        (by rw [parentOf_freeStack_ne (Ne.symm hne)]; exact hpy) k).mpr (ih q hqx hgq)

/-! ### The composite preservation lemmas

One lemma per shape the eight transitions build. Each is stated about the shape, so the arm
lemmas of §6 are one `exact` each. -/

/-- `WF` needs only that `m'`'s live continuations were live continuations of `m`. -/
theorem WF.contsWeaken {m m' : Machine ν} (h : m.WF) (hs : SameStacks m m')
    (hc : ∀ (c : ContId) (s : StackId),
      m'.conts[c]? = Option.some (Option.some s) → (m.stack? s).isSome) : m'.WF := by
  obtain ⟨r, hdec⟩ := h.acyclic
  refine ⟨?_, ?_, ?_, ⟨r, ?_⟩, ?_, ?_⟩
  · rw [hs.current, hs.live]; exact h.currentLive
  · intro s p hp; rw [hs.parent] at hp; rw [hs.live]; exact h.parentLive s p hp
  · intro c s hcs; rw [hs.live]; exact hc c s hcs
  · intro s p hp; rw [hs.parent] at hp; exact hdec s p hp
  · intro s hp; rw [hs.parent, hs.current] at hp; exact h.noChildOfCurrent s hp
  · intro s t p hs' ht'; rw [hs.parent] at hs' ht'; exact h.parentInj s t p hs' ht'

/-- The parent map after one `setParent`. -/
theorem parentOf_setParent {m : Machine ν} {x : StackId} (hxlive : (m.stack? x).isSome)
    (c : Option StackId) (t : StackId) :
    (m.setParent x c).parentOf t = if t = x then c else m.parentOf t := by
  by_cases ht : t = x
  · subst ht
    obtain ⟨info, hi⟩ := isSome_iff_exists.mp hxlive
    rw [parentOf_setParent_self c hi]
    simp
  · rw [parentOf_setParent_ne c (Ne.symm ht)]
    simp [ht]

/-- **`%resume`, `%runstack` and the `reperform` root route, as one lemma.** `x` becomes a child
of the running stack and `enter` becomes the running stack. This is `interp.c:1295-1297` and
`amd64.S:935-944` for `%resume` (`x` the outermost of the captured chain, `enter` the innermost),
`caml_runstack` for `%runstack` (`x = enter`, the fresh stack), and the resume inside
`REPERFORMTERM`'s root route (`interp.c:1374-1381`). -/
theorem wf_attach_enter_core {m : Machine ν} (h : m.WF) {x enter : StackId}
    (hxlive : (m.stack? x).isSome)
    (henterLive : (m.stack? enter).isSome)
    (henterChildless : ∀ q, m.parentOf q ≠ Option.some enter)
    (hne : enter ≠ m.current)
    (hnr : ¬ m.ChainReaches m.current x) :
    ((m.setParent x (Option.some m.current)).setCurrent enter).WF := by
  have hsp : SameParents (m.setParent x (Option.some m.current))
      ((m.setParent x (Option.some m.current)).setCurrent enter) :=
    sameParents_setCurrent _ _
  have hpar : ∀ t, ((m.setParent x (Option.some m.current)).setCurrent enter).parentOf t
      = if t = x then Option.some m.current else m.parentOf t := by
    intro t
    rw [hsp.parent t]
    exact parentOf_setParent hxlive _ t
  have hlive : ∀ t, (((m.setParent x (Option.some m.current)).setCurrent enter).stack? t).isSome
      = (m.stack? t).isSome := by
    intro t; rw [hsp.live t]; exact isSome_setParent x _ t
  have hcur : ((m.setParent x (Option.some m.current)).setCurrent enter).current = enter := rfl
  have hconts : ((m.setParent x (Option.some m.current)).setCurrent enter).conts = m.conts := by
    rw [conts_setCurrent, conts_setParent]
  have hparentLive : ∀ s p, ((m.setParent x (Option.some m.current)).setCurrent enter).parentOf s
      = Option.some p → ((((m.setParent x (Option.some m.current)).setCurrent enter).stack? p)).isSome := by
    intro s p hp
    rw [hpar] at hp
    rw [hlive]
    by_cases hs : s = x
    · rw [if_pos hs] at hp
      have hpc : m.current = p := by simpa using hp
      subst hpc
      exact h.currentLive
    · rw [if_neg hs] at hp
      exact h.parentLive s p hp
  refine ⟨?_, hparentLive, ?_, ?_, ?_, ?_⟩
  · rw [hcur, hlive]; exact henterLive
  · intro c s hc
    rw [hconts] at hc
    rw [hlive]
    exact h.contLive c s hc
  · -- acyclicity: the attached chain is grounded because `m.current`'s chain misses `x`
    refine ⟨(((m.setParent x (Option.some m.current)).setCurrent enter)).depth
      (m.stacks.length + 1 + m.stacks.length + 1), ?_⟩
    refine acyclic_rank_of_grounded (N := m.stacks.length + 1 + m.stacks.length)
      hparentLive ?_
    intro s hs
    rw [hlive] at hs
    refine (grounded_congr hsp _ s).mpr ?_
    exact grounded_setParent_attach m hnr (wf_grounded h h.currentLive) m.stacks.length s
      (wf_grounded h hs)
  · intro s hp
    rw [hpar, hcur] at hp
    by_cases hs : s = x
    · rw [if_pos hs] at hp
      have hpc : m.current = enter := by simpa using hp
      exact hne hpc.symm
    · rw [if_neg hs] at hp
      exact henterChildless s hp
  · intro s t p hs ht
    rw [hpar] at hs ht
    by_cases hsx : s = x <;> by_cases htx : t = x
    · rw [hsx, htx]
    · rw [if_pos hsx] at hs
      rw [if_neg htx] at ht
      have hpc : m.current = p := by simpa using hs
      subst hpc
      exact absurd ht (h.noChildOfCurrent t)
    · rw [if_neg hsx] at hs
      rw [if_pos htx] at ht
      have hpc : m.current = p := by simpa using ht
      subst hpc
      exact absurd hs (h.noChildOfCurrent s)
    · rw [if_neg hsx] at hs
      rw [if_neg htx] at ht
      exact h.parentInj s t p hs ht

/-- `Stack_parent(x) = …` on a freed slot writes nothing. -/
theorem setParent_of_dead {m : Machine ν} {x : StackId} (h : m.stack? x = Option.none)
    (p : Option StackId) : m.setParent x p = m := by
  unfold setParent; rw [h]

/-- `wf_attach_enter_core` with the new parent named, so a caller can supply it up to an
equation rather than syntactically. -/
theorem wf_attach_enter_core' {m : Machine ν} (h : m.WF) {x enter c : StackId}
    (hc : c = m.current)
    (hxlive : (m.stack? x).isSome)
    (henterLive : (m.stack? enter).isSome)
    (henterChildless : ∀ q, m.parentOf q ≠ Option.some enter)
    (hne : enter ≠ m.current)
    (hnr : ¬ m.ChainReaches m.current x) :
    ((m.setParent x (Option.some c)).setCurrent enter).WF := by
  subst hc
  exact wf_attach_enter_core h hxlive henterLive henterChildless hne hnr

/-- **A child stack completes**: `do_return` with `sp == Stack_high` (`interp.c:576-594`) and
`raise_notrace` past the last trap (`interp.c:980-999`) both free the running stack and switch to
its parent. -/
theorem wf_free_switch {m : Machine ν} (h : m.WF) {p : StackId}
    (hp : m.parentOf m.current = Option.some p)
    (hcont : ∀ (c : ContId) (s : StackId),
      m.conts[c]? = Option.some (Option.some s) → s ≠ m.current) :
    ((m.freeStack m.current).setCurrent p).WF := by
  have hpne : p ≠ m.current := parent_ne_self h hp
  have hsp : SameParents (m.freeStack m.current)
      ((m.freeStack m.current).setCurrent p) := sameParents_setCurrent _ _
  have hpar : ∀ t, ((m.freeStack m.current).setCurrent p).parentOf t
      = if t = m.current then Option.none else m.parentOf t := by
    intro t
    rw [hsp.parent t]
    by_cases ht : t = m.current
    · subst ht; rw [parentOf_freeStack_self]; simp
    · rw [parentOf_freeStack_ne (Ne.symm ht)]; simp [ht]
  have hlive : ∀ t, (((m.freeStack m.current).setCurrent p).stack? t).isSome
      = if t = m.current then false else (m.stack? t).isSome := by
    intro t
    rw [hsp.live t]
    by_cases ht : t = m.current
    · subst ht; rw [isSome_freeStack_self]; simp
    · rw [isSome_freeStack_ne (Ne.symm ht)]; simp [ht]
  have hcur : ((m.freeStack m.current).setCurrent p).current = p := rfl
  have hconts : ((m.freeStack m.current).setCurrent p).conts = m.conts := rfl
  have hedge : ∀ s q, ((m.freeStack m.current).setCurrent p).parentOf s = Option.some q →
      s ≠ m.current ∧ m.parentOf s = Option.some q := by
    intro s q hq
    rw [hpar] at hq
    by_cases hs : s = m.current
    · rw [if_pos hs] at hq; simp at hq
    · rw [if_neg hs] at hq; exact ⟨hs, hq⟩
  have hparentLive : ∀ s q, ((m.freeStack m.current).setCurrent p).parentOf s = Option.some q →
      ((((m.freeStack m.current).setCurrent p).stack? q)).isSome := by
    intro s q hq
    obtain ⟨hs, hq'⟩ := hedge s q hq
    have hqne : q ≠ m.current := by
      intro hqc; exact h.noChildOfCurrent s (hqc ▸ hq')
    rw [hlive, if_neg hqne]
    exact h.parentLive s q hq'
  refine ⟨?_, hparentLive, ?_, ?_, ?_, ?_⟩
  · rw [hcur, hlive, if_neg hpne]
    exact h.parentLive _ _ hp
  · intro c s hc
    rw [hconts] at hc
    rw [hlive, if_neg (hcont c s hc)]
    exact h.contLive c s hc
  · refine ⟨((m.freeStack m.current).setCurrent p).depth (m.stacks.length + 1), ?_⟩
    refine acyclic_rank_of_grounded (N := m.stacks.length) hparentLive ?_
    intro s hs
    rw [hlive] at hs
    by_cases hsc : s = m.current
    · rw [if_pos hsc] at hs; simp at hs
    · rw [if_neg hsc] at hs
      refine (grounded_congr hsp _ s).mpr ?_
      exact grounded_freeStack m h.noChildOfCurrent m.stacks.length s hsc (wf_grounded h hs)
  · intro s hps
    rw [hcur] at hps
    obtain ⟨hs, hq'⟩ := hedge s p hps
    exact hs (h.parentInj s m.current p hq' hp)
  · intro s t q hs ht
    exact h.parentInj s t q (hedge s q hs).2 (hedge t q ht).2

/-- **`caml_drop_continuation`** (`fiber.c:659-664`): a detached, childless stack is freed and no
handler of it runs. -/
theorem wf_freeStack {m : Machine ν} (h : m.WF) {x : StackId} (hne : x ≠ m.current)
    (hchild : ∀ q, m.parentOf q ≠ Option.some x)
    (hcont : ∀ (c : ContId) (s : StackId),
      m.conts[c]? = Option.some (Option.some s) → s ≠ x) :
    (m.freeStack x).WF := by
  have hpar : ∀ t, (m.freeStack x).parentOf t = if t = x then Option.none else m.parentOf t := by
    intro t
    by_cases ht : t = x
    · subst ht; rw [parentOf_freeStack_self]; simp
    · rw [parentOf_freeStack_ne (Ne.symm ht)]; simp [ht]
  have hlive : ∀ t, ((m.freeStack x).stack? t).isSome
      = if t = x then false else (m.stack? t).isSome := by
    intro t
    by_cases ht : t = x
    · subst ht; rw [isSome_freeStack_self]; simp
    · rw [isSome_freeStack_ne (Ne.symm ht)]; simp [ht]
  have hedge : ∀ s q, (m.freeStack x).parentOf s = Option.some q →
      s ≠ x ∧ m.parentOf s = Option.some q := by
    intro s q hq
    rw [hpar] at hq
    by_cases hs : s = x
    · rw [if_pos hs] at hq; simp at hq
    · rw [if_neg hs] at hq; exact ⟨hs, hq⟩
  have hparentLive : ∀ s q, (m.freeStack x).parentOf s = Option.some q →
      (((m.freeStack x).stack? q)).isSome := by
    intro s q hq
    obtain ⟨hs, hq'⟩ := hedge s q hq
    have hqne : q ≠ x := by intro hqx; exact hchild s (hqx ▸ hq')
    rw [hlive, if_neg hqne]
    exact h.parentLive s q hq'
  refine ⟨?_, hparentLive, ?_, ?_, ?_, ?_⟩
  · rw [show (m.freeStack x).current = m.current from rfl, hlive, if_neg (Ne.symm hne)]
    exact h.currentLive
  · intro c s hc
    rw [show (m.freeStack x).conts = m.conts from rfl] at hc
    rw [hlive, if_neg (hcont c s hc)]
    exact h.contLive c s hc
  · refine ⟨(m.freeStack x).depth (m.stacks.length + 1), ?_⟩
    refine acyclic_rank_of_grounded (N := m.stacks.length) hparentLive ?_
    intro s hs
    rw [hlive] at hs
    by_cases hsx : s = x
    · rw [if_pos hsx] at hs; simp at hs
    · rw [if_neg hsx] at hs
      exact grounded_freeStack m hchild m.stacks.length s hsx (wf_grounded h hs)
  · intro s hps
    rw [show (m.freeStack x).current = m.current from rfl] at hps
    exact h.noChildOfCurrent s (hedge s m.current hps).2
  · intro s t q hs ht
    exact h.parentInj s t q (hedge s q hs).2 (hedge t q ht).2

/-- From a parentless stack the chain reaches only itself. -/
theorem chainReaches_root {m : Machine ν} {s t : StackId} (hp : m.parentOf s = Option.none)
    (h : m.ChainReaches s t) : t = s := by
  cases h with
  | refl _ => rfl
  | step hp' _ => rw [hp] at hp'; exact absurd hp' (by simp)

/-- **`PERFORM` and `REPERFORMTERM` null the performer's parent and switch to it**
(`interp.c:1345,1352`, `:1387`, `amd64.S:884-894`). -/
theorem wf_detach_switch {m : Machine ν} (h : m.WF) {p : StackId}
    (hp : m.parentOf m.current = Option.some p) :
    ((m.setParent m.current Option.none).setCurrent p).WF := by
  have hsp : SameParents (m.setParent m.current Option.none)
      ((m.setParent m.current Option.none).setCurrent p) := sameParents_setCurrent _ _
  have hxlive : (m.stack? m.current).isSome := h.currentLive
  have hpar : ∀ t, ((m.setParent m.current Option.none).setCurrent p).parentOf t
      = if t = m.current then Option.none else m.parentOf t := by
    intro t; rw [hsp.parent t]; exact parentOf_setParent hxlive _ t
  have hlive : ∀ t, (((m.setParent m.current Option.none).setCurrent p).stack? t).isSome
      = (m.stack? t).isSome := by
    intro t; rw [hsp.live t]; exact isSome_setParent _ _ t
  have hedge : ∀ s q, ((m.setParent m.current Option.none).setCurrent p).parentOf s
      = Option.some q → s ≠ m.current ∧ m.parentOf s = Option.some q := by
    intro s q hq
    rw [hpar] at hq
    by_cases hs : s = m.current
    · rw [if_pos hs] at hq; simp at hq
    · rw [if_neg hs] at hq; exact ⟨hs, hq⟩
  have hparentLive : ∀ s q, ((m.setParent m.current Option.none).setCurrent p).parentOf s
      = Option.some q → ((((m.setParent m.current Option.none).setCurrent p).stack? q)).isSome := by
    intro s q hq
    rw [hlive]
    exact h.parentLive s q (hedge s q hq).2
  obtain ⟨r, hdec⟩ := h.acyclic
  refine ⟨?_, hparentLive, ?_, ⟨r, ?_⟩, ?_, ?_⟩
  · rw [show ((m.setParent m.current Option.none).setCurrent p).current = p from rfl, hlive]
    exact h.parentLive _ _ hp
  · intro c s hc
    rw [show ((m.setParent m.current Option.none).setCurrent p).conts = m.conts by
      rw [conts_setCurrent, conts_setParent]] at hc
    rw [hlive]
    exact h.contLive c s hc
  · intro s q hq; exact hdec s q (hedge s q hq).2
  · intro s hps
    rw [show ((m.setParent m.current Option.none).setCurrent p).current = p from rfl] at hps
    obtain ⟨hs, hq⟩ := hedge s p hps
    exact hs (h.parentInj s m.current p hq hp)
  · intro s t q hs ht
    exact h.parentInj s t q (hedge s q hs).2 (hedge t q ht).2

/-- The intermediate state of `PERFORM`/`REPERFORMTERM`: the performer detached, still running.
It is well formed, which is what lets `REPERFORMTERM`'s second `Stack_parent` write be treated
as an attachment to a parentless stack. -/
theorem wf_detach {m : Machine ν} (h : m.WF) : (m.setParent m.current Option.none).WF := by
  have hxlive : (m.stack? m.current).isSome := h.currentLive
  have hpar : ∀ t, (m.setParent m.current Option.none).parentOf t
      = if t = m.current then Option.none else m.parentOf t := parentOf_setParent hxlive _
  have hlive : ∀ t, ((m.setParent m.current Option.none).stack? t).isSome = (m.stack? t).isSome :=
    isSome_setParent _ _
  have hedge : ∀ s q, (m.setParent m.current Option.none).parentOf s = Option.some q →
      s ≠ m.current ∧ m.parentOf s = Option.some q := by
    intro s q hq
    rw [hpar] at hq
    by_cases hs : s = m.current
    · rw [if_pos hs] at hq; simp at hq
    · rw [if_neg hs] at hq; exact ⟨hs, hq⟩
  obtain ⟨r, hdec⟩ := h.acyclic
  refine ⟨?_, ?_, ?_, ⟨r, ?_⟩, ?_, ?_⟩
  · rw [current_setParent, hlive]
    exact h.currentLive
  · intro s q hq; rw [hlive]; exact h.parentLive s q (hedge s q hq).2
  · intro c s hc
    rw [show (m.setParent m.current Option.none).conts = m.conts from conts_setParent _ _ _] at hc
    rw [hlive]
    exact h.contLive c s hc
  · intro s q hq; exact hdec s q (hedge s q hq).2
  · intro s hps
    rw [current_setParent] at hps
    exact h.noChildOfCurrent s (hedge s m.current hps).2
  · intro s t q hs ht
    exact h.parentInj s t q (hedge s q hs).2 (hedge t q ht).2

/-! ### Allocation -/

theorem stack?_snoc_lt {m : Machine ν} (info : StackInfo ν) {t : StackId}
    (h : t < m.stacks.length) :
    ({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).stack? t = m.stack? t := by
  unfold stack?
  rw [List.getElem?_append_left h]

theorem stack?_snoc_self (m : Machine ν) (info : StackInfo ν) :
    ({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).stack? m.stacks.length
      = Option.some info := by
  unfold stack?
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem stack?_snoc_gt {m : Machine ν} (info : StackInfo ν) {t : StackId}
    (h : m.stacks.length < t) :
    ({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).stack? t = Option.none := by
  unfold stack?
  rw [List.getElem?_append_right (by omega)]
  have : ([Option.some info] : List (Option (StackInfo ν)))[t - m.stacks.length]? = Option.none := by
    refine List.getElem?_eq_none ?_
    simp only [List.length_singleton]
    omega
  rw [this]

/-- **`caml_alloc_stack`** (`fiber.c:318-334`): a fresh parentless slot at the end of the heap.
Nothing points at it, no continuation names it, and it is not the running stack. Stated about any
machine with that shape of heap, so the arm lemma is one `exact`. -/
theorem wf_of_freshSlot {m m' : Machine ν} (h : m.WF)
    (hcur : m'.current = m.current) (hconts : m'.conts = m.conts)
    (hlive : ∀ t, (m'.stack? t).isSome
      = if t < m.stacks.length then (m.stack? t).isSome else decide (t = m.stacks.length))
    (hpar : ∀ t, m'.parentOf t = if t < m.stacks.length then m.parentOf t else Option.none) :
    m'.WF := by
  have hcurlt : m.current < m.stacks.length := lt_length_of_isSome h.currentLive
  have hedge : ∀ s q, m'.parentOf s = Option.some q →
      s < m.stacks.length ∧ m.parentOf s = Option.some q := by
    intro s q hq
    rw [hpar] at hq
    by_cases hs : s < m.stacks.length
    · rw [if_pos hs] at hq; exact ⟨hs, hq⟩
    · rw [if_neg hs] at hq; simp at hq
  obtain ⟨r, hdec⟩ := h.acyclic
  refine ⟨?_, ?_, ?_, ⟨r, ?_⟩, ?_, ?_⟩
  · rw [hcur, hlive, if_pos hcurlt]; exact h.currentLive
  · intro s q hq
    obtain ⟨hs, hq'⟩ := hedge s q hq
    have hqlt : q < m.stacks.length := lt_length_of_isSome (h.parentLive s q hq')
    rw [hlive, if_pos hqlt]
    exact h.parentLive s q hq'
  · intro c s hc
    rw [hconts] at hc
    have hl := h.contLive c s hc
    rw [hlive, if_pos (lt_length_of_isSome hl)]
    exact hl
  · intro s q hq; exact hdec s q (hedge s q hq).2
  · intro s hps
    rw [hcur] at hps
    exact h.noChildOfCurrent s (hedge s m.current hps).2
  · intro s t q hs ht
    exact h.parentInj s t q (hedge s q hs).2 (hedge t q ht).2

/-- The heap of `caml_alloc_stack` has that shape. -/
theorem live_snoc (m : Machine ν) (info : StackInfo ν) (t : StackId) :
    (({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).stack? t).isSome
      = if t < m.stacks.length then (m.stack? t).isSome else decide (t = m.stacks.length) := by
  by_cases hlt : t < m.stacks.length
  · rw [stack?_snoc_lt info hlt]; simp [hlt]
  · by_cases heq : t = m.stacks.length
    · subst heq; rw [stack?_snoc_self]; simp [hlt]
    · have hgt : m.stacks.length < t := by
        rcases Nat.lt_trichotomy t m.stacks.length with hc | hc | hc
        · exact absurd hc hlt
        · exact absurd hc heq
        · exact hc
      rw [stack?_snoc_gt info hgt]; simp [hlt, heq]

theorem parentOf_snoc (m : Machine ν) {info : StackInfo ν}
    (hroot : info.handler.parent = Option.none) (t : StackId) :
    ({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).parentOf t
      = if t < m.stacks.length then m.parentOf t else Option.none := by
  unfold parentOf handlerOf
  by_cases hlt : t < m.stacks.length
  · rw [stack?_snoc_lt info hlt]; simp [hlt]
  · by_cases heq : t = m.stacks.length
    · subst heq; rw [stack?_snoc_self]; simp [hlt, hroot]
    · have hgt : m.stacks.length < t := by
        rcases Nat.lt_trichotomy t m.stacks.length with hc | hc | hc
        · exact absurd hc hlt
        · exact absurd hc heq
        · exact hc
      rw [stack?_snoc_gt info hgt]; simp [hlt]

/-- The continuation heap after `PERFORM`'s `Cont_tag` allocation (`interp.c:1332`,
`cmmgen.ml:862`): one new block, pointing at the performer. -/
theorem contLive_snoc {m : Machine ν} (h : m.WF) {old : StackId}
    (holdlive : (m.stack? old).isSome) :
    ∀ (c : ContId) (s : StackId),
      (m.conts ++ [Option.some old])[c]? = Option.some (Option.some s) → (m.stack? s).isSome := by
  intro c s hc
  by_cases hlt : c < m.conts.length
  · rw [List.getElem?_append_left hlt] at hc
    exact h.contLive c s hc
  · have hge : m.conts.length ≤ c := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hc
    by_cases heq : c = m.conts.length
    · subst heq
      simp at hc
      subst hc
      exact holdlive
    · have hgt : m.conts.length < c := by
        rcases Nat.lt_or_ge m.conts.length c with hcc | hcc
        · exact hcc
        · exact absurd (Nat.le_antisymm hge hcc).symm heq
      have hnone : ([Option.some old] : List (Option StackId))[c - m.conts.length]? = Option.none := by
        refine List.getElem?_eq_none ?_
        simp only [List.length_singleton]
        exact Nat.le_sub_of_add_le (by omega)
      rw [hnone] at hc
      simp at hc

/-! ## 5. `Safe`: the runtime's calling discipline

`WF` is not preserved by `step` unconditionally, and the reason is not a defect of the machine:
it is that `OCaml5.Term` can write a primitive application that neither OCaml's type system nor
`Stdlib.Effect` can. `%resume s f v` takes *any* stack value, and the C does exactly what the
machine does — `Stack_parent(outermost) = current` with no check (`interp.c:1295-1297`), so a
`s` that is already an ancestor of the running stack makes a cycle in the runtime too, and
`caml_continuation_use_noexc`'s next walk would not terminate. The same holds for
`%runstack s f v` with a stack that already has a parent, for `%reperform e k last_fiber` with
`last_fiber` the reperforming stack itself, and for `caml_drop_continuation k` on a stack that is
still someone's parent.

`Safe m` is exactly those side conditions, one clause per redex shape. Every `OCaml5.Stdlib`
builder satisfies them by construction, because the only stack values it ever passes to a
primitive are the ones the runtime handed it: `caml_alloc_stack`'s result (`effect.ml:78`,
`:120`), `take_cont_noexc`'s result (`:57`, `:59`) and the `last_fiber` argument of an `effc`
closure (`:76`, `:88`, `:144`). -/

/-- The discipline for the three transitions that make one stack the parent of another: the
entered stack is live, has no child of its own, is not the stack we are leaving, and the stack
being attached is not already an ancestor of the running stack. -/
structure AttachSafe (m : Machine ν) (x enter : StackId) : Prop where
  enterLive : (m.stack? enter).isSome
  enterChildless : ∀ q, m.parentOf q ≠ Option.some enter
  enterNe : enter ≠ m.current
  noCycle : ¬ m.ChainReaches m.current x

/-- The discipline for `caml_drop_continuation` (`fiber.c:659-664`): the dropped stack is not
running, is nobody's parent, and no other continuation names it. -/
structure DropSafe (m : Machine ν) (cid : ContId) (sid : StackId) : Prop where
  ne : sid ≠ m.current
  childless : ∀ q, m.parentOf q ≠ Option.some sid
  unique : ∀ (c : ContId) (s : StackId),
    m.conts[c]? = Option.some (Option.some s) → s = sid → c = cid

theorem AttachSafe.congr {m m' : Machine ν} (hs : SameStacks m m') {x enter : StackId}
    (ha : AttachSafe m x enter) : AttachSafe m' x enter :=
  ⟨by rw [hs.live]; exact ha.enterLive,
    fun q hq => ha.enterChildless q (by rw [← hs.parent]; exact hq),
    by rw [hs.current]; exact ha.enterNe,
    fun hr => ha.noCycle (by rw [← hs.current] at *; exact (chainReaches_congr hs.toSameParents _ _).mp hr)⟩

theorem DropSafe.congr {m m' : Machine ν} (hs : SameHeap m m') {cid : ContId} {sid : StackId}
    (hd : DropSafe m cid sid) : DropSafe m' cid sid :=
  ⟨by rw [hs.current]; exact hd.ne,
    fun q hq => hd.childless q (by rw [← hs.parent]; exact hq),
    fun c s hc he => hd.unique c s (by rw [← hs.conts]; exact hc) he⟩

/-- The side conditions of one step, by redex shape. Anything not listed is unconditional. -/
structure Safe (m : Machine ν) : Prop where
  /-- A stack that is completing is named by no live continuation (`interp.c:576-594`,
  `:980-999`): the runtime frees it, and a `Cont_tag` block naming it would dangle. -/
  completion : m.frames = [] → ∀ (c : ContId) (s : StackId),
    m.conts[c]? = Option.some (Option.some s) → s ≠ m.current
  /-- `%resume` (`interp.c:1288-1310`). -/
  resume : ∀ (sid : StackId) (fn : Value ν) (rest : List (Frame ν)),
    m.frames = Frame.resume3 (Value.stack sid) fn :: rest → AttachSafe m (m.outermostOf sid) sid
  /-- `%runstack` (`bytegen.ml:786`, `amd64.S:958-995`). -/
  runstack : ∀ (sid : StackId) (fn : Value ν) (rest : List (Frame ν)),
    m.frames = Frame.runstack3 (Value.stack sid) fn :: rest → AttachSafe m sid sid
  /-- `%reperform` with a parent (`interp.c:1387`): `last_fiber` is the tail of the captured
  chain, never the reperforming stack itself. -/
  reperform : ∀ (e cont : Value ν) (rest : List (Frame ν)) (tail : StackId),
    m.frames = Frame.reperform3 e cont :: rest → m.control = Control.ret (Value.stack tail) →
    tail ≠ m.current
  /-- `%reperform` at the root (`interp.c:1374-1381`): the continuation it takes is resumed. -/
  reperformRoot : ∀ (e : Value ν) (cid : ContId) (rest : List (Frame ν)) (sid : StackId),
    m.frames = Frame.reperform3 e (Value.cont cid) :: rest →
    m.conts[cid]? = Option.some (Option.some sid) → AttachSafe m (m.outermostOf sid) sid
  /-- `caml_drop_continuation` (`fiber.c:659-664`). -/
  dropCont : ∀ (cid : ContId) (rest : List (Frame ν)) (sid : StackId),
    m.frames = Frame.dropContArg :: rest → m.control = Control.ret (Value.cont cid) →
    m.conts[cid]? = Option.some (Option.some sid) → DropSafe m cid sid

/-! ### The continuation heap -/

theorem contLive_set_none {m : Machine ν} (h : m.WF) (cid : ContId) :
    ∀ (c : ContId) (s : StackId),
      (m.conts.set cid Option.none)[c]? = Option.some (Option.some s) → (m.stack? s).isSome := by
  intro c s hc
  by_cases hcc : cid = c
  · subst hcc
    by_cases hlt : cid < m.conts.length
    · rw [List.getElem?_set_self hlt] at hc; simp at hc
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at hc; simp at hc
  · rw [List.getElem?_set_ne hcc] at hc
    exact h.contLive c s hc

/-- `caml_continuation_use_noexc` only ever nulls a field, so it can only shrink the set of live
continuations. -/
theorem wf_takeCont {m : Machine ν} (h : m.WF) (cid : ContId) : (m.takeCont cid).1.WF := by
  unfold takeCont
  cases hc : m.conts[cid]? with
  | none => exact h
  | some slot =>
    cases slot with
    | none => exact h
    | some sid =>
      exact h.contsWeaken ⟨⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl⟩ (contLive_set_none h cid)

theorem sameStacks_takeCont (m : Machine ν) (cid : ContId) : SameStacks m (m.takeCont cid).1 := by
  unfold takeCont
  cases hc : m.conts[cid]? with
  | none => exact SameStacks.rfl' m
  | some slot =>
    cases slot with
    | none => exact SameStacks.rfl' m
    | some sid => exact ⟨⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl⟩

theorem conts_takeCont_weaken (m : Machine ν) (cid : ContId) :
    ∀ (c : ContId) (s : StackId), (m.takeCont cid).1.conts[c]? = Option.some (Option.some s) →
      m.conts[c]? = Option.some (Option.some s) := by
  intro c s hcs
  unfold takeCont at hcs
  cases hc : m.conts[cid]? with
  | none => rw [hc] at hcs; exact hcs
  | some slot =>
    cases slot with
    | none => rw [hc] at hcs; exact hcs
    | some sid =>
      rw [hc] at hcs
      simp only at hcs
      by_cases hcc : cid = c
      · subst hcc
        by_cases hlt : cid < m.conts.length
        · rw [List.getElem?_set_self hlt] at hcs; simp at hcs
        · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at hcs; simp at hcs
      · rw [List.getElem?_set_ne hcc] at hcs; exact hcs

/-! ### The eight transitions, one lemma each -/

/-- **`PERFORM`** (`interp.c:1319-1358`, `amd64.S:877-908`). No side condition: the performer is
the running stack, which `WF` already says is live and childless. -/
theorem wf_doPerform {m m' : Machine ν} (h : m.WF) (effV : Value ν)
    (hstep : m.doPerform effV = Sum.inl m') : m'.WF := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp h.currentLive
  cases hp : info.handler.parent with
  | none =>
    simp only [doPerform, hi, hp] at hstep
    injection hstep with hstep
    subst hstep
    exact h.sameHeap (((SameHeap.rfl' m).emit _).setControl _)
  | some p =>
    have hpar : m.parentOf m.current = Option.some p := by
      unfold parentOf handlerOf; rw [hi]; exact hp
    simp only [doPerform, hi, hp] at hstep
    injection hstep with hstep
    subst hstep
    refine WF.sameHeap ?_ (((SameHeap.rfl' _).applyThree _ _ _ _).emit _)
    have hm1 : ({ m with conts := m.conts ++ [Option.some m.current] } : Machine ν).WF :=
      h.contsWeaken ⟨⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl⟩
        (contLive_snoc h h.currentLive)
    exact wf_detach_switch hm1 hpar

/-- **`do_return` with `sp == Stack_high`** (`interp.c:576-594`, `amd64.S:1003-1021`). -/
theorem wf_doReturnToParent {m : Machine ν} (h : m.WF) {p : StackId} (v : Value ν)
    (hp : m.parentOf m.current = Option.some p)
    (hcont : ∀ (c : ContId) (s : StackId),
      m.conts[c]? = Option.some (Option.some s) → s ≠ m.current) :
    (m.doReturnToParent m.current p v).WF := by
  unfold doReturnToParent
  exact WF.sameHeap (wf_free_switch h hp hcont) (((SameHeap.rfl' _).applyOne _ _).emit _)

/-- **`raise_notrace` past the last trap** (`interp.c:980-999`, `amd64.S:1022-1024`). -/
theorem wf_doRaiseToParent {m : Machine ν} (h : m.WF) {p : StackId} (e : Value ν)
    (hp : m.parentOf m.current = Option.some p)
    (hcont : ∀ (c : ContId) (s : StackId),
      m.conts[c]? = Option.some (Option.some s) → s ≠ m.current) :
    (m.doRaiseToParent m.current p e).WF := by
  unfold doRaiseToParent
  exact WF.sameHeap (wf_free_switch h hp hcont) (((SameHeap.rfl' _).applyOne _ _).emit _)

/-- **`do_resume`** (`interp.c:1288-1310`, `amd64.S:929-953`). -/
theorem wf_doResumeStack {m : Machine ν} (h : m.WF) {sid : StackId} (fn arg : Value ν)
    (ha : AttachSafe m (m.outermostOf sid) sid) : (m.doResumeStack sid fn arg).WF := by
  unfold doResumeStack
  refine WF.sameHeap ?_ (((SameHeap.rfl' _).applyOne _ _).emit _)
  exact wf_attach_enter_core h (outermost_live_parent_none h ha.enterLive).1
    ha.enterLive ha.enterChildless ha.enterNe ha.noCycle

/-- **`%resume`** (`interp.c:1279-1310`): a null stack raises and changes nothing. -/
theorem wf_doResume {m m' : Machine ν} (h : m.WF) {stackV fn arg : Value ν}
    (ha : ∀ sid, stackV = Value.stack sid → AttachSafe m (m.outermostOf sid) sid)
    (hstep : m.doResume stackV fn arg = Sum.inl m') : m'.WF := by
  cases stackV with
  | nullStack =>
    simp only [doResume] at hstep
    injection hstep with hstep
    subst hstep
    exact h.sameHeap (((SameHeap.rfl' m).setControl _).emit _)
  | stack sid =>
    simp only [doResume] at hstep
    injection hstep with hstep
    subst hstep
    exact wf_doResumeStack h fn arg (ha sid rfl)
  | base v => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | unit => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | closure e b => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | eff i p => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | exn i p => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | none => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | some w => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | cont c => simp only [doResume] at hstep; exact absurd hstep (by simp)

/-- **`%runstack`** (`bytegen.ml:786`, `amd64.S:958-995`). -/
theorem wf_doRunstack {m m' : Machine ν} (h : m.WF) {stackV fn arg : Value ν}
    (ha : ∀ sid, stackV = Value.stack sid → AttachSafe m sid sid)
    (hstep : m.doRunstack stackV fn arg = Sum.inl m') : m'.WF := by
  cases stackV with
  | nullStack =>
    simp only [doRunstack] at hstep
    injection hstep with hstep
    subst hstep
    exact h.sameHeap (((SameHeap.rfl' m).setControl _).emit _)
  | stack sid =>
    simp only [doRunstack] at hstep
    injection hstep with hstep
    subst hstep
    have hs := ha sid rfl
    refine WF.sameHeap ?_ (((SameHeap.rfl' _).applyOne _ _).emit _)
    exact wf_attach_enter_core h hs.enterLive hs.enterLive hs.enterChildless hs.enterNe hs.noCycle
  | base v => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | unit => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | closure e b => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | eff i p => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | exn i p => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | none => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | some w => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | cont c => simp only [doRunstack] at hstep; exact absurd hstep (by simp)

/-- **`caml_alloc_stack`** (`fiber.c:318-334`). -/
theorem wf_doAllocStack {m : Machine ν} (h : m.WF) (hv hx hf : Value ν) :
    (m.doAllocStack hv hx hf).WF := by
  unfold doAllocStack
  refine WF.sameHeap ?_ ((SameHeap.rfl' _).setControl _)
  exact wf_of_freshSlot h rfl rfl (live_snoc m _) (parentOf_snoc m rfl)

/-- **`REPERFORMTERM`** (`interp.c:1361-1398`, `amd64.S:911-925`). Two routes: with a parent the
reperforming stack is detached and appended to the captured chain (`:1387`); at the root the
continuation is taken and resumed with a function that raises `Unhandled` (`:1374-1381`). -/
theorem wf_doReperform {m m' : Machine ν} (h : m.WF) {effV contV lastV : Value ν}
    (hroot : ∀ (cid sid : StackId), contV = Value.cont cid →
      m.conts[cid]? = Option.some (Option.some sid) → AttachSafe m (m.outermostOf sid) sid)
    (htail : ∀ tail, lastV = Value.stack tail → tail ≠ m.current)
    (hstep : m.doReperform effV contV lastV = Sum.inl m') : m'.WF := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp h.currentLive
  cases hp : info.handler.parent with
  | none =>
    -- the root route
    cases contV with
    | cont cid =>
      cases hc : m.conts[cid]? with
      | none =>
        simp only [doReperform, hi, hp, takeCont, hc] at hstep
        injection hstep with hstep
        subst hstep
        exact h.sameHeap (((SameHeap.rfl' m).setControl _).emit _)
      | some slot =>
        cases slot with
        | none =>
          simp only [doReperform, hi, hp, takeCont, hc] at hstep
          injection hstep with hstep
          subst hstep
          exact h.sameHeap (((SameHeap.rfl' m).setControl _).emit _)
        | some sid =>
          simp only [doReperform, hi, hp, takeCont, hc] at hstep
          injection hstep with hstep
          subst hstep
          have hm1 : ({ m with conts := m.conts.set cid Option.none } : Machine ν).WF :=
            h.contsWeaken ⟨⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl⟩ (contLive_set_none h cid)
          have hss : SameStacks m
              (({ m with conts := m.conts.set cid Option.none } : Machine ν).emit
                (Event.unhandled effV.effIdOf)) :=
            ⟨⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl⟩
          have hm2 : (({ m with conts := m.conts.set cid Option.none } : Machine ν).emit
              (Event.unhandled effV.effIdOf)).WF :=
            hm1.sameHeap (((SameHeap.rfl' _).emit _))
          have hout := outermostOf_congr hss.toSameParents sid
          refine wf_doResumeStack hm2 _ _ ?_
          rw [hout]
          exact (hroot cid sid rfl hc).congr hss
    | base v => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | unit => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | closure e b => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | eff i q => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | exn i q => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | none => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | some w => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | stack s => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | nullStack => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
  | some p =>
    have hpar : m.parentOf m.current = Option.some p := by
      unfold parentOf handlerOf; rw [hi]; exact hp
    cases lastV with
    | stack tail =>
      simp only [doReperform, hi, hp] at hstep
      injection hstep with hstep
      subst hstep
      refine WF.sameHeap ?_ (((SameHeap.rfl' _).applyThree _ _ _ _).emit _)
      -- `md` is the reperforming stack, detached: `Stack_parent(self) = NULL` (`interp.c:1386`)
      have hmd : (m.setParent m.current Option.none).WF := wf_detach h
      have hmdcur : (m.setParent m.current Option.none).current = m.current := current_setParent _ _ _
      have hmdpar : ∀ t, (m.setParent m.current Option.none).parentOf t
          = if t = m.current then Option.none else m.parentOf t :=
        parentOf_setParent h.currentLive _
      have hmdlive : ∀ t, ((m.setParent m.current Option.none).stack? t).isSome
          = (m.stack? t).isSome := isSome_setParent _ _
      have htne : tail ≠ m.current := htail tail rfl
      by_cases hlive : ((m.setParent m.current Option.none).stack? tail).isSome
      · refine wf_attach_enter_core' hmd hmdcur.symm hlive ?_ ?_ ?_ ?_
        · rw [hmdlive]; exact h.parentLive _ _ hpar
        · intro q hq
          rw [hmdpar] at hq
          by_cases hqc : q = m.current
          · rw [if_pos hqc] at hq; simp at hq
          · rw [if_neg hqc] at hq
            exact hqc (h.parentInj q m.current p hq hpar)
        · rw [hmdcur]; exact parent_ne_self h hpar
        · intro hr
          rw [hmdcur] at hr
          have hroot' : (m.setParent m.current Option.none).parentOf m.current = Option.none := by
            rw [hmdpar]; simp
          exact htne (chainReaches_root hroot' hr)
      · -- a dead `last_fiber`: `Stack_parent(last_fiber) = self` writes nothing
        have hnone : (m.setParent m.current Option.none).stack? tail = Option.none := by
          cases hst : (m.setParent m.current Option.none).stack? tail with
          | none => rfl
          | some i => rw [hst] at hlive; exact absurd hlive (by simp)
        have hid : (m.setParent m.current Option.none).setParent tail
            (Option.some m.current) = m.setParent m.current Option.none :=
          setParent_of_dead hnone _
        rw [hid]
        exact wf_detach_switch h hpar
    | base v => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | unit => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | closure e b => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | eff i q => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | exn i q => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | none => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | some w => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | cont c => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)
    | nullStack => simp only [doReperform, hi, hp] at hstep; exact absurd hstep (by simp)

/-- **`caml_drop_continuation`** (`fiber.c:659-664`): `caml_continuation_use` (so a taken handle
raises) then `caml_free_stack`. No handler of the dropped stack runs. -/
theorem wf_doDropCont {m m' : Machine ν} (h : m.WF) {contV : Value ν}
    (hd : ∀ (cid sid : StackId), contV = Value.cont cid →
      m.conts[cid]? = Option.some (Option.some sid) → DropSafe m cid sid)
    (hstep : m.doDropCont contV = Sum.inl m') : m'.WF := by
  cases contV with
  | cont cid =>
    cases hc : m.conts[cid]? with
    | none =>
      simp only [doDropCont, takeCont, hc] at hstep
      injection hstep with hstep
      subst hstep
      exact h.sameHeap (((SameHeap.rfl' m).setControl _).emit _)
    | some slot =>
      cases slot with
      | none =>
        simp only [doDropCont, takeCont, hc] at hstep
        injection hstep with hstep
        subst hstep
        exact h.sameHeap (((SameHeap.rfl' m).setControl _).emit _)
      | some sid =>
        simp only [doDropCont, takeCont, hc] at hstep
        injection hstep with hstep
        subst hstep
        have hsafe := hd cid sid rfl hc
        have hm1 : ({ m with conts := m.conts.set cid Option.none } : Machine ν).WF :=
          h.contsWeaken ⟨⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl⟩ (contLive_set_none h cid)
        refine WF.sameHeap ?_ (((SameHeap.rfl' _).emit _).setControl _)
        refine wf_freeStack hm1 hsafe.ne hsafe.childless ?_
        intro c s hcs
        have hcid : c ≠ cid := by
          intro hcc
          subst hcc
          by_cases hlt : c < m.conts.length
          · rw [show ({ m with conts := m.conts.set c Option.none } : Machine ν).conts
              = m.conts.set c Option.none from rfl, List.getElem?_set_self hlt] at hcs
            simp at hcs
          · rw [show ({ m with conts := m.conts.set c Option.none } : Machine ν).conts
              = m.conts.set c Option.none from rfl,
              List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at hcs
            simp at hcs
        rw [show ({ m with conts := m.conts.set cid Option.none } : Machine ν).conts
          = m.conts.set cid Option.none from rfl, List.getElem?_set_ne (Ne.symm hcid)] at hcs
        intro hssid
        exact hcid (hsafe.unique c s hcs hssid)
  | base v => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | unit => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | closure e b => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | eff i q => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | exn i q => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | none => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | some w => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | stack s => simp only [doDropCont] at hstep; exact absurd hstep (by simp)
  | nullStack => simp only [doDropCont] at hstep; exact absurd hstep (by simp)

/-! ## 6. `step_wf`

The arms, assembled. `stepEval` never touches the heap (§4); `stepRet` and `stepThrow` are the
frame arms — which only change the current stack's frames, the control, the trace and the cell —
plus the eight transitions, each of which has its lemma above. -/

theorem stepThrow_wf [ToString ν] {m m' : Machine ν} (h : m.WF) (hsafe : m.Safe) {e : Value ν}
    (hstep : m.stepThrow e = Sum.inl m') : m'.WF := by
  cases hf : m.frames with
  | nil =>
    obtain ⟨info, hi⟩ := isSome_iff_exists.mp h.currentLive
    cases hp : info.handler.parent with
    | none =>
      simp only [stepThrow, hf, hi, hp] at hstep
      exact absurd hstep (by simp)
    | some p =>
      have hpar : m.parentOf m.current = Option.some p := by
        unfold parentOf handlerOf; rw [hi]; exact hp
      simp only [stepThrow, hf, hi, hp] at hstep
      injection hstep with hstep
      subst hstep
      exact wf_doRaiseToParent h e hpar (hsafe.completion hf)
  | cons f rest =>
    have hwf0 : (m.withFrames rest).WF := h.sameHeap ((SameHeap.rfl' m).withFrames rest)
    cases f <;>
      simp only [stepThrow, hf] at hstep <;>
      injection hstep with hstep <;>
      subst hstep <;>
      first
        | exact hwf0.sameHeap ((SameHeap.rfl' _).setControl _)
        | exact hwf0.sameHeap (((SameHeap.rfl' _).emit _).setControl _)

theorem stepRet_wf [ToString ν] [Add ν] {m m' : Machine ν} (h : m.WF) (hsafe : m.Safe)
    {v : Value ν} (hcontrol : m.control = Control.ret v)
    (hstep : m.stepRet v = Sum.inl m') : m'.WF := by
  cases hf : m.frames with
  | nil =>
    obtain ⟨info, hi⟩ := isSome_iff_exists.mp h.currentLive
    cases hp : info.handler.parent with
    | none =>
      simp only [stepRet, hf, hi, hp] at hstep
      exact absurd hstep (by simp)
    | some p =>
      have hpar : m.parentOf m.current = Option.some p := by
        unfold parentOf handlerOf; rw [hi]; exact hp
      simp only [stepRet, hf, hi, hp] at hstep
      injection hstep with hstep
      subst hstep
      exact wf_doReturnToParent h v hpar (hsafe.completion hf)
  | cons f rest =>
    have hsh0 : SameHeap m (m.withFrames rest) := (SameHeap.rfl' m).withFrames rest
    have hwf0 : (m.withFrames rest).WF := h.sameHeap hsh0
    have hss0 : SameStacks m (m.withFrames rest) := hsh0.toSameStacks
    cases f
    case performArg =>
      simp only [stepRet, hf] at hstep
      exact wf_doPerform hwf0 v hstep
    case resume3 stackV fn =>
      simp only [stepRet, hf] at hstep
      refine wf_doResume hwf0 ?_ hstep
      intro sid hsv
      subst hsv
      have := hsafe.resume sid fn rest hf
      rw [outermostOf_congr hss0.toSameParents sid]
      exact this.congr hss0
    case runstack3 stackV fn =>
      simp only [stepRet, hf] at hstep
      refine wf_doRunstack hwf0 ?_ hstep
      intro sid hsv
      subst hsv
      exact (hsafe.runstack sid fn rest hf).congr hss0
    case reperform3 e cont =>
      simp only [stepRet, hf] at hstep
      refine wf_doReperform hwf0 ?_ ?_ hstep
      · intro cid sid hcv hcs
        subst hcv
        rw [outermostOf_congr hss0.toSameParents sid]
        refine (hsafe.reperformRoot e cid rest sid hf ?_).congr hss0
        rw [← hsh0.conts]
        exact hcs
      · intro tail hlv
        subst hlv
        rw [hss0.current]
        exact hsafe.reperform e cont rest tail hf hcontrol
    case allocStack3 hv hx =>
      simp only [stepRet, hf] at hstep
      injection hstep with hstep
      subst hstep
      exact wf_doAllocStack hwf0 hv hx v
    case dropContArg =>
      simp only [stepRet, hf] at hstep
      refine wf_doDropCont hwf0 ?_ hstep
      intro cid sid hcv hcs
      subst hcv
      refine (hsafe.dropCont cid rest sid hf hcontrol ?_).congr hsh0
      rw [← hsh0.conts]
      exact hcs
    all_goals
      simp only [stepRet, hf, applyValue, takeContUpdate] at hstep
    all_goals repeat' split at hstep
    all_goals
      first
        | (injection hstep with hstep
           subst hstep
           first
             | exact hwf0.sameHeap (SameHeap.rfl' _)
             | exact hwf0.sameHeap ((SameHeap.rfl' _).setControl _)
             | exact hwf0.sameHeap (((SameHeap.rfl' _).pushFrame _).setControl _)
             | exact hwf0.sameHeap (((SameHeap.rfl' _).emit _).setControl _)
             | exact hwf0.sameHeap (((SameHeap.rfl' _).setCell _).setControl _)
             | exact (wf_takeCont hwf0 _).sameHeap (((SameHeap.rfl' _).emit _).setControl _)
             | exact (wf_takeCont hwf0 _).sameHeap ((SameHeap.rfl' _).setControl _)
             | exact ((wf_takeCont hwf0 _).sameHeap
                 ((SameHeap.rfl' _).triple _ _ _ _)).sameHeap
                 (((SameHeap.rfl' _).emit _).setControl _)
             | exact ((wf_takeCont hwf0 _).sameHeap
                 ((SameHeap.rfl' _).triple _ _ _ _)).sameHeap
                 ((SameHeap.rfl' _).setControl _))
        | exact absurd hstep (by simp)

/-- **Evaluating a term never touches the heap.** Every arm of `stepEval` pushes a frame, emits
a row, reads or writes the one mutable cell, or sets the control; none of them is one of the
eight transitions. -/
theorem stepEval_sameHeap [ToString ν] {m m' : Machine ν} {env : List (Value ν)} {t : Term ν}
    (h : m.stepEval env t = Sum.inl m') : SameHeap m m' := by
  cases t
  case var i =>
    cases hv : env[i]? with
    | none => rw [stepEval, hv] at h; exact absurd h (by simp)
    | some v =>
      rw [stepEval, hv] at h
      injection h with h
      subst h
      exact (SameHeap.rfl' m).setControl _
  all_goals (injection h with h; subst h)
  all_goals first
    | exact (SameHeap.rfl' m).setControl _
    | exact ((SameHeap.rfl' m).pushFrame _).setControl _
    | exact ((SameHeap.rfl' m).emit _).setControl _
    | exact (((SameHeap.rfl' m).pushFrame _).emit _).setControl _

/-- **`WF` is preserved by `step`.** The eight transitions of the plan's §0 table, the trap arms
and the evaluation arms, exhaustively. The side conditions are `Safe` (§5): what the runtime's
own calling discipline guarantees about a primitive's stack arguments. -/
theorem step_wf [ToString ν] [Add ν] {m m' : Machine ν} (h : m.WF) (hsafe : m.Safe)
    (hstep : m.step = Sum.inl m') : m'.WF := by
  unfold step at hstep
  cases hc : m.control with
  | eval env t => rw [hc] at hstep; exact h.sameHeap (stepEval_sameHeap hstep)
  | ret v => rw [hc] at hstep; exact stepRet_wf h hsafe hc hstep
  | throw e => rw [hc] at hstep; exact stepThrow_wf h hsafe hstep

/-- The initial machine of a closed term is well formed: one live root stack, no parent, no
continuations (`caml_alloc_main_stack`, `fiber.c:550`). -/
theorem wf_start (t : Term ν) : (Machine.start t).WF := by
  refine ⟨?_, ?_, ?_, ⟨fun _ => 0, ?_⟩, ?_, ?_⟩
  · rfl
  · intro s p hp; exact absurd hp (by cases s <;> simp [start, parentOf, handlerOf, stack?])
  · intro c s hc; exact absurd hc (by simp [start])
  · intro s p hp; exact absurd hp (by cases s <;> simp [start, parentOf, handlerOf, stack?])
  · intro s hp; exact absurd hp (by cases s <;> simp [start, parentOf, handlerOf, stack?])
  · intro s t p hs ht; exact absurd hs (by cases s <;> simp [start, parentOf, handlerOf, stack?])

/-! ## 7. `Reaches`: the induction principle over `run`

`run` is fuel-bounded, so a property of a run's final machine is a property of a machine the
initial one reaches. `Reaches` is the reflexive-transitive closure of one `step`, and
`reaches_induction` is the induction principle O1's report §5 asks for: anything preserved by one
step holds of everything the machine reaches, `run`'s answer included. -/

/-- `m` reaches `m'` in zero or more `step`s. -/
inductive Reaches [ToString ν] [Add ν] : Machine ν → Machine ν → Prop
  | refl (m : Machine ν) : Reaches m m
  | tail {m m' m'' : Machine ν} : Reaches m m' → m'.step = Sum.inl m'' → Reaches m m''

theorem Reaches.head [ToString ν] [Add ν] {m m' m'' : Machine ν}
    (h : m.step = Sum.inl m') (hr : Reaches m' m'') : Reaches m m'' := by
  induction hr with
  | refl => exact Reaches.tail (Reaches.refl m) h
  | tail _ hs ih => exact Reaches.tail ih hs

theorem Reaches.trans [ToString ν] [Add ν] {a b c : Machine ν}
    (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact Reaches.tail ih hs

/-- **The induction principle.** A property preserved by one `step` holds of every machine
reached. -/
theorem reaches_induction [ToString ν] [Add ν] {P : Machine ν → Prop}
    (hstep : ∀ a b, P a → a.step = Sum.inl b → P b) {m m' : Machine ν}
    (hr : Reaches m m') (hm : P m) : P m' := by
  induction hr with
  | refl => exact hm
  | tail _ hs ih => exact hstep _ _ ih hs

/-- `run` only ever answers about a machine the initial one reaches. -/
theorem run_reaches [ToString ν] [Add ν] : ∀ (n : Nat) (m : Machine ν),
    Reaches m (Machine.run n m).1 := by
  intro n
  induction n with
  | zero => intro m; exact Reaches.refl m
  | succ k ih =>
    intro m
    cases hs : m.step with
    | inl m1 =>
      have : Machine.run (k + 1) m = Machine.run k m1 := by simp [run, hs]
      rw [this]
      exact Reaches.head hs (ih m1)
    | inr o =>
      have : Machine.run (k + 1) m = (m, o) := by simp [run, hs]
      rw [this]
      exact Reaches.refl m

/-- **`run_ind`**: a property of every machine of a run, from a step-level fact. This is the form
O1's report §5 names as the missing infrastructure. -/
theorem run_ind [ToString ν] [Add ν] {P : Machine ν → Prop}
    (hstep : ∀ a b, P a → a.step = Sum.inl b → P b) (n : Nat) (m : Machine ν) (hm : P m) :
    P (Machine.run n m).1 :=
  reaches_induction hstep (run_reaches n m) hm

/-- **`WF` along a whole run**, provided the discipline holds at every state reached. -/
theorem run_wf [ToString ν] [Add ν] {m : Machine ν} (h : m.WF)
    (hsafe : ∀ a, Reaches m a → a.Safe) (n : Nat) : (Machine.run n m).1.WF := by
  have key : ∀ a b, (Reaches m a ∧ a.WF) → a.step = Sum.inl b → (Reaches m b ∧ b.WF) := by
    rintro a b ⟨hra, hwa⟩ hs
    exact ⟨Reaches.tail hra hs, step_wf hwa (hsafe a hra) hs⟩
  exact (run_ind key n m ⟨Reaches.refl m, h⟩).2

/-! ## 8. Traps survive capture

The frames of a stack — traps included, since `PUSHTRAP` pushes on the stack it runs on
(`interp.c:930-938`, ruling 5 of the plan) — are touched by exactly one machine operation,
`withFrames`, and only on the running stack. `StableOff sid m m'` records that: `sid`'s frames
are what they were, or `sid` has been freed. -/

/-- `sid`'s frames are unchanged, or `sid` is gone. A structure, not a bare disjunction, so
unification never unfolds it while a proof search tries an alternative. -/
structure StableOff (sid : StackId) (m m' : Machine ν) : Prop where
  keep : (m'.stack? sid).map (·.frames) = (m.stack? sid).map (·.frames) ∨ m'.stack? sid = Option.none
  /-- The stack heap never shrinks: `caml_free_stack` empties a slot, it does not remove it, and
  `caml_alloc_stack` appends. So a slot that has ever been allocated keeps its index. -/
  len : m.stacks.length ≤ m'.stacks.length

theorem StableOff.rfl' (sid : StackId) (m : Machine ν) : StableOff sid m m :=
  ⟨Or.inl rfl, Nat.le_refl _⟩

theorem StableOff.trans {sid : StackId} {a b c : Machine ν}
    (h1 : StableOff sid a b) (h2 : StableOff sid b c) : StableOff sid a c := by
  refine ⟨?_, Nat.le_trans h1.len h2.len⟩
  rcases h2.keep with h2 | h2
  · rcases h1.keep with h1 | h1
    · exact Or.inl (by rw [h2, h1])
    · exact Or.inr (by rw [h1] at h2; simpa using h2)
  · exact Or.inr h2

theorem StableOff.setControl {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (c : Control ν) : StableOff sid m (a.setControl c) := ⟨h.keep, h.len⟩

theorem StableOff.emit {sid : StackId} {m a : Machine ν} (h : StableOff sid m a) (e : Event) :
    StableOff sid m (a.emit e) := ⟨h.keep, h.len⟩

theorem StableOff.setCell {sid : StackId} {m a : Machine ν} (h : StableOff sid m a) (v : Value ν) :
    StableOff sid m ({ a with cell := v } : Machine ν) := ⟨h.keep, h.len⟩

theorem StableOff.setCurrent {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (s : StackId) : StableOff sid m (a.setCurrent s) := ⟨h.keep, h.len⟩

theorem StableOff.conts {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (cs : List (Option StackId)) : StableOff sid m ({ a with conts := cs } : Machine ν) :=
  ⟨h.keep, h.len⟩

/-- The one operation that changes frames, and it changes only the running stack's. -/
theorem StableOff.withFrames {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (hne : a.current ≠ sid) (fs : List (Frame ν)) : StableOff sid m (a.withFrames fs) :=
  h.trans ⟨Or.inl (by rw [stack?_withFrames_ne fs hne]), by rw [stacks_length_withFrames]; exact Nat.le_refl _⟩

theorem StableOff.pushFrame {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (hne : a.current ≠ sid) (f : Frame ν) : StableOff sid m (a.pushFrame f) :=
  h.withFrames hne _

theorem StableOff.applyOne {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (hne : a.current ≠ sid) (f v : Value ν) : StableOff sid m (a.applyOne f v) :=
  (h.pushFrame hne _).setControl _

theorem StableOff.applyThree {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (hne : a.current ≠ sid) (f x y z : Value ν) : StableOff sid m (a.applyThree f x y z) :=
  (h.withFrames hne _).setControl _

/-- Re-parenting never moves a frame (`fiber.h:43-49`: `frames` and `handler` are separate
fields). -/
theorem StableOff.setParent {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (x : StackId) (p : Option StackId) : StableOff sid m (a.setParent x p) := by
  refine h.trans ⟨Or.inl ?_, by rw [stacks_length_setParent]; exact Nat.le_refl _⟩
  by_cases hx : x = sid
  · subst hx
    cases hst : a.stack? x with
    | none => rw [setParent_of_dead hst, hst]
    | some info => rw [stack?_setParent_self p hst]; simp
  · rw [stack?_setParent_ne p hx]

theorem StableOff.setTriple {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (x : StackId) (hv hx hf : Value ν) : StableOff sid m (a.setTriple x hv hx hf) := by
  refine h.trans ⟨Or.inl ?_, by rw [stacks_length_setTriple]; exact Nat.le_refl _⟩
  unfold Machine.setTriple
  cases hst : a.stack? x with
  | none => rfl
  | some info =>
    by_cases hxs : x = sid
    · subst hxs
      rw [stack?_setStack_self _ hst]; simp [hst]
    · rw [stack?_setStack_ne _ hxs]

theorem StableOff.freeStack {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (x : StackId) : StableOff sid m (a.freeStack x) := by
  by_cases hx : x = sid
  · subst hx
    exact ⟨Or.inr (stack?_freeStack a x), by rw [stacks_length_freeStack]; exact h.len⟩
  · exact h.trans ⟨Or.inl (by rw [stack?_freeStack_ne hx]),
      by rw [stacks_length_freeStack]; exact Nat.le_refl _⟩

theorem StableOff.snoc {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (hlt : sid < a.stacks.length) (info : StackInfo ν) :
    StableOff sid m ({ a with stacks := a.stacks ++ [Option.some info] } : Machine ν) :=
  h.trans ⟨Or.inl (by rw [stack?_snoc_lt info hlt]), by simp⟩

theorem StableOff.takeCont {sid : StackId} {m a : Machine ν} (h : StableOff sid m a)
    (cid : ContId) : StableOff sid m (a.takeCont cid).1 := by
  unfold Machine.takeCont
  cases hc : a.conts[cid]? with
  | none => exact ⟨h.keep, h.len⟩
  | some slot => cases slot with
    | none => exact ⟨h.keep, h.len⟩
    | some s => exact ⟨h.keep, h.len⟩

/-! ### Only the running stack's frames move

`step_stableOff` is the arm-by-arm statement: a step changes the frames of `m.current` and of
`m'.current` and of no other stack. It is the *quiescence* lemma the avatar simulation needs —
the machine's one `control` field belongs to the running stack, and every other live stack is
parked, its whole continuation sitting in its frame list, untouched. -/

theorem stableOff_current (m : Machine ν) (fs : List (Frame ν)) (sid : StackId)
    (hne : m.current ≠ sid) : StableOff sid m (m.withFrames fs) :=
  (StableOff.rfl' sid m).withFrames hne fs

/-- `%resume`, `%runstack` and the `reperform` root route. -/
theorem stableOff_doResumeStack {m : Machine ν} {sid s : StackId} (fn arg : Value ν)
    (_h1 : m.current ≠ s) (h2 : sid ≠ s) : StableOff s m (m.doResumeStack sid fn arg) := by
  unfold doResumeStack
  refine (((StableOff.rfl' s m).setParent _ _).setCurrent sid).applyOne ?_ fn arg |>.emit _
  exact h2

theorem stableOff_doResume {m m' : Machine ν} {s : StackId} {stackV fn arg : Value ν}
    (h1 : m.current ≠ s) (h2 : m'.current ≠ s)
    (hstep : m.doResume stackV fn arg = Sum.inl m') : StableOff s m m' := by
  cases stackV with
  | stack sid =>
    simp only [doResume] at hstep
    injection hstep with hstep
    subst hstep
    refine stableOff_doResumeStack fn arg h1 ?_
    simpa only [doResumeStack, current_emit, current_applyOne, current_setCurrent] using h2
  | nullStack =>
    simp only [doResume] at hstep; injection hstep with hstep; subst hstep
    exact ((StableOff.rfl' s m).setControl _).emit _
  | base v => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | unit => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | closure e b => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | eff i p => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | exn i p => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | none => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | some w => simp only [doResume] at hstep; exact absurd hstep (by simp)
  | cont c => simp only [doResume] at hstep; exact absurd hstep (by simp)

theorem stableOff_doRunstack {m m' : Machine ν} {s : StackId} {stackV fn arg : Value ν}
    (_h1 : m.current ≠ s) (h2 : m'.current ≠ s)
    (hstep : m.doRunstack stackV fn arg = Sum.inl m') : StableOff s m m' := by
  cases stackV with
  | stack sid =>
    simp only [doRunstack] at hstep
    injection hstep with hstep
    subst hstep
    have hsid : sid ≠ s := by
      simpa only [current_emit, current_applyOne, current_setCurrent] using h2
    exact ((((StableOff.rfl' s m).setParent _ _).setCurrent sid).applyOne hsid fn arg).emit _
  | nullStack =>
    simp only [doRunstack] at hstep; injection hstep with hstep; subst hstep
    exact ((StableOff.rfl' s m).setControl _).emit _
  | base v => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | unit => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | closure e b => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | eff i p => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | exn i p => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | none => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | some w => simp only [doRunstack] at hstep; exact absurd hstep (by simp)
  | cont c => simp only [doRunstack] at hstep; exact absurd hstep (by simp)

theorem stableOff_doPerform {m m' : Machine ν} {s : StackId} {effV : Value ν}
    (_h1 : m.current ≠ s) (h2 : m'.current ≠ s)
    (hstep : m.doPerform effV = Sum.inl m') : StableOff s m m' := by
  cases hi : m.stack? m.current with
  | none => simp only [doPerform, hi] at hstep; exact absurd hstep (by simp)
  | some info =>
    cases hp : info.handler.parent with
    | none =>
      simp only [doPerform, hi, hp] at hstep; injection hstep with hstep; subst hstep
      exact ((StableOff.rfl' s m).emit _).setControl _
    | some p =>
      simp only [doPerform, hi, hp] at hstep; injection hstep with hstep; subst hstep
      have hpne : p ≠ s := by
        simpa only [current_emit, current_applyThree, current_setCurrent] using h2
      exact (((((StableOff.rfl' s m).conts _).setParent _ _).setCurrent p).applyThree hpne
        _ _ _ _).emit _

theorem stableOff_doReperform {m m' : Machine ν} {s : StackId} {effV contV lastV : Value ν}
    (h1 : m.current ≠ s) (h2 : m'.current ≠ s)
    (hstep : m.doReperform effV contV lastV = Sum.inl m') : StableOff s m m' := by
  cases hi : m.stack? m.current with
  | none => simp only [doReperform, hi] at hstep; exact absurd hstep (by simp)
  | some info =>
    cases hp : info.handler.parent with
    | none =>
      cases contV <;> simp only [doReperform, hi, hp] at hstep
      case cont cid =>
        have hcur : ((m.takeCont cid).1.emit (Event.unhandled effV.effIdOf)).current = m.current :=
          (sameStacks_takeCont m cid).current
        split at hstep
        · injection hstep with hstep
          subst hstep
          refine StableOff.trans
            (((StableOff.rfl' s m).takeCont cid).emit (Event.unhandled effV.effIdOf)) ?_
          refine stableOff_doResumeStack _ _ (by rw [hcur]; exact h1) ?_
          simpa only [doResumeStack, current_emit, current_applyOne, current_setCurrent] using h2
        · injection hstep with hstep
          subst hstep
          exact (((StableOff.rfl' s m).takeCont cid).setControl _).emit _
      all_goals exact absurd hstep (by simp)
    | some p =>
      cases lastV <;> simp only [doReperform, hi, hp] at hstep
      case stack tail =>
        injection hstep with hstep
        subst hstep
        have hpne : p ≠ s := by
          simpa only [current_emit, current_applyThree, current_setCurrent] using h2
        exact (((((StableOff.rfl' s m).setParent _ _).setParent _ _).setCurrent p).applyThree
          hpne _ _ _ _).emit _
      all_goals exact absurd hstep (by simp)

theorem stableOff_doDropCont {m m' : Machine ν} {s : StackId} {contV : Value ν}
    (hstep : m.doDropCont contV = Sum.inl m') : StableOff s m m' := by
  cases contV <;> simp only [doDropCont] at hstep
  case cont cid =>
    split at hstep
    · injection hstep with hstep
      subst hstep
      exact ((((StableOff.rfl' s m).takeCont cid).freeStack _).emit _).setControl _
    · injection hstep with hstep
      subst hstep
      exact (((StableOff.rfl' s m).takeCont cid).setControl _).emit _
  all_goals exact absurd hstep (by simp)

theorem stableOff_stepEval [ToString ν] {m m' : Machine ν} {s : StackId}
    {env : List (Value ν)} {t : Term ν} (h1 : m.current ≠ s)
    (hstep : m.stepEval env t = Sum.inl m') : StableOff s m m' := by
  cases t
  case var i =>
    cases hv : env[i]? with
    | none => rw [stepEval, hv] at hstep; exact absurd hstep (by simp)
    | some v =>
      rw [stepEval, hv] at hstep
      injection hstep with hstep
      subst hstep
      exact (StableOff.rfl' s m).setControl _
  all_goals (injection hstep with hstep; subst hstep)
  all_goals first
    | exact (StableOff.rfl' s m).setControl _
    | exact ((StableOff.rfl' s m).pushFrame h1 _).setControl _
    | exact ((StableOff.rfl' s m).emit _).setControl _
    | exact (((StableOff.rfl' s m).pushFrame h1 _).emit _).setControl _

/-- **Quiescence, one step.** A `step` changes the frames of the stack it runs on and of the
stack it switches to, and of no other stack: every other live stack is parked, and its whole
continuation — traps included — sits unchanged in its frame list. -/
theorem step_stableOff [ToString ν] [Add ν] {m m' : Machine ν} {s : StackId}
    (hslt : s < m.stacks.length) (h1 : m.current ≠ s) (h2 : m'.current ≠ s)
    (hstep : m.step = Sum.inl m') : StableOff s m m' := by
  unfold step at hstep
  cases hc : m.control with
  | eval env t => rw [hc] at hstep; exact stableOff_stepEval h1 hstep
  | throw e =>
    rw [hc] at hstep
    cases hf : m.frames with
    | nil =>
      cases hi : m.stack? m.current with
      | none => simp only [stepThrow, hf, hi] at hstep; exact absurd hstep (by simp)
      | some info =>
        cases hp : info.handler.parent with
        | none => simp only [stepThrow, hf, hi, hp] at hstep; exact absurd hstep (by simp)
        | some p =>
          simp only [stepThrow, hf, hi, hp] at hstep
          injection hstep with hstep
          subst hstep
          have hpne : p ≠ s := by
            simpa only [doRaiseToParent, current_emit, current_applyOne, current_setCurrent]
              using h2
          exact ((((StableOff.rfl' s m).freeStack _).setCurrent p).applyOne hpne _ _).emit _
    | cons f rest =>
      have h0 : (m.withFrames rest).current ≠ s := by rw [current_withFrames]; exact h1
      cases f <;>
        simp only [stepThrow, hf] at hstep <;>
        injection hstep with hstep <;>
        subst hstep <;>
        first
          | exact (stableOff_current m rest s h1).setControl _
          | exact ((stableOff_current m rest s h1).emit _).setControl _
  | ret v =>
    rw [hc] at hstep
    cases hf : m.frames with
    | nil =>
      cases hi : m.stack? m.current with
      | none => simp only [stepRet, hf, hi] at hstep; exact absurd hstep (by simp)
      | some info =>
        cases hp : info.handler.parent with
        | none => simp only [stepRet, hf, hi, hp] at hstep; exact absurd hstep (by simp)
        | some p =>
          simp only [stepRet, hf, hi, hp] at hstep
          injection hstep with hstep
          subst hstep
          have hpne : p ≠ s := by
            simpa only [doReturnToParent, current_emit, current_applyOne, current_setCurrent]
              using h2
          exact ((((StableOff.rfl' s m).freeStack _).setCurrent p).applyOne hpne _ _).emit _
    | cons f rest =>
      have h0 : (m.withFrames rest).current ≠ s := by rw [current_withFrames]; exact h1
      have hbase : StableOff s m (m.withFrames rest) := stableOff_current m rest s h1
      have hslt0 : s < (m.withFrames rest).stacks.length := by
        rw [stacks_length_withFrames]; exact hslt
      cases f
      case performArg =>
        simp only [stepRet, hf] at hstep
        exact hbase.trans (stableOff_doPerform h0 h2 hstep)
      case resume3 stackV fn =>
        simp only [stepRet, hf] at hstep
        exact hbase.trans (stableOff_doResume h0 h2 hstep)
      case runstack3 stackV fn =>
        simp only [stepRet, hf] at hstep
        exact hbase.trans (stableOff_doRunstack h0 h2 hstep)
      case reperform3 e cont =>
        simp only [stepRet, hf] at hstep
        exact hbase.trans (stableOff_doReperform h0 h2 hstep)
      case dropContArg =>
        simp only [stepRet, hf] at hstep
        exact hbase.trans (stableOff_doDropCont hstep)
      case allocStack3 hv hx =>
        simp only [stepRet, hf] at hstep
        injection hstep with hstep
        subst hstep
        exact ((hbase.snoc hslt0 _).setControl _)
      all_goals
        simp only [stepRet, hf, applyValue, takeContUpdate] at hstep
      all_goals repeat' split at hstep
      all_goals
        first
          | (injection hstep with hstep
             subst hstep
             first
               | exact hbase
               | exact hbase.setControl _
               | exact (hbase.pushFrame h0 _).setControl _
               | exact (hbase.emit _).setControl _
               | exact (hbase.setCell _).setControl _
               | exact ((hbase.takeCont _).emit _).setControl _
               | exact (hbase.takeCont _).setControl _
               | exact (((hbase.takeCont _).setTriple _ _ _ _).emit _).setControl _
               | exact ((hbase.takeCont _).setTriple _ _ _ _).setControl _)
          | exact absurd hstep (by simp)

/-! ## 9. One-shot, at run level

The continuation heap only ever grows at the end (`PERFORM` allocates one `Cont_tag` block,
`interp.c:1332`) and is only ever written by nulling a field
(`caml_continuation_use_noexc`, `fiber.c:615-621`). `ContsMono` is that, and it is what makes the
one-shot property a property of a *run* rather than of a single arm. -/

/-- **Taken stays taken.** A `Cont_tag` block whose field is NULL is never written again: the
heap only grows at the end (`PERFORM`, `interp.c:1332`) and is only ever written by nulling
(`caml_continuation_use_noexc`, `fiber.c:615-621`). -/
structure ContsMono (m m' : Machine ν) : Prop where
  taken : ∀ (c : ContId),
    m.conts[c]? = Option.some Option.none → m'.conts[c]? = Option.some Option.none

theorem ContsMono.rfl' (m : Machine ν) : ContsMono m m := ⟨fun _ h => h⟩

theorem ContsMono.trans {a b c : Machine ν} (h1 : ContsMono a b) (h2 : ContsMono b c) :
    ContsMono a c := ⟨fun x h => h2.taken x (h1.taken x h)⟩

theorem ContsMono.ofEq {m m' : Machine ν} (h : m'.conts = m.conts) : ContsMono m m' :=
  ⟨fun _ hc => by rw [h]; exact hc⟩

theorem ContsMono.ofSameHeap {m m' : Machine ν} (h : SameHeap m m') : ContsMono m m' :=
  ContsMono.ofEq h.conts

theorem ContsMono.setControl {m a : Machine ν} (h : ContsMono m a) (c : Control ν) :
    ContsMono m (a.setControl c) := h.trans (ContsMono.ofEq rfl)

theorem ContsMono.emit {m a : Machine ν} (h : ContsMono m a) (e : Event) :
    ContsMono m (a.emit e) := h.trans (ContsMono.ofEq rfl)

theorem ContsMono.setCell {m a : Machine ν} (h : ContsMono m a) (v : Value ν) :
    ContsMono m ({ a with cell := v } : Machine ν) := h.trans (ContsMono.ofEq rfl)

theorem ContsMono.setCurrent {m a : Machine ν} (h : ContsMono m a) (s : StackId) :
    ContsMono m (a.setCurrent s) := h.trans (ContsMono.ofEq rfl)

theorem ContsMono.withFrames {m a : Machine ν} (h : ContsMono m a) (fs : List (Frame ν)) :
    ContsMono m (a.withFrames fs) := h.trans (ContsMono.ofEq (conts_withFrames a fs))

theorem ContsMono.pushFrame {m a : Machine ν} (h : ContsMono m a) (f : Frame ν) :
    ContsMono m (a.pushFrame f) := h.withFrames _

theorem ContsMono.applyOne {m a : Machine ν} (h : ContsMono m a) (f v : Value ν) :
    ContsMono m (a.applyOne f v) := (h.pushFrame _).setControl _

theorem ContsMono.applyThree {m a : Machine ν} (h : ContsMono m a) (f x y z : Value ν) :
    ContsMono m (a.applyThree f x y z) := (h.withFrames _).setControl _

theorem ContsMono.setParent {m a : Machine ν} (h : ContsMono m a) (x : StackId)
    (p : Option StackId) : ContsMono m (a.setParent x p) :=
  h.trans (ContsMono.ofEq (conts_setParent a x p))

theorem ContsMono.setTriple {m a : Machine ν} (h : ContsMono m a) (x : StackId)
    (hv hx hf : Value ν) : ContsMono m (a.setTriple x hv hx hf) :=
  h.trans (ContsMono.ofEq (conts_setTriple a x hv hx hf))

theorem ContsMono.freeStack {m a : Machine ν} (h : ContsMono m a) (x : StackId) :
    ContsMono m (a.freeStack x) := h.trans (ContsMono.ofEq rfl)

theorem ContsMono.snoc {m a : Machine ν} (h : ContsMono m a) (info : StackInfo ν) :
    ContsMono m ({ a with stacks := a.stacks ++ [Option.some info] } : Machine ν) :=
  h.trans (ContsMono.ofEq rfl)

/-- `PERFORM` appends one block; every older block keeps its value. -/
theorem ContsMono.contsSnoc {m a : Machine ν} (h : ContsMono m a) (x : StackId) :
    ContsMono m ({ a with conts := a.conts ++ [Option.some x] } : Machine ν) := by
  refine h.trans ⟨?_⟩
  intro c hc
  have hlt : c < a.conts.length := by
    rcases Nat.lt_or_ge c a.conts.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hc; simp at hc
  rw [show ({ a with conts := a.conts ++ [Option.some x] } : Machine ν).conts
    = a.conts ++ [Option.some x] from rfl, List.getElem?_append_left hlt]
  exact hc

/-- `caml_continuation_use_noexc` nulls one field. -/
theorem ContsMono.takeCont {m a : Machine ν} (h : ContsMono m a) (cid : ContId) :
    ContsMono m (a.takeCont cid).1 := by
  refine h.trans ⟨?_⟩
  intro c hc
  unfold Machine.takeCont
  cases hcc : a.conts[cid]? with
  | none => exact hc
  | some slot => cases slot with
    | none => exact hc
    | some sid =>
      simp only
      by_cases hcid : cid = c
      · subst hcid
        have hlt : cid < a.conts.length := by
          rcases Nat.lt_or_ge cid a.conts.length with hlt | hge
          · exact hlt
          · rw [List.getElem?_eq_none hge] at hcc; simp at hcc
        rw [List.getElem?_set_self hlt]
      · rw [List.getElem?_set_ne hcid]
        exact hc


theorem contsMono_doResumeStack (m : Machine ν) (sid : StackId) (fn arg : Value ν) :
    ContsMono m (m.doResumeStack sid fn arg) :=
  ((((ContsMono.rfl' m).setParent _ _).setCurrent sid).applyOne fn arg).emit _

/-- **The continuation heap is monotone under one `step`.** -/
theorem step_contsMono [ToString ν] [Add ν] {m m' : Machine ν} (hstep : m.step = Sum.inl m') :
    ContsMono m m' := by
  unfold step at hstep
  cases hc : m.control with
  | eval env t => rw [hc] at hstep; exact ContsMono.ofSameHeap (stepEval_sameHeap hstep)
  | throw e =>
    rw [hc] at hstep
    cases hf : m.frames with
    | nil =>
      cases hi : m.stack? m.current with
      | none => simp only [stepThrow, hf, hi] at hstep; exact absurd hstep (by simp)
      | some info =>
        cases hp : info.handler.parent with
        | none => simp only [stepThrow, hf, hi, hp] at hstep; exact absurd hstep (by simp)
        | some p =>
          simp only [stepThrow, hf, hi, hp] at hstep
          injection hstep with hstep
          subst hstep
          exact ((((ContsMono.rfl' m).freeStack _).setCurrent p).applyOne _ _).emit _
    | cons f rest =>
      cases f <;>
        simp only [stepThrow, hf] at hstep <;>
        injection hstep with hstep <;>
        subst hstep <;>
        first
          | exact ((ContsMono.rfl' m).withFrames rest).setControl _
          | exact (((ContsMono.rfl' m).withFrames rest).emit _).setControl _
  | ret v =>
    rw [hc] at hstep
    cases hf : m.frames with
    | nil =>
      cases hi : m.stack? m.current with
      | none => simp only [stepRet, hf, hi] at hstep; exact absurd hstep (by simp)
      | some info =>
        cases hp : info.handler.parent with
        | none => simp only [stepRet, hf, hi, hp] at hstep; exact absurd hstep (by simp)
        | some p =>
          simp only [stepRet, hf, hi, hp] at hstep
          injection hstep with hstep
          subst hstep
          exact ((((ContsMono.rfl' m).freeStack _).setCurrent p).applyOne _ _).emit _
    | cons f rest =>
      have hbase : ContsMono m (m.withFrames rest) := (ContsMono.rfl' m).withFrames rest
      cases f
      case performArg =>
        simp only [stepRet, hf] at hstep
        cases hi : (m.withFrames rest).stack? (m.withFrames rest).current with
        | none => simp only [doPerform, hi] at hstep; exact absurd hstep (by simp)
        | some info =>
          cases hp : info.handler.parent with
          | none =>
            simp only [doPerform, hi, hp] at hstep
            injection hstep with hstep
            subst hstep
            exact (hbase.emit _).setControl _
          | some p =>
            simp only [doPerform, hi, hp] at hstep
            injection hstep with hstep
            subst hstep
            exact (((((hbase.contsSnoc _).setParent _ _).setCurrent p).applyThree _ _ _ _).emit _)
      case resume3 stackV fn =>
        simp only [stepRet, hf] at hstep
        cases stackV <;> simp only [doResume] at hstep <;>
          first
            | (injection hstep with hstep
               subst hstep
               first
                 | exact hbase.trans (contsMono_doResumeStack _ _ _ _)
                 | exact (hbase.setControl _).emit _)
            | exact absurd hstep (by simp)
      case runstack3 stackV fn =>
        simp only [stepRet, hf] at hstep
        cases stackV <;> simp only [doRunstack] at hstep <;>
          first
            | (injection hstep with hstep
               subst hstep
               first
                 | exact ((((hbase.setParent _ _).setCurrent _).applyOne _ _).emit _)
                 | exact (hbase.setControl _).emit _)
            | exact absurd hstep (by simp)
      case reperform3 e cont =>
        simp only [stepRet, hf] at hstep
        cases hi : (m.withFrames rest).stack? (m.withFrames rest).current with
        | none => simp only [doReperform, hi] at hstep; exact absurd hstep (by simp)
        | some info =>
          cases hp : info.handler.parent with
          | none =>
            cases cont <;> simp only [doReperform, hi, hp] at hstep
            case cont cid =>
              split at hstep
              · injection hstep with hstep
                subst hstep
                exact ((hbase.takeCont cid).emit _).trans (contsMono_doResumeStack _ _ _ _)
              · injection hstep with hstep
                subst hstep
                exact ((hbase.takeCont cid).setControl _).emit _
            all_goals exact absurd hstep (by simp)
          | some p =>
            cases v <;> simp only [doReperform, hi, hp] at hstep
            case stack tail =>
              injection hstep with hstep
              subst hstep
              exact ((((hbase.setParent _ _).setParent _ _).setCurrent p).applyThree _ _ _ _).emit _
            all_goals exact absurd hstep (by simp)
      case dropContArg =>
        simp only [stepRet, hf] at hstep
        cases v <;> simp only [doDropCont] at hstep
        case cont cid =>
          split at hstep
          · injection hstep with hstep
            subst hstep
            exact (((hbase.takeCont cid).freeStack _).emit _).setControl _
          · injection hstep with hstep
            subst hstep
            exact ((hbase.takeCont cid).setControl _).emit _
        all_goals exact absurd hstep (by simp)
      case allocStack3 hv hx =>
        simp only [stepRet, hf] at hstep
        injection hstep with hstep
        subst hstep
        exact (hbase.snoc _).setControl _
      all_goals
        simp only [stepRet, hf, applyValue, takeContUpdate] at hstep
      all_goals repeat' split at hstep
      all_goals
        first
          | (injection hstep with hstep
             subst hstep
             first
               | exact hbase
               | exact hbase.setControl _
               | exact (hbase.pushFrame _).setControl _
               | exact (hbase.emit _).setControl _
               | exact (hbase.setCell _).setControl _
               | exact ((hbase.takeCont _).emit _).setControl _
               | exact (hbase.takeCont _).setControl _
               | exact (((hbase.takeCont _).setTriple _ _ _ _).emit _).setControl _
               | exact ((hbase.takeCont _).setTriple _ _ _ _).setControl _)
          | exact absurd hstep (by simp)

/-! ### The run-level consequences -/

theorem reaches_contsMono [ToString ν] [Add ν] {m m' : Machine ν} (hr : Reaches m m') :
    ContsMono m m' := by
  refine reaches_induction (P := fun a => ContsMono m a) ?_ hr (ContsMono.rfl' m)
  intro a b hma hs
  exact hma.trans (step_contsMono hs)

/-- **A taken handle stays taken, for the rest of the run.** -/
theorem handle_taken_stable [ToString ν] [Add ν] {m m' : Machine ν} {cid : ContId}
    (hr : Reaches m m') (h : m.conts[cid]? = Option.some Option.none) :
    m'.conts[cid]? = Option.some Option.none :=
  (reaches_contsMono hr).taken cid h

/-- **A parked stack is resumed at most once, and only through its own continuation.** Once
`caml_continuation_use_noexc` has answered with the stack (`fiber.c:615-621`), every later use of
that block, anywhere in the rest of the run, answers `nullStack` — and `%resume` on `nullStack`
raises `Continuation_already_resumed` (`interp.c:1291-1294`, O1's `doResume_null`). -/
theorem resume_at_most_once [ToString ν] [Add ν] {m1 m2 : Machine ν} {cid : ContId}
    {sid : StackId} (hlive : m1.conts[cid]? = Option.some (Option.some sid))
    (hr : Reaches (m1.takeCont cid).1 m2) : (m2.takeCont cid).2 = Value.nullStack := by
  have hlt : cid < m1.conts.length := by
    rcases Nat.lt_or_ge cid m1.conts.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hlive; simp at hlive
  have htaken : (m1.takeCont cid).1.conts[cid]? = Option.some Option.none := by
    rw [takeCont_live m1 cid sid hlive]
    exact List.getElem?_set_self hlt
  have := handle_taken_stable hr htaken
  unfold takeCont
  rw [this]

/-! ### Parked stacks keep their frames

`ReachesOff sid m m'` is "the run from `m` to `m'` never ran on `sid` and never freed it" — a
stack parked by a `perform`, between the capture and the matching `resume`. -/

/-- A run that stays off `sid` and keeps it live. -/
inductive ReachesOff [ToString ν] [Add ν] (sid : StackId) : Machine ν → Machine ν → Prop
  | refl (m : Machine ν) : m.current ≠ sid → (m.stack? sid).isSome → ReachesOff sid m m
  | tail {m a b : Machine ν} : ReachesOff sid m a → a.step = Sum.inl b →
      b.current ≠ sid → (b.stack? sid).isSome → ReachesOff sid m b

theorem ReachesOff.currentNe [ToString ν] [Add ν] {sid : StackId} {m m' : Machine ν}
    (h : ReachesOff sid m m') : m'.current ≠ sid := by
  cases h with
  | refl hne _ => exact hne
  | tail _ _ hne _ => exact hne

theorem ReachesOff.live [ToString ν] [Add ν] {sid : StackId} {m m' : Machine ν}
    (h : ReachesOff sid m m') : (m'.stack? sid).isSome := by
  cases h with
  | refl _ hl => exact hl
  | tail _ _ _ hl => exact hl

theorem ReachesOff.toReaches [ToString ν] [Add ν] {sid : StackId} {m m' : Machine ν}
    (h : ReachesOff sid m m') : Reaches m m' := by
  induction h with
  | refl _ _ => exact Reaches.refl _
  | tail _ hs _ _ ih => exact Reaches.tail ih hs

/-- **Frame preservation across parking.** While the machine is not running on `sid` and has not
freed it, `sid`'s frames — the traps `PUSHTRAP` pushed on it included (`interp.c:930-938`) — are
exactly what they were. -/
theorem frames_parked [ToString ν] [Add ν] {sid : StackId} {m m' : Machine ν}
    (h : ReachesOff sid m m') :
    (m'.stack? sid).map (·.frames) = (m.stack? sid).map (·.frames) := by
  induction h with
  | refl _ _ => rfl
  | tail hro hs hne hlive ih =>
    rename_i a b
    have hst := step_stableOff (lt_length_of_isSome hro.live) hro.currentNe hne hs
    rcases hst.keep with hk | hk
    · rw [hk]; exact ih
    · rw [hk] at hlive; exact absurd hlive (by simp)

/-- **Traps survive capture** (O1 report §5, second blocked statement; witness 09's shape,
stated generally). A trap pushed on a stack before it performs is still on it when a later
`resume` re-enters, because nothing between the two touches its frames. -/
theorem trap_survives_capture [ToString ν] [Add ν] {sid : StackId} {m m' : Machine ν}
    {fs : List (Frame ν)} (h : ReachesOff sid m m')
    (hcap : (m.stack? sid).map (·.frames) = Option.some fs) :
    (m'.stack? sid).map (·.frames) = Option.some fs := by
  rw [frames_parked h]; exact hcap

/-- The same, spelled for a single trap frame: a `try … with` pushed on the captured stack is
still there. -/
theorem trap_frame_survives_capture [ToString ν] [Add ν] {sid : StackId} {m m' : Machine ν}
    {fs : List (Frame ν)} {env : List (Value ν)} {handler : Term ν}
    (h : ReachesOff sid m m') (hcap : (m.stack? sid).map (·.frames) = Option.some fs)
    (htrap : Frame.trap env handler ∈ fs) :
    ∃ fs', (m'.stack? sid).map (·.frames) = Option.some fs' ∧ Frame.trap env handler ∈ fs' :=
  ⟨fs, trap_survives_capture h hcap, htrap⟩

/-- **Quiescence, along a run.** The current stack is the only stack whose control moves: every
other live stack's whole continuation is its frame list, and `step` leaves it alone. This is the
one-step form; `frames_parked` is its transitive closure. -/
theorem quiescence [ToString ν] [Add ν] {m m' : Machine ν} {s : StackId}
    (hlive : (m.stack? s).isSome) (h1 : m.current ≠ s) (h2 : m'.current ≠ s)
    (hstep : m.step = Sum.inl m') (hlive' : (m'.stack? s).isSome) :
    (m'.stack? s).map (·.frames) = (m.stack? s).map (·.frames) := by
  rcases (step_stableOff (lt_length_of_isSome hlive) h1 h2 hstep).keep with hk | hk
  · exact hk
  · rw [hk] at hlive'; exact absurd hlive' (by simp)

/-! ### `handle_effect` runs on the performer's parent, and nowhere else

The field-level form a simulation relation between a `Deep.RunFiber` and a `StackInfo` consumes:
after a `perform`, the performing stack is *parked* — detached, its frames untouched, named by
exactly one fresh `Cont_tag` block — and the frames that gained the handler call are its
*parent's*. -/

theorem frames_map_of_live {m : Machine ν} {X : List (Frame ν)}
    (hlive : (m.stack? m.current).isSome) (h : m.frames = X) :
    (m.stack? m.current).map (·.frames) = Option.some X := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp hlive
  rw [hi]
  unfold frames at h
  rw [hi] at h
  simpa using h

theorem isSome_setControl (m : Machine ν) (c : Control ν) (t : StackId) :
    ((m.setControl c).stack? t).isSome = (m.stack? t).isSome := rfl

theorem stack?_setControl (m : Machine ν) (c : Control ν) (t : StackId) :
    (m.setControl c).stack? t = m.stack? t := rfl

theorem stack?_applyThree_ne {m : Machine ν} {t : StackId} (f a b c : Value ν)
    (h : m.current ≠ t) : (m.applyThree f a b c).stack? t = m.stack? t :=
  stack?_withFrames_ne _ h

theorem isSome_applyOne (m : Machine ν) (f a : Value ν) (t : StackId) :
    ((m.applyOne f a).stack? t).isSome = (m.stack? t).isSome :=
  isSome_withFrames _ t

theorem isSome_applyThree (m : Machine ν) (f a b c : Value ν) (t : StackId) :
    ((m.applyThree f a b c).stack? t).isSome = (m.stack? t).isSome :=
  isSome_withFrames _ t

/-- **`PERFORM`, field by field** (`interp.c:1334-1357`, `amd64.S:880-896`). -/
theorem perform_parks_and_handles_on_parent {m : Machine ν} (h : m.WF) {p : StackId}
    {info pinfo : StackInfo ν} (effV : Value ν)
    (hsi : m.stack? m.current = Option.some info)
    (hp : info.handler.parent = Option.some p)
    (hpi : m.stack? p = Option.some pinfo) :
    ∃ m', m.doPerform effV = Sum.inl m' ∧
      m'.current = p ∧
      m'.control = Control.ret effV ∧
      m'.parentOf m.current = Option.none ∧
      m'.conts[m.conts.length]? = Option.some (Option.some m.current) ∧
      (m'.stack? m.current).map (·.frames) = Option.some info.frames ∧
      (m'.stack? p).map (·.frames) = Option.some (Frame.appFn info.handler.handleEffect ::
        Frame.appTo (Value.cont m.conts.length) :: Frame.appTo (Value.stack m.current) ::
        pinfo.frames) := by
  have hpar : m.parentOf m.current = Option.some p := by
    unfold parentOf handlerOf; rw [hsi]; exact hp
  have hne : m.current ≠ p := fun hc => parent_ne_self h hpar hc.symm
  have hsi1 : ({ m with conts := m.conts ++ [Option.some m.current] } : Machine ν).stack?
      m.current = Option.some info := hsi
  have hpi1 : ({ m with conts := m.conts ++ [Option.some m.current] } : Machine ν).stack? p
      = Option.some pinfo := hpi
  obtain ⟨m', hstep, hcur, hconts, hdetach, hctl, hframes⟩ :=
    doPerform_parent m effV hsi hp hpi hne
  refine ⟨m', hstep, hcur, hctl, hdetach, ?_, ?_, ?_⟩
  · rw [hconts, List.getElem?_append_right (Nat.le_refl _)]
    simp
  · -- the performer's own frames are untouched: the handler call is queued on the parent
    simp only [doPerform, hsi, hp] at hstep
    injection hstep with hstep
    subst hstep
    rw [stack?_emit,
      stack?_applyThree_ne _ _ _ _ (by
        simp only [current_setCurrent]; exact fun hc => hne hc.symm),
      stack?_setCurrent, stack?_setParent_self Option.none hsi1]
    rfl
  · have hlivep : (m'.stack? m'.current).isSome := by
      rw [hcur]
      simp only [doPerform, hsi, hp] at hstep
      injection hstep with hstep
      subst hstep
      rw [stack?_emit, isSome_applyThree, stack?_setCurrent, isSome_setParent, hpi1]
      rfl
    rw [← hcur]
    exact frames_map_of_live hlivep hframes


/-! ### Frames, read through `Option.map`

The shape a simulation relation states its frame equalities in. -/

theorem framesMap_setParent (m : Machine ν) (x : StackId) (p : Option StackId) (t : StackId) :
    ((m.setParent x p).stack? t).map (·.frames) = (m.stack? t).map (·.frames) := by
  by_cases hx : x = t
  · subst hx
    cases hst : m.stack? x with
    | none => rw [setParent_of_dead hst, hst]
    | some info => rw [stack?_setParent_self p hst]; simp
  · rw [stack?_setParent_ne p hx]

theorem frames_of_framesMap {m : Machine ν} {fs : List (Frame ν)}
    (h : (m.stack? m.current).map (·.frames) = Option.some fs) : m.frames = fs := by
  unfold frames
  cases hst : m.stack? m.current with
  | none => rw [hst] at h; simp at h
  | some info => rw [hst] at h; simpa using h

theorem framesMap_withFrames {m : Machine ν} {info : StackInfo ν} (fs : List (Frame ν))
    (h : m.stack? m.current = Option.some info) :
    ((m.withFrames fs).stack? (m.withFrames fs).current).map (·.frames) = Option.some fs := by
  rw [current_withFrames]
  unfold withFrames
  rw [h, stack?_setStack_self { info with frames := fs } h]
  rfl

theorem framesMap_pushFrame {m : Machine ν} {fs : List (Frame ν)} (f : Frame ν) (t : StackId)
    (ht : m.current = t) (h : (m.stack? t).map (·.frames) = Option.some fs) :
    ((m.pushFrame f).stack? t).map (·.frames) = Option.some (f :: fs) := by
  subst ht
  cases hst : m.stack? m.current with
  | none => rw [hst] at h; simp at h
  | some info =>
    unfold pushFrame
    rw [frames_of_framesMap h]
    have := framesMap_withFrames (m := m) fs hst
    rw [current_withFrames] at this
    unfold withFrames
    rw [hst, stack?_setStack_self { info with frames := f :: fs } hst]
    rfl

/-! ### `do_resume`, field by field -/

theorem doResumeStack_control (m : Machine ν) (sid : StackId) (fn arg : Value ν) :
    (m.doResumeStack sid fn arg).control = Control.ret arg := rfl

theorem doResumeStack_conts (m : Machine ν) (sid : StackId) (fn arg : Value ν) :
    (m.doResumeStack sid fn arg).conts = m.conts := by
  unfold doResumeStack
  rw [conts_emit, conts_applyOne, conts_setCurrent, conts_setParent]

/-- The resumed stack gets exactly one frame: `fn` applied to the resumption value
(`interp.c:1300-1310`). Its own frames — traps included — are underneath, untouched. -/
theorem doResumeStack_framesMap {m : Machine ν} {sid : StackId} {fs : List (Frame ν)}
    (fn arg : Value ν) (h : (m.stack? sid).map (·.frames) = Option.some fs) :
    ((m.doResumeStack sid fn arg).stack? sid).map (·.frames)
      = Option.some (Frame.appFn fn :: fs) := by
  unfold doResumeStack
  rw [stack?_emit]
  unfold applyOne
  rw [stack?_setControl]
  refine framesMap_pushFrame (Frame.appFn fn) sid rfl ?_
  rw [stack?_setCurrent, framesMap_setParent]
  exact h

/-- **`REPERFORMTERM` at the root** (`interp.c:1374-1381`; O1 report §5, third blocked
statement). The continuation is taken — so the handle is spent, and `resume_at_most_once`
applies — and it is resumed with a function that raises `Unhandled`, on the captured stack: the
exception surfaces *inside the performing fiber*, where that fiber's own traps can see it. -/
theorem reperform_root_raises_in_performer {m : Machine ν} {info sinfo : StackInfo ν}
    (effV : Value ν) {cid : ContId} {sid : StackId}
    (hsi : m.stack? m.current = Option.some info)
    (hroot : info.handler.parent = Option.none)
    (hcont : m.conts[cid]? = Option.some (Option.some sid))
    (hsid : m.stack? sid = Option.some sinfo) :
    ∃ m', m.doReperform effV (Value.cont cid) (Value.stack m.current) = Sum.inl m' ∧
      m'.current = sid ∧
      m'.control = Control.ret (Value.exn ExnId.unhandled effV) ∧
      m'.conts[cid]? = Option.some Option.none ∧
      (m'.stack? sid).map (·.frames) = Option.some
        (Frame.appFn (Value.closure [] (Term.raise (Term.var 0))) :: sinfo.frames) := by
  have hlt : cid < m.conts.length := by
    rcases Nat.lt_or_ge cid m.conts.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hcont; simp at hcont
  simp only [doReperform, hsi, hroot, takeCont, hcont]
  refine ⟨_, rfl, doResumeStack_current _ _ _ _, doResumeStack_control _ _ _ _, ?_, ?_⟩
  · rw [doResumeStack_conts,
      show (({ m with conts := m.conts.set cid Option.none } : Machine ν).emit
        (Event.unhandled effV.effIdOf)).conts = m.conts.set cid Option.none from rfl]
    exact List.getElem?_set_self hlt
  · refine doResumeStack_framesMap _ _ ?_
    rw [show (({ m with conts := m.conts.set cid Option.none } : Machine ν).emit
      (Event.unhandled effV.effIdOf)).stack? sid = m.stack? sid from rfl, hsid]
    rfl

/-! ## 10. A small-step toolkit

Four one-step lemmas in the shape a chain of `Reaches` can consume: each gives the next machine
abstractly, with its `current`, its `control` and the frames of the stack it runs on. They are
what turns an arm-level fact into a step-sequence equation. -/

/-- Returning into an `appFn` of a closure: the closure's body starts, one frame lighter. -/
theorem step_ret_appFn_closure [ToString ν] [Add ν] {m : Machine ν} {fs : List (Frame ν)}
    {v : Value ν} {env : List (Value ν)} {body : Term ν}
    (hctl : m.control = Control.ret v)
    (hfr : (m.stack? m.current).map (·.frames)
      = Option.some (Frame.appFn (Value.closure env body) :: fs)) :
    ∃ M, m.step = Sum.inl M ∧ M.current = m.current ∧
      M.control = Control.eval (v :: env) body ∧
      (M.stack? m.current).map (·.frames) = Option.some fs := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp (by
    cases hst : m.stack? m.current with
    | none => rw [hst] at hfr; simp at hfr
    | some info => rfl : (m.stack? m.current).isSome)
  refine ⟨(m.withFrames fs).setControl (Control.eval (v :: env) body), ?_, ?_, ?_, ?_⟩
  · rw [step, hctl]
    simp only [stepRet, frames_of_framesMap hfr, applyValue]
  · exact current_withFrames _ _
  · rfl
  · have := framesMap_withFrames (m := m) fs hi
    rw [current_withFrames] at this
    exact this

/-- Evaluating `raise e`. -/
theorem step_eval_raise [ToString ν] [Add ν] {m : Machine ν} {fs : List (Frame ν)}
    {env : List (Value ν)} {e : Term ν}
    (hctl : m.control = Control.eval env (Term.raise e))
    (hfr : (m.stack? m.current).map (·.frames) = Option.some fs) :
    ∃ M, m.step = Sum.inl M ∧ M.current = m.current ∧ M.control = Control.eval env e ∧
      (M.stack? m.current).map (·.frames) = Option.some (Frame.raiseArg :: fs) := by
  refine ⟨(m.pushFrame Frame.raiseArg).setControl (Control.eval env e), ?_, ?_, ?_, ?_⟩
  · rw [step, hctl]; simp only [stepEval]
  · exact current_withFrames _ _
  · rfl
  · exact framesMap_pushFrame Frame.raiseArg m.current rfl hfr

/-- Evaluating a variable. -/
theorem step_eval_var [ToString ν] [Add ν] {m : Machine ν} {env : List (Value ν)} {i : Nat}
    {v : Value ν} (hctl : m.control = Control.eval env (Term.var i)) (hv : env[i]? = Option.some v) :
    ∃ M, m.step = Sum.inl M ∧ M.current = m.current ∧ M.control = Control.ret v ∧
      ∀ t, (M.stack? t).map (·.frames) = (m.stack? t).map (·.frames) := by
  refine ⟨m.setControl (Control.ret v), ?_, ?_, ?_, ?_⟩
  · rw [step, hctl]
    simp only [stepEval, hv]
  · rfl
  · rfl
  · exact fun _ => rfl

/-- Returning into a `raiseArg`: the value becomes the exception being thrown, on this stack —
`Kraise` (`bytegen.ml:757`), which unwinds *within* the stack until a trap or the stack's end
(`interp.c:964-1005`). -/
theorem step_ret_raiseArg [ToString ν] [Add ν] {m : Machine ν} {fs : List (Frame ν)} {v : Value ν}
    (hctl : m.control = Control.ret v)
    (hfr : (m.stack? m.current).map (·.frames) = Option.some (Frame.raiseArg :: fs)) :
    ∃ M, m.step = Sum.inl M ∧ M.current = m.current ∧ M.control = Control.throw v ∧
      (M.stack? m.current).map (·.frames) = Option.some fs := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp (by
    cases hst : m.stack? m.current with
    | none => rw [hst] at hfr; simp at hfr
    | some info => rfl : (m.stack? m.current).isSome)
  refine ⟨(m.withFrames fs).setControl (Control.throw v), ?_, ?_, ?_, ?_⟩
  · rw [step, hctl]
    simp only [stepRet, frames_of_framesMap hfr]
  · exact current_withFrames _ _
  · rfl
  · have := framesMap_withFrames (m := m) fs hi
    rw [current_withFrames] at this
    exact this

/-- **The `Unhandled` really is raised inside the resumed stack.** Four steps after a resume with
the raising closure — the shape `REPERFORMTERM`'s root route (`interp.c:1374-1381`) and
`Deep.discontinue` (`effect.ml:59`) both use — the control is `throw v` on that same stack, with
its own frames, so its own traps see it. -/
theorem raise_closure_throws [ToString ν] [Add ν] {m : Machine ν} {fs : List (Frame ν)}
    {v : Value ν} (hctl : m.control = Control.ret v)
    (hfr : (m.stack? m.current).map (·.frames)
      = Option.some (Frame.appFn (Value.closure [] (Term.raise (Term.var 0))) :: fs)) :
    ∃ M, Reaches m M ∧ M.current = m.current ∧ M.control = Control.throw v ∧
      (M.stack? m.current).map (·.frames) = Option.some fs := by
  obtain ⟨M1, h1, h1c, h1ctl, h1f⟩ := step_ret_appFn_closure hctl hfr
  rw [← h1c] at h1f
  obtain ⟨M2, h2, h2c, h2ctl, h2f⟩ := step_eval_raise h1ctl h1f
  rw [← h2c] at h2f
  obtain ⟨M3, h3, h3c, h3ctl, h3f⟩ := step_eval_var h2ctl (i := 0) (v := v) rfl
  obtain ⟨M4, h4, h4c, h4ctl, h4f⟩ := step_ret_raiseArg h3ctl (by rw [h3f, h3c]; exact h2f)
  refine ⟨M4, ?_, ?_, h4ctl, ?_⟩
  · exact Reaches.head h1 (Reaches.head h2 (Reaches.head h3 (Reaches.tail (Reaches.refl _) h4)))
  · rw [h4c, h3c, h2c, h1c]
  · rw [show m.current = M3.current by rw [h3c, h2c, h1c]]
    exact h4f

/-! ## 11. The `Stdlib.Effect` behavioural corollaries

`OCaml5.Stdlib`'s builders are terms over the eight primitive forms, so their behaviour is a
consequence of the transitions. These are the three the O1 report §5 lists, each as a
step-sequence equation over the machine, in the field-level shape a simulation relation with a
`Deep.RunFiber` record consumes. -/

/-- **`Deep.continue k v`** (`effect.ml:57`): `resume (take_cont_noexc k) (fun x -> x) v`. Once
the handle has answered with the stack, the machine resumes *on that stack*, with `v`, and with
the stack's own frames — every trap included — underneath. -/
theorem deepContinue_resumes [ToString ν] [Add ν] {m : Machine ν} {sid : StackId}
    {fs : List (Frame ν)} (v : Value ν)
    (hfr : (m.stack? sid).map (·.frames) = Option.some fs) :
    ∃ M, Reaches (m.doResumeStack sid (Value.closure [] (Term.var 0)) v) M ∧
      M.current = sid ∧ M.control = Control.ret v ∧
      (M.stack? sid).map (·.frames) = Option.some fs := by
  have hcur := doResumeStack_current m sid (Value.closure [] (Term.var 0)) v
  have hfr1 : ((m.doResumeStack sid (Value.closure [] (Term.var 0)) v).stack?
      (m.doResumeStack sid (Value.closure [] (Term.var 0)) v).current).map (·.frames)
      = Option.some (Frame.appFn (Value.closure [] (Term.var 0)) :: fs) := by
    rw [hcur]; exact doResumeStack_framesMap _ _ hfr
  obtain ⟨M1, h1, h1c, h1ctl, h1f⟩ :=
    step_ret_appFn_closure (doResumeStack_control m sid (Value.closure [] (Term.var 0)) v) hfr1
  obtain ⟨M2, h2, h2c, h2ctl, h2f⟩ := step_eval_var h1ctl (i := 0) (v := v) rfl
  refine ⟨M2, Reaches.head h1 (Reaches.tail (Reaches.refl _) h2), ?_, h2ctl, ?_⟩
  · rw [h2c, h1c, hcur]
  · rw [h2f, ← hcur]; exact h1f

/-- **`Deep.discontinue k e`** (`effect.ml:59`): `resume (take_cont_noexc k) (fun e -> raise e) e`.
Four steps later the exception is being thrown *on the captured stack*, with that stack's own
frames — so a trap pushed there before the `perform` catches it (witness 09). -/
theorem deepDiscontinue_raises [ToString ν] [Add ν] {m : Machine ν} {sid : StackId}
    {fs : List (Frame ν)} (e : Value ν)
    (hfr : (m.stack? sid).map (·.frames) = Option.some fs) :
    ∃ M, Reaches (m.doResumeStack sid (Value.closure [] (Term.raise (Term.var 0))) e) M ∧
      M.current = sid ∧ M.control = Control.throw e ∧
      (M.stack? sid).map (·.frames) = Option.some fs := by
  have hcur := doResumeStack_current m sid (Value.closure [] (Term.raise (Term.var 0))) e
  have hfr1 : ((m.doResumeStack sid (Value.closure [] (Term.raise (Term.var 0))) e).stack?
      (m.doResumeStack sid (Value.closure [] (Term.raise (Term.var 0))) e).current).map (·.frames)
      = Option.some (Frame.appFn (Value.closure [] (Term.raise (Term.var 0))) :: fs) := by
    rw [hcur]; exact doResumeStack_framesMap _ _ hfr
  obtain ⟨M, hr, hc, hctl, hf⟩ :=
    raise_closure_throws
      (doResumeStack_control m sid (Value.closure [] (Term.raise (Term.var 0))) e) hfr1
  exact ⟨M, hr, by rw [hc, hcur], hctl, by rw [← hcur]; exact hf⟩

/-- **`Deep.match_with`'s `retc` runs on the parent** (`effect.ml:78-79`: the triple is installed
by `alloc_stack` on the *child*, and `do_return` calls it after switching, `interp.c:576-594`). -/
theorem child_return_runs_retc_on_parent {m : Machine ν} {old p : StackId}
    {info pinfo : StackInfo ν} (v : Value ν)
    (hold : m.stack? old = Option.some info) (hp : m.stack? p = Option.some pinfo)
    (hne : p ≠ old) :
    (m.doReturnToParent old p v).current = p ∧
    (m.doReturnToParent old p v).control = Control.ret v ∧
    (m.doReturnToParent old p v).stack? old = Option.none ∧
    ((m.doReturnToParent old p v).stack? p).map (·.frames)
      = Option.some (Frame.appFn info.handler.handleValue :: pinfo.frames) := by
  obtain ⟨hfree, hcur, hctl⟩ := doReturnToParent_frees m v hold hne
  refine ⟨hcur, hctl, hfree, ?_⟩
  have hlive : ((m.doReturnToParent old p v).stack?
      (m.doReturnToParent old p v).current).isSome := by
    rw [hcur]
    unfold doReturnToParent
    rw [stack?_emit, isSome_applyOne, stack?_setCurrent, stack?_freeStack_ne (Ne.symm hne), hp]
    rfl
  have := frames_map_of_live hlive (doReturnToParent_handler m v hold hp hne)
  rw [hcur] at this
  exact this

/-- **…and `exnc` on the parent for an uncaught raise** (`effect.ml:90`; `raise_notrace` past the
last trap, `interp.c:980-999`). -/
theorem child_raise_runs_exnc_on_parent {m : Machine ν} {old p : StackId}
    {info pinfo : StackInfo ν} (e : Value ν)
    (hold : m.stack? old = Option.some info) (hp : m.stack? p = Option.some pinfo)
    (hne : p ≠ old) :
    (m.doRaiseToParent old p e).current = p ∧
    (m.doRaiseToParent old p e).control = Control.ret e ∧
    (m.doRaiseToParent old p e).stack? old = Option.none ∧
    ((m.doRaiseToParent old p e).stack? p).map (·.frames)
      = Option.some (Frame.appFn info.handler.handleExn :: pinfo.frames) := by
  obtain ⟨hfree, hcur, hctl⟩ := doRaiseToParent_frees m e hold hne
  refine ⟨hcur, hctl, hfree, ?_⟩
  have hlive : ((m.doRaiseToParent old p e).stack?
      (m.doRaiseToParent old p e).current).isSome := by
    rw [hcur]
    unfold doRaiseToParent
    rw [stack?_emit, isSome_applyOne, stack?_setCurrent, stack?_freeStack_ne (Ne.symm hne), hp]
    rfl
  have := frames_map_of_live hlive (doRaiseToParent_handler m e hold hp hne)
  rw [hcur] at this
  exact this

/-- **The `reperform` root route, end to end** (`interp.c:1374-1381`). The handle is spent, the
captured stack is re-entered, and four steps later `Unhandled eff` is being thrown *there*, over
that stack's own frames — which is why a `try … with` inside the performing fiber catches it
(witness 08). -/
theorem reperform_root_unhandled_in_performer [ToString ν] [Add ν] {m : Machine ν}
    {info sinfo : StackInfo ν} (effV : Value ν) {cid : ContId} {sid : StackId}
    (hsi : m.stack? m.current = Option.some info)
    (hroot : info.handler.parent = Option.none)
    (hcont : m.conts[cid]? = Option.some (Option.some sid))
    (hsid : m.stack? sid = Option.some sinfo) :
    ∃ m' M, m.doReperform effV (Value.cont cid) (Value.stack m.current) = Sum.inl m' ∧
      Reaches m' M ∧
      M.current = sid ∧
      M.control = Control.throw (Value.exn ExnId.unhandled effV) ∧
      (M.stack? sid).map (·.frames) = Option.some sinfo.frames ∧
      m'.conts[cid]? = Option.some Option.none := by
  obtain ⟨m', hstep, hcur, hctl, hconts, hfr⟩ :=
    reperform_root_raises_in_performer effV hsi hroot hcont hsid
  have hfr' : (m'.stack? m'.current).map (·.frames) = Option.some
      (Frame.appFn (Value.closure [] (Term.raise (Term.var 0))) :: sinfo.frames) := by
    rw [hcur]; exact hfr
  obtain ⟨M, hr, hc, hthrow, hf⟩ := raise_closure_throws hctl hfr'
  exact ⟨m', M, hstep, hr, by rw [hc, hcur], hthrow, by rw [← hcur]; exact hf, hconts⟩

/-! ## 12. The four statements spike A0 asks for

`docs/research/2026-09-04-spike-a0-avatar.md` §1, "Requests to P1", in its order. Each is stated
in the field-level shape a simulation relation between a `Deep.RunFiber` record and a `StackInfo`
would use: `RunFiber.id` ↔ `StackId`, `RunFiber.running` ↔ `sid = m.current`, `RunFiber.parked`
↔ a live `Cont_tag` block naming `sid`, `RunFiber.frame` ↔ `StackInfo.frames`. -/

/-- **A0 §1 P1.1 — a fiber parked by `perform` is resumed at most once.** `takeCont_twice`
(`Effect.lean:947`) lifted from the heap block to the run: after the continuation captured at the
park has been taken once, every later state of the run finds the handle spent, and `%resume`
through it raises `Continuation_already_resumed` and changes nothing else — no stack is entered,
no frame is queued. -/
theorem resume_at_most_once_raises [ToString ν] [Add ν] {m1 m2 : Machine ν} {cid : ContId}
    {sid : StackId} (fn arg : Value ν)
    (hcap : m1.conts[cid]? = Option.some (Option.some sid))
    (hr : Reaches (m1.takeCont cid).1 m2) :
    (m2.takeCont cid).1 = m2 ∧ (m2.takeCont cid).2 = Value.nullStack ∧
    ∃ m3, m2.doResume (m2.takeCont cid).2 fn arg = Sum.inl m3 ∧
      m3.control = Control.throw (Value.exn ExnId.continuationAlreadyResumed Value.unit) ∧
      m3.current = m2.current ∧ m3.stacks = m2.stacks ∧ m3.conts = m2.conts := by
  have hlt : cid < m1.conts.length := by
    rcases Nat.lt_or_ge cid m1.conts.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hcap; simp at hcap
  have htaken : (m1.takeCont cid).1.conts[cid]? = Option.some Option.none := by
    rw [takeCont_live m1 cid sid hcap]
    exact List.getElem?_set_self hlt
  have h2 : m2.conts[cid]? = Option.some Option.none := handle_taken_stable hr htaken
  have hid := takeCont_taken m2 cid h2
  refine ⟨by rw [hid], by rw [hid], ?_⟩
  rw [hid]
  obtain ⟨m3, hstep, hctl, hcur, hst, hcs, -⟩ := doResume_null m2 fn arg
  exact ⟨m3, hstep, hctl, hcur, hst, hcs⟩


/-! ### Where `current` goes -/

theorem current_setControl (m : Machine ν) (c : Control ν) : (m.setControl c).current = m.current :=
  rfl

theorem current_setCell (m : Machine ν) (v : Value ν) :
    ({ m with cell := v } : Machine ν).current = m.current := rfl

theorem current_freeStack (m : Machine ν) (x : StackId) : (m.freeStack x).current = m.current := rfl

theorem current_takeCont (m : Machine ν) (cid : ContId) :
    (m.takeCont cid).1.current = m.current := (sameStacks_takeCont m cid).current

theorem current_setTriple' (m : Machine ν) (x : StackId) (hv hx hf : Value ν) :
    (m.setTriple x hv hx hf).current = m.current := current_setTriple m x hv hx hf

theorem current_doResumeStack (m : Machine ν) (sid : StackId) (fn arg : Value ν) :
    (m.doResumeStack sid fn arg).current = sid := doResumeStack_current m sid fn arg

set_option linter.unusedSimpArgs false in
/-- **You can only enter a live stack.** Whatever `step` switches to — a parent
(`interp.c:1352`, `:578`, `:985`), a captured stack (`:1298`) or a fresh one — was already a live
slot before the step. Under `WF` and `Safe` this is exhaustive over the arms; it is the fact a
simulation needs to know that "the fiber that becomes running existed". -/
theorem step_current_live [ToString ν] [Add ν] {m m' : Machine ν} (h : m.WF) (hsafe : m.Safe)
    (hstep : m.step = Sum.inl m') : (m.stack? m'.current).isSome := by
  unfold step at hstep
  cases hc : m.control with
  | eval env t =>
    rw [hc] at hstep
    rw [(stepEval_sameHeap hstep).current]
    exact h.currentLive
  | throw e =>
    rw [hc] at hstep
    cases hf : m.frames with
    | nil =>
      cases hi : m.stack? m.current with
      | none => simp only [stepThrow, hf, hi] at hstep; exact absurd hstep (by simp)
      | some info =>
        cases hp : info.handler.parent with
        | none => simp only [stepThrow, hf, hi, hp] at hstep; exact absurd hstep (by simp)
        | some p =>
          have hpar : m.parentOf m.current = Option.some p := by
            unfold parentOf handlerOf; rw [hi]; exact hp
          simp only [stepThrow, hf, hi, hp] at hstep
          injection hstep with hstep
          subst hstep
          simp only [doRaiseToParent, current_emit, current_applyOne, current_setCurrent]
          exact h.parentLive _ _ hpar
    | cons f rest =>
      cases f <;>
        simp only [stepThrow, hf] at hstep <;>
        injection hstep with hstep <;>
        subst hstep <;>
        simp only [pushFrame, current_emit, current_setControl, current_withFrames] <;>
        exact h.currentLive
  | ret v =>
    rw [hc] at hstep
    cases hf : m.frames with
    | nil =>
      cases hi : m.stack? m.current with
      | none => simp only [stepRet, hf, hi] at hstep; exact absurd hstep (by simp)
      | some info =>
        cases hp : info.handler.parent with
        | none => simp only [stepRet, hf, hi, hp] at hstep; exact absurd hstep (by simp)
        | some p =>
          have hpar : m.parentOf m.current = Option.some p := by
            unfold parentOf handlerOf; rw [hi]; exact hp
          simp only [stepRet, hf, hi, hp] at hstep
          injection hstep with hstep
          subst hstep
          simp only [doReturnToParent, current_emit, current_applyOne, current_setCurrent]
          exact h.parentLive _ _ hpar
    | cons f rest =>
      have hsh0 : SameHeap m (m.withFrames rest) := (SameHeap.rfl' m).withFrames rest
      have hwf0 : (m.withFrames rest).WF := h.sameHeap hsh0
      have hss0 : SameStacks m (m.withFrames rest) := hsh0.toSameStacks
      cases f
      case performArg =>
        simp only [stepRet, hf] at hstep
        cases hi : (m.withFrames rest).stack? (m.withFrames rest).current with
        | none => simp only [doPerform, hi] at hstep; exact absurd hstep (by simp)
        | some info =>
          cases hp : info.handler.parent with
          | none =>
            simp only [doPerform, hi, hp] at hstep
            injection hstep with hstep
            subst hstep
            simp only [current_emit, current_setControl, current_withFrames]
            exact h.currentLive
          | some p =>
            have hpar : (m.withFrames rest).parentOf (m.withFrames rest).current
                = Option.some p := by
              unfold parentOf handlerOf; rw [hi]; exact hp
            simp only [doPerform, hi, hp] at hstep
            injection hstep with hstep
            subst hstep
            simp only [current_emit, current_applyThree, current_setCurrent]
            rw [← hss0.live p]
            exact hwf0.parentLive _ _ hpar
      case resume3 stackV fn =>
        simp only [stepRet, hf] at hstep
        cases stackV <;> simp only [doResume] at hstep <;>
          first
            | (injection hstep with hstep
               subst hstep
               first
                 | (simp only [current_doResumeStack]
                    rw [← hss0.live]
                    exact ((hsafe.resume _ fn rest hf).congr hss0).enterLive)
                 | (simp only [current_emit, current_setControl, current_withFrames]
                    exact h.currentLive))
            | exact absurd hstep (by simp)
      case runstack3 stackV fn =>
        simp only [stepRet, hf] at hstep
        cases stackV <;> simp only [doRunstack] at hstep <;>
          first
            | (injection hstep with hstep
               subst hstep
               first
                 | (simp only [current_emit, current_applyOne, current_setCurrent]
                    rw [← hss0.live]
                    exact ((hsafe.runstack _ fn rest hf).congr hss0).enterLive)
                 | (simp only [current_emit, current_setControl, current_withFrames]
                    exact h.currentLive))
            | exact absurd hstep (by simp)
      case reperform3 e cont =>
        simp only [stepRet, hf] at hstep
        cases hi : (m.withFrames rest).stack? (m.withFrames rest).current with
        | none => simp only [doReperform, hi] at hstep; exact absurd hstep (by simp)
        | some info =>
          cases hp : info.handler.parent with
          | none =>
            cases cont <;> simp only [doReperform, hi, hp] at hstep
            case cont cid =>
              cases hcc : (m.withFrames rest).conts[cid]? with
              | none =>
                simp only [takeCont, hcc] at hstep
                injection hstep with hstep
                subst hstep
                simp only [current_emit, current_setControl, current_withFrames]
                exact h.currentLive
              | some slot =>
                cases slot with
                | none =>
                  simp only [takeCont, hcc] at hstep
                  injection hstep with hstep
                  subst hstep
                  simp only [current_emit, current_setControl, current_withFrames]
                  exact h.currentLive
                | some sid =>
                  simp only [takeCont, hcc] at hstep
                  injection hstep with hstep
                  subst hstep
                  simp only [current_doResumeStack]
                  rw [← hss0.live]
                  refine ((hsafe.reperformRoot e cid rest sid hf ?_).congr hss0).enterLive
                  rw [← hsh0.conts]
                  exact hcc
            all_goals exact absurd hstep (by simp)
          | some p =>
            have hpar : (m.withFrames rest).parentOf (m.withFrames rest).current
                = Option.some p := by
              unfold parentOf handlerOf; rw [hi]; exact hp
            cases v <;> simp only [doReperform, hi, hp] at hstep
            case stack tail =>
              injection hstep with hstep
              subst hstep
              simp only [current_emit, current_applyThree, current_setCurrent]
              rw [← hss0.live p]
              exact hwf0.parentLive _ _ hpar
            all_goals exact absurd hstep (by simp)
      all_goals
        simp only [stepRet, hf, applyValue, takeContUpdate, doDropCont, doAllocStack] at hstep
      all_goals repeat' split at hstep
      all_goals
        first
          | (injection hstep with hstep
             subst hstep
             simp only [pushFrame, applyOne, applyThree, current_emit, current_setControl,
               current_setCell, current_withFrames, current_takeCont, current_freeStack,
               current_setTriple', current_setCurrent]
             exact h.currentLive)
          | exact absurd hstep (by simp)


/-- **A0 §1 P1.2 — a stack that ends is freed before its handler is queued, and stays freed.**
`doReturnToParent`/`doRaiseToParent` free the slot and queue exactly one frame, carrying the
ending stack's *own* `handle_value` / `handle_exn`, on the parent
(`child_return_runs_retc_on_parent`, `child_raise_runs_exnc_on_parent`). This is the run-level
half: the slot never comes back, so `stepRet`/`stepThrow` can never take the completion arm for
that stack a second time, and no later step can queue its handler again. -/
theorem freed_stays_freed [ToString ν] [Add ν] {m m' : Machine ν} {sid : StackId}
    (h : m.WF) (hsafe : ∀ a, Reaches m a → a.Safe)
    (hlt : sid < m.stacks.length) (hdead : m.stack? sid = Option.none)
    (hr : Reaches m m') : m'.stack? sid = Option.none := by
  have key : ∀ a b, (Reaches m a ∧ a.WF ∧ a.stack? sid = Option.none ∧ sid < a.stacks.length) →
      a.step = Sum.inl b →
      (Reaches m b ∧ b.WF ∧ b.stack? sid = Option.none ∧ sid < b.stacks.length) := by
    rintro a b ⟨hra, hwa, hda, hla⟩ hs
    have hsa := hsafe a hra
    have hwb : b.WF := step_wf hwa hsa hs
    have hca : a.current ≠ sid := by
      intro hcc
      have hl := hwa.currentLive
      rw [hcc, hda] at hl
      exact absurd hl (by simp)
    have hcb : b.current ≠ sid := by
      intro hcc
      have hl := step_current_live hwa hsa hs
      rw [hcc, hda] at hl
      exact absurd hl (by simp)
    have hstable := step_stableOff hla hca hcb hs
    refine ⟨Reaches.tail hra hs, hwb, ?_, Nat.lt_of_lt_of_le hla hstable.len⟩
    rcases hstable.keep with hk | hk
    · rw [hda] at hk
      cases hb : b.stack? sid with
      | none => rfl
      | some i => rw [hb] at hk; simp at hk
    · exact hk
  exact (reaches_induction key hr ⟨Reaches.refl m, h, hdead, hlt⟩).2.2.1

/-- **A0 §1 P1.3 — a `perform` with no handler above it is `Unhandled`, on the performing
stack.** `caml_callback`'s effects variant starts a stack whose `Stack_parent` is NULL, so a
handler installed outside that boundary is not on the chain; the machine's spelling of "outside
the boundary" is exactly `parentOf current = none`. The exception is raised *on the performer*
(`interp.c:1327-1332`, `amd64.S:897-908`), no continuation is allocated, and no stack is
switched — so the performer's own traps, and only those, can catch it. -/
theorem perform_at_root_unhandled {m : Machine ν} {info : StackInfo ν} (effV : Value ν)
    (hsi : m.stack? m.current = Option.some info)
    (hroot : info.handler.parent = Option.none) :
    ∃ m', m.doPerform effV = Sum.inl m' ∧
      m'.current = m.current ∧
      m'.control = Control.throw (Value.exn ExnId.unhandled effV) ∧
      m'.conts = m.conts ∧
      m'.stacks = m.stacks ∧
      (m'.stack? m.current).map (·.frames) = Option.some info.frames := by
  obtain ⟨m', hstep, hconts, hstacks, hcur, hctl⟩ := doPerform_root m effV hsi hroot
  refine ⟨m', hstep, hcur, hctl, hconts, hstacks, ?_⟩
  rw [show m'.stack? m.current = m.stack? m.current by
    unfold stack?; rw [hstacks], hsi]
  rfl

/-! ### A0 §1 P1.4 — the trap on the discontinued stack runs first -/

/-- Unwinding pops a non-trap frame and stays on the same stack: `raise_notrace` walks the
current stack's frames (`interp.c:964-1005`), it does not leave the stack until they are
exhausted. -/
theorem step_throw_pops [ToString ν] [Add ν] {m : Machine ν} {e : Value ν} {f : Frame ν}
    {rest : List (Frame ν)} (hctl : m.control = Control.throw e)
    (hfr : (m.stack? m.current).map (·.frames) = Option.some (f :: rest))
    (hnt : ∀ env hn, f ≠ Frame.trap env hn) :
    ∃ M, m.step = Sum.inl M ∧ M.current = m.current ∧ M.control = Control.throw e ∧
      (M.stack? m.current).map (·.frames) = Option.some rest := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp (by
    cases hst : m.stack? m.current with
    | none => rw [hst] at hfr; simp at hfr
    | some info => rfl : (m.stack? m.current).isSome)
  refine ⟨(m.withFrames rest).setControl (Control.throw e), ?_, ?_, ?_, ?_⟩
  · rw [step, hctl]
    cases f <;> simp only [stepThrow, frames_of_framesMap hfr]
    case trap env hn => exact absurd rfl (hnt env hn)
  · exact current_withFrames _ _
  · rfl
  · have := framesMap_withFrames (m := m) rest hi
    rw [current_withFrames] at this
    exact this

/-- Unwinding meets a trap: the handler runs, on this stack (`interp.c:938-946`). -/
theorem step_throw_trap [ToString ν] [Add ν] {m : Machine ν} {e : Value ν}
    {env : List (Value ν)} {hn : Term ν} {rest : List (Frame ν)}
    (hctl : m.control = Control.throw e)
    (hfr : (m.stack? m.current).map (·.frames) = Option.some (Frame.trap env hn :: rest)) :
    ∃ M, m.step = Sum.inl M ∧ M.current = m.current ∧
      M.control = Control.eval (e :: env) hn ∧
      (M.stack? m.current).map (·.frames) = Option.some rest := by
  obtain ⟨info, hi⟩ := isSome_iff_exists.mp (by
    cases hst : m.stack? m.current with
    | none => rw [hst] at hfr; simp at hfr
    | some info => rfl : (m.stack? m.current).isSome)
  refine ⟨?M, ?step, ?cur, ?ctl, ?fr⟩
  case step =>
    rw [step, hctl]
    simp only [stepThrow, frames_of_framesMap hfr]
    rfl
  case cur => exact current_withFrames _ _
  case ctl => rfl
  case fr =>
    have := framesMap_withFrames (m := m) rest hi
    rw [current_withFrames] at this
    exact this

/-- **A0 §1 P1.4 — `discontinue` into a stack carrying a trap runs the trap, and the parent's
`handle_exn` never sees the exception.** The frames above the trap are popped one at a time and
the trap's handler starts, all on the discontinued stack: the completion arm
(`doRaiseToParent`) fires only when the frame list is *empty*, so a trap anywhere in it is
reached first. This is the avatar's cleanups-before-exited ordering. -/
theorem throw_reaches_first_trap [ToString ν] [Add ν] {m : Machine ν} {e : Value ν} :
    ∀ (pre : List (Frame ν)) (env : List (Value ν)) (hn : Term ν) (rest : List (Frame ν)),
      m.control = Control.throw e →
      (m.stack? m.current).map (·.frames) = Option.some (pre ++ Frame.trap env hn :: rest) →
      (∀ f ∈ pre, ∀ env' hn', f ≠ Frame.trap env' hn') →
      ∃ M, Reaches m M ∧ M.current = m.current ∧ M.control = Control.eval (e :: env) hn ∧
        (M.stack? m.current).map (·.frames) = Option.some rest := by
  intro pre
  induction pre generalizing m with
  | nil =>
    intro env hn rest hctl hfr _
    obtain ⟨M, hs, hc, hctl', hfr'⟩ := step_throw_trap hctl (by simpa using hfr)
    exact ⟨M, Reaches.tail (Reaches.refl m) hs, hc, hctl', hfr'⟩
  | cons f pre ih =>
    intro env hn rest hctl hfr hnt
    obtain ⟨M1, hs1, hc1, hctl1, hfr1⟩ :=
      step_throw_pops hctl (by simpa using hfr) (fun env' hn' => hnt f (by simp) env' hn')
    rw [← hc1] at hfr1
    obtain ⟨M, hr, hc, hctl', hfr'⟩ :=
      ih (m := M1) env hn rest hctl1 hfr1 (fun g hg => hnt g (by simp [hg]))
    refine ⟨M, Reaches.head hs1 hr, ?_, hctl', ?_⟩
    · rw [hc, hc1]
    · rw [← hc1]; exact hfr'

/-- **A0 §1 P1.4, end to end.** `Deep.discontinue k e` into a stack whose frames carry a trap:
the exception is raised on that stack, the frames above the trap are popped, and the trap's
handler runs — all before the parent's `handle_exn` could see anything, because the completion
arm needs an empty frame list. -/
theorem discontinue_runs_trap_first [ToString ν] [Add ν] {m : Machine ν} {sid : StackId}
    {pre rest : List (Frame ν)} {env : List (Value ν)} {hn : Term ν} (e : Value ν)
    (hfr : (m.stack? sid).map (·.frames) = Option.some (pre ++ Frame.trap env hn :: rest))
    (hnt : ∀ f ∈ pre, ∀ (env' : List (Value ν)) (hn' : Term ν), f ≠ Frame.trap env' hn') :
    ∃ M, Reaches (m.doResumeStack sid (Value.closure [] (Term.raise (Term.var 0))) e) M ∧
      M.current = sid ∧ M.control = Control.eval (e :: env) hn ∧
      (M.stack? sid).map (·.frames) = Option.some rest := by
  obtain ⟨M1, hr1, hc1, hctl1, hfr1⟩ := deepDiscontinue_raises (m := m) (sid := sid) e hfr
  rw [← hc1] at hfr1
  obtain ⟨M, hr, hc, hctl, hfr'⟩ := throw_reaches_first_trap pre env hn rest hctl1 hfr1 hnt
  refine ⟨M, hr1.trans hr, by rw [hc, hc1], hctl, ?_⟩
  rw [← hc1]; exact hfr'

end Machine

/-! ## 8. `admissibleAt` monotonicity (spike O5 report §9, item 1)

`bytegen.ml:796-804` consults the tail-position flag only at `Preperform`, and only to reject:
`Kreperformterm` when `is_tailcall cont`, `fatal_error` otherwise. So the predicate is monotone
in the polarity — a term admitted where the compiler's continuation is *not* a tail call is
admitted where it is. The induction is over the nested `Term` / `List (EffId × Term ν)` /
`List (ExnId × Term ν)` recursor, which is the piece the O5 spike did not have. -/

namespace Compiler

variable {ν : Type u}

/-- **O5 §9 item 1.** The polarity is monotone: `nonTail` is the strictly harder position. -/
theorem admissibleAt_mono (t : Term ν) :
    admissibleAt TailPosition.nonTail t = true → admissibleAt TailPosition.tail t = true := by
  induction t using Term.rec
    (motive_2 := fun cls => admissibleEffClauses TailPosition.nonTail cls = true →
      admissibleEffClauses TailPosition.tail cls = true)
    (motive_3 := fun cls => admissibleExnClauses TailPosition.nonTail cls = true →
      admissibleExnClauses TailPosition.tail cls = true)
    (motive_4 := fun p => admissibleAt TailPosition.nonTail p.2 = true →
      admissibleAt TailPosition.tail p.2 = true)
    (motive_5 := fun p => admissibleAt TailPosition.nonTail p.2 = true →
      admissibleAt TailPosition.tail p.2 = true) <;>
    simp_all [admissibleAt, admissibleEffClauses, admissibleExnClauses]

/-- The corollary the corpus `#guard`s: an admissible compilation unit is admissible as a
function body. -/
theorem admissible_admissibleAt_tail (t : Term ν) (h : Admissible t = true) :
    admissibleAt TailPosition.tail t = true :=
  admissibleAt_mono t h

end Compiler

end OCaml5
