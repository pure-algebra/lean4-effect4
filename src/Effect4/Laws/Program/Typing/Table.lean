import Effect4.Program.Typing.Table
import Effect4.Program.Typing.Agreement
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.Typing.Focus
import Effect4.Laws.Program.Typing.CheckSound
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Table — the laws of the address table, of the refusals and of the slots

`Program/Typing/Table.lean` computes the address table of a program (`table`), its distinct
refusals (`refusals`) and the environment of a term slot (`Node.extSlotEnv`). This module
proves what a caller reads from each:

- **The addresses.** `Node.addresses` lists exactly the addresses of a node's nodes
  (`mem_addresses_iff`). It is the path fold at the yield of one path
  (`addresses_eq_foldList`), so the statement is `Node.mem_foldList_iff`
  (`Laws/Program/PathFold.lean`) at that yield.
- **The refusals.** The head of the list is the located refusal of `explain`
  (`refusals_head`), and the list is empty exactly when the checker admits the program
  (`refusals_nil_iff`). On a typed program no entry holds a refusal
  (`table_result_refusal_none_of_hasTy`).
- **The slots.** On a typed node, the term in a slot has a type at the slot's environment
  (`hasTy_extSlotEnv`).

Placement (AGENTS.md, Trust): concept initial-algebras-folds (`docs/core/semantics.md` §2.7),
requirement R14. The claims are `address-table` (pointer `refusals_nil_iff`) and
`term-slot-environment` (pointer `hasTy_extSlotEnv`). The consumers are the query driver
(slice QUERY of `docs/research/2026-10-06-next-slices-plan.md`), the TypeScript printer at an
eliminator inside a term (slice PRINT), and a pass that answers every address (slice PASS),
whose specification is the table.

What the module does not establish:

- an order of the addresses, or of the refusals after the head;
- an entry after a refused sibling: it is not reached, and no law marks it;
- the frame of an edit: that an entry outside a replaced focus keeps its answer. It is the
  proposed claim `edit-frame`, and no theorem states it;
- that the slot's environment is the only one at which the slot's term has a type.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-! ## The addresses -/

/-- The yield of the address list: at every sort, the node's own path. -/
def addressYield : PathYield Op (List Nat) where
  eff _ p := [p]
  stmt _ p := [p]
  stmts _ p := [p]
  effs _ p := [p]
  action _ p := [p]
  layer _ p := [p]
  layers _ p := [p]

/-- `Node.addresses` is the path fold at `addressYield`, from the empty path. A step of
`address-table`. Its consumer is `mem_addresses_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem addresses_eq_foldList (n : Node Op) : Node.addresses n = n.foldList addressYield [] := by
  cases n <;> rfl

/-- The address yield at a node is the node's path alone. A step of `address-table`. Its
consumer is `mem_addresses_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem yieldAt_addressYield (m : Node Op) (p : List Nat) :
    Node.yieldAt addressYield m p = [p] := by
  cases m <;> rfl

/-- **The address list holds exactly the addresses of a node's nodes**: a path is in
`Node.addresses` exactly when a node stands at it. It is `Node.mem_foldList_iff` at the address
yield. It says nothing of the order of the list. A step of `address-table`. Its consumers are
the table's entries, each of which stands at an address, and the query driver (slice QUERY). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem mem_addresses_iff (n : Node Op) (a : List Nat) :
    a ∈ Node.addresses n ↔ (n.at_ a).isSome = true := by
  rw [addresses_eq_foldList, Node.mem_foldList_iff]
  constructor
  · rintro ⟨path, m, hat, hx⟩
    rw [yieldAt_addressYield, List.nil_append, List.mem_singleton] at hx
    rw [hx, hat]
    rfl
  · intro h
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    refine ⟨a, m, hm, ?_⟩
    rw [yieldAt_addressYield, List.nil_append]
    exact List.mem_singleton_self a

/-- The address list of a program starts at the root. A step of `address-table`. Its consumer
is `table_head`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem addresses_eff_head (p : Eff Op) : ∃ rest, Node.addresses (.eff p) = [] :: rest := by
  cases p <;> exact ⟨_, rfl⟩

/-! ## The table and the refusals -/

/-- The table of a program starts with the root's entry: the root's environment, and the
checker's answer on the whole program. A step of `address-table`. Its consumer is
`refusals_head`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_head (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    ∃ rest, table s env0 p = ⟨[], some (.env env0), some (Checker.check s env0 [] p)⟩ :: rest := by
  obtain ⟨rest, h⟩ := addresses_eff_head p
  unfold table
  rw [h]
  exact ⟨_, rfl⟩

/-- On a typed program no entry of the table holds a refusal: the checker answers a type at
every address of a program (`hasTy_focusAt`). A step of `address-table`. Its consumer is
`refusals_of_hasTy`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_result_refusal_none_of_hasTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op}
    {T : EffTy} (hp : HasTy s env0 p T) {e : Table.Entry} (he : e ∈ table s env0 p) :
    e.result.bind Checker.refusal = none := by
  unfold table at he
  simp only [List.mem_map] at he
  obtain ⟨a, -, rfl⟩ := he
  dsimp only
  split
  · rename_i q tys hat henv
    obtain ⟨env, t, hf⟩ := hasTy_focusAt hp hat
    obtain ⟨-, henv', hty⟩ := focusAt_eq_some.mp hf
    have hsame : env = tys := by
      injection henv'.symm.trans henv with h1
      injection h1
    subst hsame
    have hchk := check_complete s q env t (effTy_sound s q env t hty) a
    rw [hchk]
    rfl
  · rfl

/-- On a typed program the list of refusals is empty. A step of `address-table`. Its consumers
are `refusals_head` and `refusals_nil_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem refusals_of_hasTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    (hp : HasTy s env0 p T) : refusals s env0 p = [] := by
  unfold refusals
  have hnil : (table s env0 p).filterMap (fun e => e.result.bind Checker.refusal) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e he
    exact table_result_refusal_none_of_hasTy hp he
  rw [hnil]
  rfl

/-- **The head of the list of refusals is the located refusal of `explain`.** The root's entry
is first in the table, and its answer is the checker's on the whole program. It says nothing
of the order after the head. A step of `address-table`. Its consumers are `refusals_nil_iff`
and the query driver's refusals (slice QUERY). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem refusals_head (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    (refusals s env0 p).head? = explain s env0 p := by
  cases h : explain s env0 p with
  | none =>
    have hty : (effTy s env0 p).isSome = true := (explain_none_iff s env0 p).mp h
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hty
    rw [refusals_of_hasTy (effTy_sound s p env0 T hT)]
    rfl
  | some ref =>
    unfold refusals
    obtain ⟨rest, htable⟩ := table_head s env0 p
    rw [htable]
    simp only [List.filterMap_cons]
    have href : Checker.refusal (Checker.check s env0 [] p) = some ref := h
    simp only [Option.bind_some, href]
    rw [List.eraseDups_cons]
    rfl

/-- **The list of refusals is empty exactly when the checker admits the program.** It is the
table's form of `explain_none_iff`. The pointer of the claim `address-table`. Its consumer is
the query driver's refusals (slice QUERY). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem refusals_nil_iff (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    refusals s env0 p = [] ↔ (effTy s env0 p).isSome = true := by
  constructor
  · intro h
    have hhead : (refusals s env0 p).head? = none := by rw [h]; rfl
    rw [refusals_head] at hhead
    exact (explain_none_iff s env0 p).mp hhead
  · intro h
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp h
    exact refusals_of_hasTy (effTy_sound s p env0 T hT)

/-! ## The slots -/

/-- **On a typed node, the term in a slot has a type at the slot's environment.** The slot
table answers an environment at each slot that the node has (`Node.extSlotTerm`), and the
typing rule of the node types the slot's term there: the test of `catchIf`, the test, the step
and the result of `iterate`, and an operation's own term at the instance of its parameter. The
proof is the inversion of `HasTy` at the three constructors. The pointer of the claim
`term-slot-environment`. Its consumer is the TypeScript printer at an eliminator inside such a
term (slice PRINT).

It does not say that the environment is the only one at which the term has a type, and it
says nothing at a node that the checker refuses. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem hasTy_extSlotEnv {s : Signature Op} {env : TyEnv} {p : Eff Op} {T : EffTy}
    (hp : HasTy s env p T) {slot : ExtSlot} {t : Term}
    (ht : (Node.eff p).extSlotTerm s slot = some t) :
    ∃ env' ty, (Node.eff p).extSlotEnv s env slot = some env' ∧ termTy s env' t = some ty := by
  cases hp with
  | catchIf hb htest _ _ =>
    cases slot <;> simp only [Node.extSlotTerm, Option.some.injEq, reduceCtorEq] at ht
    subst ht
    exact ⟨_, _, by simp only [Node.extSlotEnv, effTy_complete _ _ _ _ hb, Option.map_some], htest⟩
  | iterate h0 htest hb hstep hres _ _ =>
    cases slot <;> simp only [Node.extSlotTerm, Option.some.injEq, reduceCtorEq] at ht <;>
      subst ht
    · exact ⟨_, _, by simp only [Node.extSlotEnv, h0, Option.map_some], htest⟩
    · exact ⟨_, _, by simp only [Node.extSlotEnv, h0, effTy_complete _ _ _ _ hb, Option.map_some],
        hstep⟩
    · exact ⟨_, _, by simp only [Node.extSlotEnv, h0, Option.map_some], hres⟩
  | perform _ hreq hrow =>
    cases slot <;> simp only [Node.extSlotTerm, Option.map_eq_some_iff, reduceCtorEq] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    simp only [rowTy, checkRow, Signature.termUse, hb, Option.map_some] at hrow
    split at hrow
    · cases hrow
    · rename_i σ hσ
      cases hty : termTy s (env ++ [TermUse.instParam b.param σ]) b.term with
      | none =>
        simp only [bindTerm, hty] at hrow
        cases hrow
      | some r => exact ⟨_, r, by simp only [Node.extSlotEnv, hb, hreq, hσ], hty⟩
  | _ => cases slot <;> simp only [Node.extSlotTerm, reduceCtorEq] at ht

end Effect4.Program
