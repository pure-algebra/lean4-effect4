import Effect4.Program.Typing.Parts
import Effect4.Laws.Program.Typing.Call
import Effect4.Laws.Program.Typing.Table
import Effect4.Laws.Program.Definitions
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Parts — the call instance at every call of a whole program

`Program/Typing/Parts.lean` splits a whole program into its parts, as the module check checks
them, and reads the focus and the call instance at the part that holds an address. This module
has the laws.

## Placement

Concept `host-session-protocol`; property: reply admission at the call's checked instance
(decisions rows 323 and 333). Requirement R6.

- **`block-call-instance`** (claim, role preservation; pointer `checkModule_programCallAt`). On a
  program that the module check admits, `programCallAt` answers at every call, in a definition's
  body, in the main program, and in a program with no block. The instance's operation is the
  call's. A step of the claim `reply-at-call-instance`. Consumers: the session's call table
  (`Api.HostSession.callTable`), through `lookup_programCalls`; the session's completeness
  (`Api.HostSession.instanceAt_complete`).
- Reach: every signature, every program that `Checker.checkModule` admits, every address of a
  call, at the root's empty environment. Rows 323 and 328.
- It does not establish: that the expansion of layer references keeps a call at its address
  (`expansion-keeps-call`); handle rows; delayed cell reads (row 100); anything of a run.
- Unlocks: R6, typed replies for every program built with installed definitions; R14, the focus
  inside such a program; R10, through a module law read on sessions (seat HOST's P3).

The red control is part B of seat HOST's probe
(`docs/research/2026-10-08-host-authoring-boundary/BoundaryProbe.lean`): before this module the
call table of a program with a block was empty. `Test/Program/PartsControls.lean` reads the law
at a program with a block.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-! ## The part holds the node -/

/-- **A body holds its address**: the node at an address of a block's bodies' spine is the node
at the rest of the address in the body that `Part.bodyAt` answers. A step of `Eff.partAt_at`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Part.bodyAt_at {sig : Signature Op} {part : Part Op} {rest : List Nat} :
    ∀ {decls : List DefDecl} {bodies : Effs Op} {path : List Nat},
      Part.bodyAt sig decls bodies path = some (part, rest) →
      (Node.effs bodies).at_ path = (Node.eff part.program).at_ rest := by
  intro decls
  induction decls with
  | nil =>
    intro bodies path h
    cases bodies <;> cases h
  | cons d ds ih =>
    intro bodies path h
    cases bodies with
    | nil => cases h
    | cons body bodies =>
      cases path with
      | nil => cases h
      | cons i r =>
        rcases i with _ | _ | i
        · cases h
          rfl
        · have hrest := ih (bodies := bodies) (path := r) h
          exact hrest
        · cases h

/-- **The part holds the node at the address**: the node at an address of a program is the node
at the rest of the address in the part that `Eff.partAt` answers. A step of
`programCallAt_rowTy`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Eff.partAt_at {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {part : Part Op} {rest : List Nat} (h : p.partAt s env0 path = some (part, rest)) :
    (Node.eff p).at_ path = (Node.eff part.program).at_ rest := by
  unfold Eff.partAt at h
  split at h
  · split at h
    · exact Part.bodyAt_at h
    · cases h
      rfl
    · cases h
  · cases h
    rfl

/-- **A typed program with no block is its own part**: `HasTy` derives no type for a block, so
the part at every address is the program itself. A step of `hasTy_programCallAt`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Eff.partAt_of_hasTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    (hp : HasTy s env0 p T) (path : List Nat) :
    p.partAt s env0 path = some (⟨s, env0, p⟩, path) := by
  unfold Eff.partAt
  split
  · cases hp
  · rfl

/-! ## The instance at a part -/

/-- **Where `programCallAt` answers, the node is a call typed at its part.** The node at the
address is a `perform` of the instance's operation. In the part that holds the address, the
request has the instance's request type, and the row check at the part's signature answers the
instance's columns and bindings. It is `callAt_rowTy` at the part. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem programCallAt_rowTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {c : CallInstance Op} (h : programCallAt s env0 p path = some c) :
    ∃ (part : Part Op) (rest : List Nat) (request : Term) (env : TyEnv) (t : EffTy),
      p.partAt s env0 path = some (part, rest) ∧
      (Node.eff p).at_ path = some (.eff (.perform c.op request)) ∧
      (Node.eff part.program).envAt part.sig (.env part.env) rest = some (.env env) ∧
      termTy part.sig env request = some c.request ∧
      rowTy (part.sig.rowOf c.op) c.request (part.sig.termUse env c.op) = some t ∧
      t.answer = c.answer ∧ t.error = c.error ∧
      rowBindings (part.sig.rowOf c.op) c.request (part.sig.termUse env c.op) =
        some c.bindings := by
  unfold programCallAt at h
  obtain ⟨⟨part, rest⟩, hpart, hcall⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨request, env, t, hat, henv, hreq, hrow, ha, he, hb⟩ := callAt_rowTy hcall
  exact ⟨part, rest, request, env, t, hpart, (Eff.partAt_at hpart).trans hat, henv, hreq, hrow,
    ha, he, hb⟩

/-- **On a typed program `callAt` answers at every call**, with the call's operation. The focus
answers there (`hasTy_focusAt`), and the rule of `perform` gives the request's type and the row
check's answer, whose bindings `rowBindings` answers (`checkRow_rowBindings`). A step of
`block-call-instance`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem hasTy_callAt {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    {path : List Nat} {op : Op} {request : Term} (hp : HasTy s env0 p T)
    (hat : (Node.eff p).at_ path = some (.eff (.perform op request))) :
    ∃ c, callAt s env0 p path = some c ∧ c.op = op := by
  obtain ⟨env, t, hf⟩ := hasTy_focusAt hp hat
  cases (focusAt_typed hf).2 with
  | perform _hdom hterm hrow =>
    rename_i requestTy
    have hcheck : checkRow (s.rowOf op) requestTy (s.termUse env op) = .ok t := by
      unfold rowTy at hrow
      cases hc : checkRow (s.rowOf op) requestTy (s.termUse env op) with
      | error _ => rw [hc] at hrow; cases hrow
      | ok t' => rw [hc] at hrow; cases hrow; rfl
    obtain ⟨σ, hσ, -, -⟩ := checkRow_rowBindings hcheck
    refine ⟨⟨op, requestTy, t.answer, t.error, σ⟩, ?_, rfl⟩
    unfold callAt
    simp only [hf, Option.bind_some, hterm, hσ, Option.map_some]

/-- **A typed spine of bodies holds a typed body at every address of a program inside it**: the
body that `Part.bodyAt` answers is typed at the block's signature and its declared request, and
it holds the node. A step of `block-call-instance`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem BodiesHasTy.bodyAt {sig : Signature Op} :
    ∀ {decls : List DefDecl} {bodies : Effs Op} {path : List Nat} {q : Eff Op},
      BodiesHasTy sig decls bodies → (Node.effs bodies).at_ path = some (.eff q) →
      ∃ (part : Part Op) (rest : List Nat) (T : EffTy),
        Part.bodyAt sig decls bodies path = some (part, rest) ∧
        HasTy part.sig part.env part.program T ∧ (Node.eff part.program).at_ rest = some (.eff q)
  | _, _, [], _, .nil, h => by cases h
  | _, _, _ :: _, _, .nil, h => by cases h
  | _, _, [], _, .cons _ _ _ _, h => by cases h
  | _, _, 0 :: rest, _, .cons (body := body) (t := t) _ hb _ _, h =>
    ⟨⟨sig, _, body⟩, rest, t, rfl, hb, h⟩
  | _, _, 1 :: _, _, .cons _ _ _ hrest, h => by
    have hbody := BodiesHasTy.bodyAt hrest h
    exact hbody
  | _, _, (_ + 2) :: _, _, .cons _ _ _ _, h => by cases h

/-! ## The claim -/

/-- **On a typed whole program `programCallAt` answers at every call**, with the call's
operation: in a definition's body at the block's signature and its request, in the main program
at the block's signature, and in a program with no block. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem moduleHasTy_programCallAt {s : Signature Op} {p : Eff Op} {T : EffTy} {path : List Nat}
    {op : Op} {request : Term} (hp : ModuleHasTy s p T)
    (hat : (Node.eff p).at_ path = some (.eff (.perform op request))) :
    ∃ c, programCallAt s [] p path = some c ∧ c.op = op := by
  cases hp with
  | defs hb hm =>
    match path, hat with
    | [], hat => cases hat
    | 0 :: rest, hat =>
      obtain ⟨part, rest', T', hpart, hty, hat'⟩ := hb.bodyAt hat
      obtain ⟨c, hc, hop⟩ := hasTy_callAt hty hat'
      refine ⟨c, ?_, hop⟩
      unfold programCallAt Eff.partAt
      simp only [hpart, Option.bind_some, hc]
    | 1 :: rest, hat =>
      obtain ⟨c, hc, hop⟩ := hasTy_callAt hm hat
      exact ⟨c, hc, hop⟩
    | (_ + 2) :: _, hat => cases hat
  | plain h =>
    obtain ⟨c, hc, hop⟩ := hasTy_callAt h hat
    refine ⟨c, ?_, hop⟩
    unfold programCallAt
    rw [Eff.partAt_of_hasTy h path]
    exact hc

/-- **The claim `block-call-instance`.** On a program that the module check admits, the call
instance answers at every call, with the call's operation: inside a definition's body, in the
main program of a block, and in a program with no block. Before this law the session's call
table missed every call of a program with a block (seat HOST's probe, part B). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem checkModule_programCallAt {s : Signature Op} {p : Eff Op} {T : EffTy}
    {path : List Nat} {op : Op} {request : Term} (hp : Checker.checkModule s p = .ok T)
    (hat : (Node.eff p).at_ path = some (.eff (.perform op request))) :
    ∃ c, programCallAt s [] p path = some c ∧ c.op = op :=
  moduleHasTy_programCallAt (checkModule_sound s p T hp) hat

/-! ## The table -/

/-- A lookup in a table made by `filterMap` over a list of addresses answers the function at an
address of the list, and nothing elsewhere. A step of `lookup_programCalls`. -/
theorem lookup_filterMap_pair {β : Type} (f : List Nat → Option β) (o : List Nat) :
    ∀ l : List (List Nat),
      (l.filterMap fun a => (f a).map fun c => (a, c)).lookup o = if o ∈ l then f o else none
  | [] => rfl
  | a :: l => by
    have ih := lookup_filterMap_pair f o l
    by_cases hoa : o = a
    · subst hoa
      cases hf : f o with
      | none =>
        rw [List.filterMap_cons, hf, Option.map_none, ih, if_pos List.mem_cons_self]
        split
        · exact hf
        · rfl
      | some c =>
        -- `List.lookup_cons_self` reaches `Classical.choice` through its `ReflBEq` instance
        have hself : (o == o) = true := beq_iff_eq.mpr rfl
        rw [List.filterMap_cons, hf, Option.map_some, if_pos List.mem_cons_self]
        simp only [List.lookup, hself]
    · have hb : (o == a) = false := beq_eq_false_iff_ne.mpr hoa
      have rhs : (if o ∈ a :: l then f o else none) = (if o ∈ l then f o else none) := by
        by_cases hl : o ∈ l
        · rw [if_pos (List.mem_cons_of_mem a hl), if_pos hl]
        · rw [if_neg (fun h => hl ((List.mem_cons.mp h).resolve_left hoa)), if_neg hl]
      rw [rhs, ← ih]
      cases hf : f a with
      | none => rw [List.filterMap_cons, hf, Option.map_none]
      | some c =>
        rw [List.filterMap_cons, hf, Option.map_some]
        simp only [List.lookup, hb]

/-- **The call table answers at an address exactly what `programCallAt` answers there**: a
call's address is an address of the program (`mem_addresses_iff`), so the table misses none. A
step of `reply-at-call-instance`; consumer: `Api.HostSession.start_callInstance`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem lookup_programCalls (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (o : List Nat) :
    (programCalls s env0 p).lookup o = programCallAt s env0 p o := by
  unfold programCalls
  rw [lookup_filterMap_pair]
  split
  · rfl
  · rename_i hno
    cases hc : programCallAt s env0 p o with
    | none => rfl
    | some c =>
      obtain ⟨_, _, request, _, _, _, hat, _⟩ := programCallAt_rowTy hc
      exact absurd ((mem_addresses_iff (.eff p) o).mpr (by rw [hat]; rfl)) hno

end Effect4.Program
