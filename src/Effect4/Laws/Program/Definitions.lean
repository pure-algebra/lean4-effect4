import Effect4.Program.Definitions
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Definitions — a definition block is a conservative extension, with its judgment

`Program/Definitions.lean` defines a program's definition block and its whole-module check
(decisions row 328). This module holds the two typing laws that the block owes before it lands
(row 328, point 5).

| Statement | In words | From |
| --- | --- | --- |
| `defs_conservative` (G1) | a program that invokes no definition is checked the same at a block's signature, refusals included | `cata_eff_congr_on` |
| `checkModule_conservative` | G1 at the root: a module whose bodies check has its main program's own verdict | `defs_conservative` |
| `checkModule_eq_check` | a program with no block is checked as the checker checks it | the definition |
| `invoke_hasTy` (G2) | an invocation has the type of its definition's declared row, at its request's type | `HasTy.perform` |
| `checkModule_sound` (G2) | what the module check accepts, the module judgment derives | `check_sound` |
| `checkModule_complete` (G2) | what the module judgment derives, the module check accepts | `check_complete` |

The block's signature differs from the signature only at an invocation: its domain bit and its
row (`Signature.withDefs`). So the checker's two algebras agree field by field on every read
except an invocation's (`defs_check_agreeOn`). Its terms, causes and requirement rows agree
through the signature with an empty domain, which both signatures extend.

The module judgment `ModuleHasTy` is a judgment beside `HasTy`, not a rule of it: a block stands
at the root only, and `HasTy` derives no type for a block below the root.

## Placement

Concept `initial-algebras-folds`: the checker is one fold of the program, and each law reads that
fold at two signatures. Requirement R2 (C3 for a block) and R1 at a signature with a block, under
decisions row 328.

- **`defs-conservative`** (claim, role compatibility; pointer `defs_conservative`). Reach: every
  signature, every block, environment and path, for a program with no node that performs an
  invocation (`NoInvocation`). Refusals are included, and no service key is assumed typed. It
  does not establish anything of the block's own bodies, any run or any meaning. Consumer: G2's
  soundness at the extended signature, and a program that gains a block.
- **`invocation-rule`** (claim, role compatibility; pointer `invoke_hasTy`). Reach: the
  declarative judgment at a block's signature, a closed declaration (row 328, the first stage),
  every environment. It does not establish any run or meaning, a generic definition (G8), or that
  a declared row is inhabited (row 127).
- **`module-check`** (claim, role compatibility; pointers `checkModule_sound` and
  `checkModule_complete`). Reach: every signature and every program at its root. It does not
  establish a block below the root, which the checker refuses (`TypeReason.definitionBlock`).
  Consumer: the whole program's typing (`typeOfProgram`), and with it admission, and G3.

No statement here names a run. The host boundary stays where `docs/core/host-boundary.md` puts
it.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing
open Effect4.Laws.Auto

variable {Op : Type}

/-! ## The block's signature -/

/-- At an operation that invokes no definition, the block's signature has the signature's own
domain bit. A step of `defs_check_agreeOn`. -/
theorem Signature.withDefs_dom_of_none (sig : Signature Op) (decls : List DefDecl) {op : Op}
    (h : sig.callOf op = none) : (sig.withDefs decls).dom op = sig.dom op := by
  simp only [Signature.withDefs, h]

/-- At an operation that invokes no definition, the block's signature has the signature's own
row. A step of `defs_check_agreeOn`. -/
theorem Signature.withDefs_rowOf_of_none (sig : Signature Op) (decls : List DefDecl) {op : Op}
    (h : sig.callOf op = none) : (sig.withDefs decls).rowOf op = sig.rowOf op := by
  simp only [Signature.withDefs, h]

/-- The invocation of definition `k` is in the block's domain exactly when the block has a
definition `k`. A step of `invoke_hasTy`. -/
theorem Signature.withDefs_dom_call (sig : Signature Op) (decls : List DefDecl) {op : Op}
    {k : Nat} (h : sig.callOf op = some k) :
    (sig.withDefs decls).dom op = decide (k < decls.length) := by
  simp only [Signature.withDefs, h]

/-- The invocation of definition `k` reads the row that definition `k` declares, in normal form.
A step of `invoke_hasTy`. -/
theorem Signature.withDefs_rowOf_call (sig : Signature Op) (decls : List DefDecl) {op : Op}
    {k : Nat} {d : DefDecl} (h : sig.callOf op = some k) (hd : decls[k]? = some d) :
    (sig.withDefs decls).rowOf op = d.row.normalizeTypes := by
  simp only [Signature.withDefs, h, hd]

/-- **An empty block changes nothing** at a signature that keeps every invocation outside its
domain, as an application's does (`SigApp.signature_callsOutside`). A step of `rootCode_typed`
(`Typed/Assembly.lean`): the source's signature of a program with no block is its tables'. -/
theorem Signature.withDefs_nil (sig : Signature Op)
    (h : ∀ op k, sig.callOf op = some k → sig.dom op = false) : sig.withDefs [] = sig := by
  have e1 : (sig.withDefs []).rowOf = sig.rowOf := funext fun op => by
    cases hc : sig.callOf op with
    | none => exact sig.withDefs_rowOf_of_none [] hc
    | some k => simp only [Signature.withDefs, hc, List.getElem?_nil]
  have e2 : (sig.withDefs []).dom = sig.dom := funext fun op => by
    cases hc : sig.callOf op with
    | none => exact sig.withDefs_dom_of_none [] hc
    | some k =>
      rw [sig.withDefs_dom_call [] hc, h op k hc]
      exact decide_eq_false (Nat.not_lt_zero k)
  show { sig with rowOf := (sig.withDefs []).rowOf, dom := (sig.withDefs []).dom } = sig
  rw [e1, e2]

/-- An application's signature keeps every invocation outside its domain (`nativeSignature`). -/
theorem SigApp.signature_callsOutside (app : SigApp) :
    ∀ op k, app.signature.callOf op = some k → app.signature.dom op = false := by
  intro op k h
  cases op with
  | call _ => rfl
  | _ => cases h

/-- The signature with an empty domain and every other field of `sig`. Both `sig` and its block's
signature extend it, so the reads that do not touch a row agree. A step of `defs_check_agreeOn`. -/
def Signature.emptyDom (sig : Signature Op) : Signature Op := { sig with dom := fun _ => false }

theorem Signature.emptyDom_extends (sig : Signature Op) : SigExtends sig.emptyDom sig :=
  ⟨rfl, rfl, rfl, fun _ h => absurd h Bool.false_ne_true, fun _ _ h => h, rfl, rfl⟩

theorem Signature.emptyDom_extends_withDefs (sig : Signature Op) (decls : List DefDecl) :
    SigExtends sig.emptyDom (sig.withDefs decls) :=
  ⟨rfl, rfl, rfl, fun _ h => absurd h Bool.false_ne_true, fun _ _ h => h, rfl, rfl⟩

/-! ## G1: conservative -/

/-- **A program that invokes no definition**: no operation it performs is an invocation of
`sig` (`Signature.callOf`). Every service key is allowed. -/
def NoInvocation (sig : Signature Op) (e : Eff Op) : Prop :=
  cata_eff (readsAlg (fun op => sig.callOf op = none) (fun _ => True)) e

/-- **Along a block the checker's two algebras agree on every read but an invocation's**: field
by field, outright where the field reads no row, and guarded at a `perform`. The step of G1. -/
theorem defs_check_agreeOn (sig : Signature Op) (decls : List DefDecl) :
    (Checker.check.alg (sig.withDefs decls)).AgreeOn (Checker.check.alg sig)
      (fun op => sig.callOf op = none) (fun _ => True) := by
  have h₁ := sig.emptyDom_extends_withDefs decls
  have h₂ := sig.emptyDom_extends
  have hterm : Checker.term? (sig.withDefs decls) = Checker.term? sig :=
    (term?_ext h₁).trans (term?_ext h₂).symm
  have hcause : Checker.cause? (sig.withDefs decls) = Checker.cause? sig :=
    (cause?_ext h₁).trans (cause?_ext h₂).symm
  have hbody : bodyRequires (sig.withDefs decls) = bodyRequires sig :=
    funext fun t => (h₁.bodyRequires t).trans (h₂.bodyRequires t).symm
  have huse : ∀ env op, (sig.withDefs decls).termUse env op = sig.termUse env op :=
    fun env op => (h₁.termUse env op).trans (h₂.termUse env op).symm
  have hservice : (sig.withDefs decls).serviceTy = sig.serviceTy := rfl
  have hscope : (sig.withDefs decls).scopeKey = sig.scopeKey := rfl
  exact {
    eff_succeed := by simp only [Checker.check.alg, hterm]
    eff_fail := by simp only [Checker.check.alg, hterm]
    eff_failCause := by simp only [Checker.check.alg, hcause]
    eff_sync := by simp only [Checker.check.alg, hterm]
    eff_suspend := rfl
    eff_perform := fun op hn => by
      simp only [Checker.check.alg, hterm, sig.withDefs_dom_of_none decls hn,
        sig.withDefs_rowOf_of_none decls hn, huse]
    eff_bind := rfl
    eff_gen := rfl
    eff_catchCause := rfl
    eff_matchCause := rfl
    eff_onExit := rfl
    eff_exit := rfl
    eff_uninterruptible := rfl
    eff_interruptible := rfl
    eff_yieldNow := rfl
    eff_awaitFiber := by simp only [Checker.check.alg, hterm]
    eff_withFiber := rfl
    eff_scoped := by simp only [Checker.check.alg, hbody]
    eff_acquireRelease := by simp only [Checker.check.alg, hscope]
    eff_provideLayer := rfl
    eff_service := fun _ _ => by simp only [Checker.check.alg, hservice]
    eff_provideService := fun _ _ => by simp only [Checker.check.alg, hservice, hterm]
    eff_catchIf := by simp only [Checker.check.alg, hterm]
    eff_select := by simp only [Checker.check.alg, hterm]
    eff_iterate := by simp only [Checker.check.alg, hterm]
    eff_restore := by simp only [Checker.check.alg, hterm]
    eff_defs := rfl
    stmt_bindYield := rfl
    stmt_yieldDiscard := rfl
    stmt_ret := by simp only [Checker.check.alg, hterm]
    stmt_ifElse := by simp only [Checker.check.alg, hterm]
    stmt_whileTrue := rfl
    stmt_breakLoop := rfl
    stmts_nil := rfl
    stmts_cons := rfl
    effs_nil := rfl
    effs_cons := rfl
    action_fork := rfl
    action_forkIn := by simp only [Checker.check.alg, hterm]
    action_forkScoped := by simp only [Checker.check.alg, hscope]
    action_runIn := by simp only [Checker.check.alg, hterm]
    action_interrupt := by simp only [Checker.check.alg, hterm]
    action_interruptScoped := by simp only [Checker.check.alg, hterm]
    action_interruptAll := by simp only [Checker.check.alg, hterm]
    action_awaitAll := by simp only [Checker.check.alg, hterm]
    action_awaitAllFailFast := by simp only [Checker.check.alg, hterm]
    action_snapshotChildren := rfl
    action_awaitNewChildren := by simp only [Checker.check.alg, hterm]
    action_raceAll := rfl
    action_setContext := by simp only [Checker.check.alg, hterm]
    action_getContext := rfl
    action_getId := rfl
    action_closeScope := by simp only [Checker.check.alg, hterm]
    action_getInterruptible := rfl
    layer_succeed := fun _ _ => by simp only [Checker.check.alg, hservice]
    layer_effect := fun _ _ => by simp only [Checker.check.alg, hservice, hbody]
    layer_effectDiscard := by simp only [Checker.check.alg, hbody]
    layer_provide := rfl
    layer_provideMerge := rfl
    layer_merge := rfl
    layer_fresh := rfl
    layer_orDie := rfl
    layer_ref := rfl
    layer_mergeAll := rfl
    layers_nil := rfl
    layers_cons := rfl
  }

/-- **G1, the claim `defs-conservative`** (decisions row 328, point 5): a program that invokes no
definition is checked the same at any block's signature, refusals included, at every
environment and path. No service key is assumed typed: the block's signature changes only an
invocation's domain bit and row. -/
@[semantics "initial-algebras-folds" (requirement := R2)]
theorem defs_conservative (sig : Signature Op) (decls : List DefDecl) {e : Eff Op}
    (hn : NoInvocation sig e) (env : TyEnv) (p : List Nat) :
    Checker.check (sig.withDefs decls) env p e = Checker.check sig env p e := by
  rw [Checker.check.eq_cata, Checker.check.eq_cata]
  rw [cata_eff_congr_on (defs_check_agreeOn sig decls) e hn]

/-- A program with no block is checked as the checker checks it, at the root. -/
@[semantics "initial-algebras-folds" (requirement := R2)]
theorem checkModule_eq_check (sig : Signature Op) {e : Eff Op}
    (h : ∀ decls bodies main, e ≠ .defs decls bodies main) :
    Checker.checkModule sig e = Checker.check sig [] [] e := by
  unfold Checker.checkModule
  split
  · exact absurd rfl (h _ _ _)
  · rfl

/-- **G1 at the root**: a module whose bodies the checker admits, and whose main program invokes
no definition, has its main program's own verdict at the main program's path, refusals
included. -/
@[semantics "initial-algebras-folds" (requirement := R2)]
theorem checkModule_conservative (sig : Signature Op) (decls : List DefDecl) (bodies : Effs Op)
    {main : Eff Op} (hlen : decls.length = bodies.toList.length)
    (hb : Checker.checkBodies (sig.withDefs decls) [0] decls bodies = .ok ())
    (hn : NoInvocation sig main) :
    Checker.checkModule sig (.defs decls bodies main) = Checker.check sig [] [1] main := by
  rw [← defs_conservative sig decls hn [] [1]]
  simp only [Checker.checkModule, hlen, hb]
  rfl

/-! ## G2: the invocation rule and the module judgment -/

/-- **G2, the claim `invocation-rule`** (decisions row 328): at a block's signature, the
invocation of definition `k` has the type of the row that definition `k` declares, in normal
form, at its request's type. It is `HasTy.perform` read at the block's signature: no rule is
added to `HasTy`. -/
@[semantics "initial-algebras-folds" (requirement := R1)]
theorem invoke_hasTy (sig : Signature Op) (decls : List DefDecl) {op : Op} {k : Nat}
    {d : DefDecl} (hk : sig.callOf op = some k) (hd : decls[k]? = some d) (env : TyEnv)
    (request : Term) (t : EffTy) :
    HasTy (sig.withDefs decls) env (.perform op request) t ↔
      ∃ requestTy, termTy sig env request = some requestTy ∧
        rowTy d.row.normalizeTypes requestTy (sig.termUse env op) = some t := by
  have hterm : termTy (sig.withDefs decls) env request = termTy sig env request :=
    ((sig.emptyDom_extends_withDefs decls).termTy env request).trans
      (sig.emptyDom_extends.termTy env request).symm
  have huse : (sig.withDefs decls).termUse env op = sig.termUse env op :=
    ((sig.emptyDom_extends_withDefs decls).termUse env op).trans
      (sig.emptyDom_extends.termUse env op).symm
  have hlt : k < decls.length := (List.getElem?_eq_some_iff.mp hd).1
  constructor
  · intro h
    cases h with
    | perform _ hr hrow =>
      rw [hterm] at hr
      rw [sig.withDefs_rowOf_call decls hk hd, huse] at hrow
      exact ⟨_, hr, hrow⟩
  · rintro ⟨requestTy, hr, hrow⟩
    refine .perform ?_ (hterm.trans hr) ?_
    · rw [sig.withDefs_dom_call decls hk]
      exact decide_eq_true hlt
    · rw [sig.withDefs_rowOf_call decls hk hd, huse]
      exact hrow

/-- **The bodies of a block meet their declarations**, at a signature: each declaration is
formed, and each body has, at the environment of its declared request, a type below its
declaration. One rule per arm of `Checker.checkBodies`, at equal lengths. -/
inductive BodiesHasTy (sig : Signature Op) : List DefDecl → Effs Op → Prop
  | nil : BodiesHasTy sig [] .nil
  | cons {d : DefDecl} {ds : List DefDecl} {body : Eff Op} {rest : Effs Op} {t : EffTy} :
      d.formed = true → HasTy sig [d.request.normalize] body t → d.admits t = true →
      BodiesHasTy sig ds rest → BodiesHasTy sig (d :: ds) (.cons body rest)

/-- **The module judgment** (decisions row 328): a module with a block has the type of its main
program at the block's signature, when its bodies meet their declarations there; a program with
no block has its type. `HasTy` derives no type for a block, so the two rules do not overlap. -/
inductive ModuleHasTy (sig : Signature Op) : Eff Op → EffTy → Prop
  | defs {decls : List DefDecl} {bodies : Effs Op} {main : Eff Op} {t : EffTy} :
      BodiesHasTy (sig.withDefs decls) decls bodies → HasTy (sig.withDefs decls) [] main t →
      ModuleHasTy sig (.defs decls bodies main) t
  | plain {e : Eff Op} {t : EffTy} : HasTy sig [] e t → ModuleHasTy sig e t

/-- **The body of a declaration**: where the bodies' judgment holds, each declaration of the block
has its body, typed in the environment of its declared request at a type the formed declaration
admits. A step of `bodiesTyped_of_typeOf` (`Typed/Denotation.lean`), the premise of M5's
invocation arm. -/
theorem BodiesHasTy.get {sig : Signature Op} :
    ∀ {decls : List DefDecl} {bodies : Effs Op}, BodiesHasTy sig decls bodies →
      ∀ {k : Nat} {d : DefDecl}, decls[k]? = some d →
        ∃ body t, bodies.toList[k]? = some body ∧ HasTy sig [d.request.normalize] body t ∧
          d.formed = true ∧ d.admits t = true
  | _, _, .nil, _, _, h => by
    rw [List.getElem?_nil] at h
    cases h
  | _, _, .cons (body := body) (t := t) hf hb ht _, 0, _, h => by
    rw [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨body, t, rfl, hb, hf, ht⟩
  | _, _, .cons _ _ _ hrest, _ + 1, _, h => by
    rw [List.getElem?_cons_succ] at h
    exact hrest.get h

/-- What the bodies' check accepts at equal lengths, the bodies' judgment derives. A step of
`checkModule_sound`. -/
theorem checkBodies_sound (sig : Signature Op) :
    ∀ (p : List Nat) (decls : List DefDecl) (bodies : Effs Op),
      decls.length = bodies.toList.length →
      Checker.checkBodies sig p decls bodies = .ok () → BodiesHasTy sig decls bodies
  | _, [], .nil, _, _ => .nil
  | _, [], .cons _ _, hlen, _ => absurd hlen (Nat.zero_ne_add_one _)
  | _, _ :: _, .nil, hlen, _ => absurd hlen (Nat.add_one_ne_zero _)
  | p, d :: ds, .cons body rest, hlen, h => by
    have hlen' : ds.length = rest.toList.length := by
      simp only [Effs.toList, List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact hlen
    have ih := checkBodies_sound sig (p ++ [1]) ds rest hlen'
    simp only [Checker.checkBodies] at h
    by_cases hf : d.formed = true
    · rw [if_pos hf] at h
      obtain ⟨t, ht, h⟩ := bind_eq_ok.mp h
      by_cases ha : d.admits t = true
      · rw [if_pos ha] at h
        exact .cons hf (check_sound sig body _ _ t ht) ha (ih h)
      · rw [if_neg ha] at h
        cases h
    · rw [if_neg hf] at h
      cases h

/-- What the bodies' judgment derives, the bodies' check accepts, at every path and at equal
lengths. A step of `checkModule_complete`. -/
theorem checkBodies_complete (sig : Signature Op) :
    ∀ {decls : List DefDecl} {bodies : Effs Op}, BodiesHasTy sig decls bodies →
      decls.length = bodies.toList.length ∧
        ∀ p, Checker.checkBodies sig p decls bodies = .ok ()
  | _, _, .nil => ⟨rfl, fun _ => rfl⟩
  | _, _, .cons (body := body) hf hb ht hrest => by
    obtain ⟨hlen, hcheck⟩ := checkBodies_complete sig hrest
    refine ⟨by simp only [Effs.toList, List.length_cons, hlen], fun p => ?_⟩
    simp only [Checker.checkBodies, hf, check_complete sig body _ _ hb (p ++ [0]), ht,
      hcheck (p ++ [1]), ↓reduceIte, bind, Except.bind]

/-- **G2's soundness, the claim `module-check`**: what the module check accepts, the module
judgment derives. -/
@[semantics "initial-algebras-folds" (requirement := R1)]
theorem checkModule_sound (sig : Signature Op) (e : Eff Op) (t : EffTy)
    (h : Checker.checkModule sig e = .ok t) : ModuleHasTy sig e t := by
  cases e with
  | defs decls bodies main =>
    simp only [Checker.checkModule] at h
    by_cases hlen : decls.length = bodies.toList.length
    · have hb := checkBodies_sound (sig.withDefs decls) [0] decls bodies hlen
      rw [if_pos hlen] at h
      obtain ⟨_, hbody, hm⟩ := bind_eq_ok.mp h
      exact .defs (hb hbody) (check_sound _ main [] [1] t hm)
    · rw [if_neg hlen] at h
      cases h
  | _ => exact .plain (check_sound sig _ [] [] t h)

/-- **G2's completeness, the claim `module-check`**: what the module judgment derives, the module
check accepts. -/
@[semantics "initial-algebras-folds" (requirement := R1)]
theorem checkModule_complete (sig : Signature Op) (e : Eff Op) (t : EffTy)
    (h : ModuleHasTy sig e t) : Checker.checkModule sig e = .ok t := by
  cases h with
  | defs hb hm =>
    obtain ⟨hlen, hcheck⟩ := checkBodies_complete _ hb
    simp only [Checker.checkModule, hlen, hcheck [0], check_complete _ _ _ _ hm [1]]
    rfl
  | plain hd =>
    rw [checkModule_eq_check sig (fun _ _ _ heq => by subst heq; cases hd)]
    exact check_complete sig _ _ _ hd []

/-! ## The whole program's typing

`typeOfProgram` (`Program/Typing.lean`) is the module check after the layer references. So the
laws of the whole program's typing are the module's: its judgment (`ModuleHasTy`), its
monotonicity along an extension, and, on a program with no block, the checker's own answer. -/

/-- **A block extends both signatures alike**: an extension keeps which operations are
invocations (`SigExtends.callOf`), so it extends the block's signature too. A step of
`moduleHasTy_ext`. -/
theorem SigExtends.withDefs {s s' : Signature Op} (h : SigExtends s s') (decls : List DefDecl) :
    SigExtends (s.withDefs decls) (s'.withDefs decls) := by
  refine ⟨h.atomOf, h.constAtom, h.scopeKey, fun op hd => ?_, h.service, h.termOf, h.callOf⟩
  cases hc : s.callOf op with
  | none =>
    have hc' : s'.callOf op = none := by rw [h.callOf]; exact hc
    rw [s.withDefs_dom_of_none decls hc] at hd
    rw [s'.withDefs_dom_of_none decls hc', s'.withDefs_rowOf_of_none decls hc',
      s.withDefs_rowOf_of_none decls hc]
    exact h.row op hd
  | some k =>
    have hc' : s'.callOf op = some k := by rw [h.callOf]; exact hc
    rw [s.withDefs_dom_call decls hc] at hd
    refine ⟨by rw [s'.withDefs_dom_call decls hc']; exact hd, ?_⟩
    have hlt : k < decls.length := of_decide_eq_true hd
    obtain ⟨d, hdk⟩ : ∃ d, decls[k]? = some d := ⟨decls[k], List.getElem?_eq_getElem hlt⟩
    rw [s'.withDefs_rowOf_call decls hc' hdk, s.withDefs_rowOf_call decls hc hdk]

/-- The bodies' judgment along an extension. A step of `moduleHasTy_ext`. -/
theorem bodiesHasTy_ext {s s' : Signature Op} (h : SigExtends s s') :
    ∀ {decls : List DefDecl} {bodies : Effs Op}, BodiesHasTy s decls bodies →
      BodiesHasTy s' decls bodies
  | _, _, .nil => .nil
  | _, _, .cons hf hb ht hrest => .cons hf (hasTy_ext h hb) ht (bodiesHasTy_ext h hrest)

/-- **The module judgment along an extension** (C3's monotone half for a module): a module the
judgment types under `s` it types under every extension `s'`, at the same type. -/
@[semantics "initial-algebras-folds" (requirement := R2)]
theorem moduleHasTy_ext {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op} {t : EffTy}
    (he : ModuleHasTy s e t) : ModuleHasTy s' e t := by
  cases he with
  | defs hb hm => exact .defs (bodiesHasTy_ext (h.withDefs _) hb) (hasTy_ext (h.withDefs _) hm)
  | plain hd => exact .plain (hasTy_ext h hd)

/-- **The whole program's typing along an extension**: a program `typeOfProgram` admits under
`s` it admits under every extension `s'`, at the same type. -/
@[semantics "initial-algebras-folds" (requirement := R2)]
theorem typeOfProgram_ext {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op} {t : EffTy}
    (he : typeOfProgram s e = some t) : typeOfProgram s' e = some t := by
  unfold typeOfProgram at he ⊢
  split at he
  · rw [if_pos ‹_›]
    exact toOption_eq_some.mpr (checkModule_complete s' _ t
      (moduleHasTy_ext h (checkModule_sound s _ t (toOption_eq_some.mp he))))
  · cases he

/-- **On a program whose expansion has no block, the whole program's typing is the checker's
answer** at the empty environment. -/
theorem typeOfProgram_eq_typeOf (sig : Signature Op) {e : Eff Op}
    (h : ∀ decls bodies main, e.expandRefs ≠ .defs decls bodies main) :
    typeOfProgram sig e = if e.layerRefsWF then typeOf sig e.expandRefs else none := by
  unfold typeOfProgram
  rw [checkModule_eq_check sig h]
  rfl

end Effect4.Program
