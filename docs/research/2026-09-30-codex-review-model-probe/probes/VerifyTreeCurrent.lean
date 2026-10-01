import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Typed.ForkSource
import Effect4.Laws.Program.Admits
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Program.Authoring.Services
import Effect4.Api.Author
import Effect4.Laws.Program.RuntimeR

/-!
# Verifier for seat TREE: checks of TREE-02, TREE-03, TREE-07, TREE-08, TREE-16, and what the
seat missed

Research probe (docs/research/2026-09-30-model-probe/tree/verify.md). Nothing here is imported by
the tree. Every red control is kept.

* §A TREE-08, strengthened from a row-level test to a kernel theorem: along an appended row table
  (the direction `rows_append` proves typing monotone), the typed state's program judgment is
  NOT monotone. `hostCall` is typed under the empty table and refused under `[] ++ [rowB]`.
* §B Missed: the seat's freshness premise admits the machine's reserved names. A declaration at
  `CurrentMemoMap`'s key (name 3) is "fresh" (the built-in table types it `none`), the program
  that reads it types at `nat`, and the machine answers a memo-map handle (tested).
* §C TREE-03: `fork_source_extension` holds over every signature with the tree's own proof, so
  un-pinning it is a statement change only (proved).
* §D TREE-02: item E's `FlatFits`, read through an open table, refuses every context that holds a
  service at a non-flat carrier; an honest program provides one (proved and tested).
* §E Missed: `nativeServiceTyWith` types two keys of one service code at two carriers, which the
  key module's frame (a carrier is selected by the code) excludes (tested).
* §F TREE-16: the raw runner `Api.run` runs the seventh carrier; the refusing stages are the
  checked ones (tested).
-/

set_option autoImplicit false

namespace Effect4.Program.Typed.VerifyTree

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Program.Denote

/-! ## §A The typed state's program judgment is not monotone in the row table -/

/-- A host row answering a string (`R2Probe.rowB`). -/
def rowB : Effect4.Program.Row :=
  { name := "b", spelling := "B.b", shape := .value, kind := .async, request := .unit,
    answer := .string, cite := "probe", registration := .external }

/-- A reference program parked on host row 0, whose continuation hands the exit back. -/
def hostCall : RProgram :=
  .vis (.inr (.async (.external (.external 0) Val.unit) Val.unit)) (fun ex => .pure ex)

/-- The same program, with the empty row table and with one row appended. -/
def srcShort (p : NativeEff) : ProgramSource := { program := p, table := [] }
def srcLong (p : NativeEff) : ProgramSource := { program := p, table := [] ++ [rowB] }

/-- Under the short table, index 0 reads the placeholder row, whose columns are `never`: the
host-row entry of `Ψ_F` holds at every certificate (`Residual.lean:110-112`). -/
theorem asyncPre_short_every_cert (p : NativeEff) (w : World) (req : Val) (cert : EffTy) :
    asyncPre (srcShort p) w (.external (.external 0) req) cert :=
  ⟨Ty.OrderProof.sub_never _, Ty.OrderProof.sub_never _⟩

/-- Under the longer table the same index names `rowB`, and the entry refuses a `nat` certificate. -/
theorem asyncPre_long_refuses_nat (p : NativeEff) (w : World) (req : Val) :
    ¬ asyncPre (srcLong p) w (.external (.external 0) req) (EffTy.pure .nat) := by
  intro h
  have h1 : Ty.sub .string .nat = true := h.1
  have h2 : Ty.sub .string .nat = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-- Adapted after E: direct membership plus the production subtyping law. -/
theorem strongExit_str_of_sub (w : World) (cert : EffTy) (s : String)
    (hsub : Ty.sub .string cert.answer = true) : FitsExit w cert (.success (Val.str s)) :=
  fits_sub w hsub (Val.str s) True.intro

/-- **Typed under the short table** (every certificate is admitted at index 0). -/
theorem hostCall_typed_short (p : NativeEff) (w : World) :
    TypedProg (srcShort p) w (EffTy.pure .nat) hostCall :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat : EffTy)
    (asyncPre_short_every_cert p w Val.unit (EffTy.pure .nat))
    (fun _ _ _ hpost => TypedProg.pure hpost)

/-- **Refused under the appended table**: whatever certificate a derivation picks is above
`string`, so the continuation must accept a string exit at `nat`. -/
theorem hostCall_untyped_long (p : NativeEff) (w : World) :
    ¬ TypedProg (srcLong p) w (EffTy.pure .nat) hostCall := by
  intro h
  cases h with
  | fiber _ _ _ _ cert pre next =>
    have hsub : Ty.sub .string cert.answer = true := pre.1
    have hk : TypedProg (srcLong p) w (EffTy.pure .nat) (.pure (.success (Val.str "x"))) :=
      next w (leHost_refl w) (.success (Val.str "x")) (strongExit_str_of_sub w cert "x" hsub)
    cases hk with
    | pure hex =>
      exact hex

/-- TREE-08 as one statement: the program judgment is not monotone along `t ↦ t ++ t'`. -/
theorem typedProg_not_table_monotone :
    ¬ ∀ (p : NativeEff) (w : World) (ty : EffTy) (prog : RProgram),
        TypedProg { program := p, table := [] } w ty prog →
        TypedProg { program := p, table := [] ++ [rowB] } w ty prog := by
  intro hmono
  obtain ⟨w⟩ : Nonempty World :=
    ⟨{ ids := [], state := Stores.empty, Γ := fun _ => none, «Π» := fun _ => none,
       Ρ := fun _ => none, Θ := fun _ _ => none }⟩
  exact hostCall_untyped_long (.succeed (.lit .unit)) w
    (hmono (.succeed (.lit .unit)) w _ hostCall (hostCall_typed_short (.succeed (.lit .unit)) w))

/-! ## §B Missed: a "fresh" declaration at a reserved name is unsound -/

/-- `Layer.CurrentMemoMap`'s key (`Machine/ContextMap.lean:670`), a reserved name (`< 4`). -/
def memoKey : ServiceKey := ⟨⟨3⟩, ⟨3⟩⟩

theorem memoKey_eq : memoKey = Env.currentMemoMapKey := rfl

/-- The built-in table types no reserved name except `Scope` (`Native.lean:288-293`). -/
theorem memoKey_untyped : nativeServiceTy memoKey = none := by decide +kernel

/-- So the freshness premise of the seat's `services_append` / `native_into_with`
(`R2Probe.lean:289-298`) holds for a declaration of `CurrentMemoMap` at `nat`. -/
theorem memo_entry_fresh :
    ∀ entry ∈ [(memoKey, Ty.nat)], nativeServiceTyWith [] entry.1 = none := by
  intro entry hmem
  rw [List.mem_singleton] at hmem
  rw [hmem]
  exact memoKey_untyped

/-- `Effect.provide(Effect.service(CurrentMemoMap), Layer.succeed(K4, 1))`. -/
def freeKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def memoRead : NativeEff := .provideLayer (.succeed freeKey (.nat 1)) false (.service memoKey)

-- tested: refused today (the built-in table does not type the reserved name)
#guard (Api.typeOf memoRead []).isNone
-- tested: under the "fresh" declaration it types, answering `nat`
#guard ((typeOfProgram (nativeSignatureWith [] [(memoKey, .nat)]) memoRead).map
  (fun t => (t.answer, t.error))) = some (Ty.nat, Ty.never)
-- tested: the typing certificate the seat's `admitProgramB` would take exists
#guard (checkTypedProgram (nativeSignatureWith [] [(memoKey, .nat)]) memoRead).isSome
-- tested: the machine finishes with the memo map's handle (kind 5), which is not a number
#guard (match (Api.run memoRead 500).exit with
  | some (.success v) => v == Val.handle 5 1 && !(Val.hasTy v .nat [])
  | _ => false)

/-- The reference machine, the one M6's `RReachable` runs (`Assembly.lean:75-76`). -/
def machineOfR : RReplay → RState
  | .finished m | .frontier _ m | .stuck _ m => m

-- tested: on the reference machine the root fiber also finishes with a memo-map handle (kind 5)
#guard (match ((machineOfR (replayR memoRead 500 [Api.evaluate, Api.flush])).fiber?
    Api.root).bind RunFiber.exit with
  | some (.success (.handle k _)) => k == 5
  | _ => false)

/-! ## §C TREE-03: `fork_source_extension` over every signature, with the tree's own proof -/

theorem fork_source_extension_sig (sig : Signature NativeOp) (root : NativeEff) (site : Point)
    (body : NativeEff) (env : TyEnv) (ty : EffTy) (w : World) (m : RState) (parent : RFiber)
    (options : Supervision.ForkOptions)
    (bodyAt : Node.at_ (.eff root) (site.child 0).path = some (.eff body))
    (bodyTy : Checker.check sig env (site.child 0).path body = .ok ty)
    (hstate : w.state = m.state)
    (hids : w.ids = m.fibers.map (fun f => f.id))
    (fresh : w.Γ ⟨m.nextId⟩ = none) :
    (let spawned := spawn (interpR root) m parent (denoteAt root (site.child 0))
        options site.path
     let newer := w.addFiber spawned.2.2 ty
     w.le newer ∧
     newer.state = spawned.1.state ∧
     newer.ids = spawned.1.fibers.map (fun f => f.id) ∧
     newer.Γ spawned.2.2 = some ty ∧
     ∃ child, child ∈ spawned.1.fibers ∧ child.id = spawned.2.2 ∧
       child.origin = .forked parent.id options.daemon site.path ∧
       child.frame.current = denoteAt root (site.child 0) ∧
       Node.at_ (.eff root) (site.child 0).path = some (.eff body) ∧
       Checker.check sig env (site.child 0).path body = .ok ty) := by
  intro spawned newer
  refine ⟨(fork_extension w spawned.2.2 ty fresh).1, ?_, ?_, insert_here _ _ _, ?_⟩
  · show w.state = spawned.1.state
    rw [hstate]
    rfl
  · show w.ids ++ [spawned.2.2] = spawned.1.fibers.map (fun f => f.id)
    rw [hids]
    change m.fibers.map (fun f : RFiber => f.id) ++ [spawned.2.2] =
      (m.fibers ++ [_]).map (fun f : RFiber => f.id)
    rw [List.map_append]
    rfl
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, bodyAt, bodyTy⟩

/-! ## §D TREE-02: item E's `FlatFits` against an open service table

Copied from `docs/research/2026-09-30-pass/membership/Fits.lean:35-91` (the draft item E lands);
`ServicesFitWith` reads a supplied table where the draft reads `nativeServiceTy`. -/

abbrev Inv := Ty → Ty → Prop

def RefDeclared (w : World) (inv : Inv) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ inv t' t

def PromiseDeclared (w : World) (inv : Inv) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ inv a' a ∧ inv e' e

def HandleFits (w : World) (inv : Inv) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = NativeOp.refTarget ∧ RefDeclared w inv ⟨index⟩ .nat
  | some .promise => target = NativeOp.deferredTarget ∧ PromiseDeclared w inv ⟨index⟩ .nat .nat
  | some .scope => target = Ty.scopeTarget
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

def FlatFits (w : World) (inv : Inv) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target =>
    match v with | .handle kind index => HandleFits w inv kind index target | _ => False
  | _ => False

def ServicesFitWith (sty : ServiceKey → Option Ty) (w : World) (inv : Inv)
    (services : Env.Ctx) : Prop :=
  ∀ key sv t, services.getV key = some sv → sty key = some t → FlatFits w inv sv t

def optKey : ServiceKey := ⟨⟨13⟩, ⟨13⟩⟩

theorem optKey_declared :
    nativeServiceTyWith [(optKey, .option .nat)] optKey = some (.option .nat) := by
  decide +kernel

/-- Every context that holds a value at the option-typed key fails the clause, at every world. -/
theorem servicesFit_refuses_option (w : World) (inv : Inv) (services : Env.Ctx) (sv : Val)
    (h : services.getV optKey = some sv) :
    ¬ ServicesFitWith (nativeServiceTyWith [(optKey, .option .nat)]) w inv services :=
  fun hfit => hfit optKey sv (.option .nat) h optKey_declared

/-- `Effect.provideService(Effect.service(K), K, Option.some(1))`: an honest program. -/
def optProgram : NativeEff :=
  .provideService optKey (.app "some" (.cons (.lit (.nat 1)) .nil)) (.service optKey)

-- tested: it types, closed, at `option nat` under the declared table, and runs to `some 1`
#guard ((typeOfProgram (nativeSignatureWith [] [(optKey, .option .nat)]) optProgram).map
  (fun t => (t.answer, t.error, t.requires == Env.Requirement.empty))) =
  some (Ty.option .nat, Ty.never, true)
#guard (match (Api.run optProgram 100).exit with
  | some (.success v) => v == Effect4.Store.Val.some (Effect4.Store.Val.nat 1)
  | _ => false)

/-! ## §E Missed: per-key carriers against the key module's per-code frame -/

def keyA : ServiceKey := ⟨⟨20⟩, ⟨12⟩⟩
def keyB : ServiceKey := ⟨⟨21⟩, ⟨12⟩⟩

/-- One service code, two carriers: `nativeServiceTyWith` keys its entries by the whole key,
where `ServiceKey.Carrier` selects a key's carrier by its code (`Machine/Key.lean:343-349`). -/
theorem one_code_two_carriers :
    keyA.service = keyB.service ∧
      nativeServiceTyWith [(keyA, .string), (keyB, .nat)] keyA = some .string ∧
      nativeServiceTyWith [(keyA, .string), (keyB, .nat)] keyB = some .nat := by
  decide +kernel

/-- The built-in table is per code for free names: two names, one code, one carrier. -/
theorem builtin_per_code : nativeServiceTy ⟨⟨20⟩, ⟨4⟩⟩ = nativeServiceTy ⟨⟨21⟩, ⟨4⟩⟩ := by
  decide +kernel

/-! ## §F TREE-16: the raw runner is not a refusing stage -/

def greetKey : ServiceKey := ⟨⟨12⟩, ⟨12⟩⟩
def greetProgram : NativeEff :=
  .provideService greetKey (.lit (.str "hello")) (.service greetKey)

-- tested: refused by the checked stages (as the seat's R1Probe shows) …
#guard (Api.typeOf greetProgram []).isNone
-- … and run by `Api.run`, which is raw by design (`Api.lean:311-318`)
#guard (match (Api.run greetProgram 100).exit with
  | some (.success v) => v == Val.str "hello"
  | _ => false)

end Effect4.Program.Typed.VerifyTree

#print axioms Effect4.Program.Typed.VerifyTree.asyncPre_short_every_cert
#print axioms Effect4.Program.Typed.VerifyTree.asyncPre_long_refuses_nat
#print axioms Effect4.Program.Typed.VerifyTree.strongExit_str_of_sub
#print axioms Effect4.Program.Typed.VerifyTree.hostCall_typed_short
#print axioms Effect4.Program.Typed.VerifyTree.hostCall_untyped_long
#print axioms Effect4.Program.Typed.VerifyTree.typedProg_not_table_monotone
#print axioms Effect4.Program.Typed.VerifyTree.memoKey_eq
#print axioms Effect4.Program.Typed.VerifyTree.memoKey_untyped
#print axioms Effect4.Program.Typed.VerifyTree.memo_entry_fresh
#print axioms Effect4.Program.Typed.VerifyTree.fork_source_extension_sig
#print axioms Effect4.Program.Typed.VerifyTree.optKey_declared
#print axioms Effect4.Program.Typed.VerifyTree.servicesFit_refuses_option
#print axioms Effect4.Program.Typed.VerifyTree.one_code_two_carriers
#print axioms Effect4.Program.Typed.VerifyTree.builtin_per_code
