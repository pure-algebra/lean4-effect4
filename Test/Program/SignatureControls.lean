import Effect4.Laws.Program.Signature
import Effect4.Program.Authoring.Services

/-!
# Σ_app (decisions rows 111–116): the extension's red and positive controls

`Laws/Program/Signature.lean` states the signature an application's tables give the checker and
extension along it. These are the fixtures the rows rule on (the model probe's TREE and pedigree
seats and Codex's audit proved them as probes; kept here as controls):

* `prepend_not_extends` (red, proved): a row prepended to the table is not an extension; the same
  program, unchanged, answers another row's type. Appending is (`rows_append`, tested).
* `shadow_not_extends` (red, proved): a declaration at a code the built-in table already types
  re-types every key of that code, so it is not an extension; the freshness premise of
  `SigApp.services_append` refuses it (`shadow_not_fresh`).
* `one_code_two_carriers` (red, proved): the per-key table `nativeServiceTyWith` types two keys of
  one service code at two carriers, which `Machine/Key.lean`'s `carrier_def` frame excludes.
  Under the per-code table (row 113) the two keys have one carrier (`per_code_one_carrier`).
-/

set_option autoImplicit false

namespace Test.Program.SignatureControls

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

/-! ## Rows: append extends, prepend does not -/

/-- Two host rows that differ in their answer and in their printed shape. -/
def rowA : Row :=
  { name := "a", spelling := "A.a", kind := .async, request := .unit, answer := .nat,
    cite := "probe", registration := .external }
def rowB : Row := { rowA with name := "b", spelling := "B.b", shape := .value, answer := .string }

/-- `yield* A.a()`: the host row at index 0. -/
def callA : NativeEff := .perform (.external 0) (.lit .unit)

-- tested: under `[rowA]` the call answers a number; prepend `rowB` and the same program,
-- unchanged, answers a string; append and it still answers a number
#guard effTy (nativeSignature [rowA]) [] callA = some ⟨.nat, .never, Requirement.empty⟩
#guard effTy (nativeSignature ([rowB] ++ [rowA])) [] callA = some ⟨.string, .never, Requirement.empty⟩
#guard effTy (nativeSignature ([rowA] ++ [rowB])) [] callA = some ⟨.nat, .never, Requirement.empty⟩

/-- **Red control (proved).** Prepending is not an extension: index 0 is admitted by both tables
at different rows. -/
theorem prepend_not_extends :
    ¬ SigExtends (nativeSignature [rowA]) (nativeSignature ([rowB] ++ [rowA])) := by
  intro h
  have hrow := (h.row (.external 0) rfl).2
  have hshape := congrArg Row.shape hrow
  exact absurd hshape (by decide)

/-- **Positive control (proved).** Appending is, and the call keeps its type. -/
theorem append_keeps_call :
    effTy (nativeSignature ([rowA] ++ [rowB])) [] callA = some ⟨.nat, .never, Requirement.empty⟩ :=
  effTy_ext (rows_append [rowA] [rowB]) (by decide +kernel)

/-! ## Services: per code, fresh codes only -/

/-- A key with type code 4 (a number) under a free name (`firstFreeName` is 4). -/
def natKey : ServiceKey := ⟨⟨100⟩, ⟨4⟩⟩

theorem natKey_ty : (SigApp.mk [] []).serviceTy natKey = some .nat := by decide +kernel

theorem natKey_bool : (SigApp.mk [] [(natKey, .bool)]).serviceTy natKey = some .bool := by
  decide +kernel

/-- **Red control (proved).** A declaration that re-types a code the built-in table types is not
an extension. -/
theorem shadow_not_extends :
    ¬ SigExtends (SigApp.mk [] []).signature (SigApp.mk [] [(natKey, .bool)]).signature := by
  intro h
  have hk := h.service natKey .nat natKey_ty
  change (SigApp.mk [] [(natKey, .bool)]).serviceTy natKey = some .nat at hk
  rw [natKey_bool] at hk
  cases hk

/-- And the freshness premise of `SigApp.services_append` refuses it. -/
theorem shadow_not_fresh : ¬ SigApp.FreshCode (SigApp.mk [] []) (natKey, .bool) := by
  intro h
  have hb : SigApp.builtinCodeTy natKey.service = some .nat := by decide +kernel
  rw [h.2] at hb
  cases hb

/-- A fresh code (12, a string service of the application's own). -/
def greetKey : ServiceKey := ⟨⟨12⟩, ⟨12⟩⟩

theorem greet_fresh : SigApp.FreshCode (SigApp.mk [] []) (greetKey, .string) :=
  ⟨rfl, by decide +kernel⟩

/-- **Positive control (proved).** A declaration at a fresh code extends the signature, and the
application's key is typed at its declared carrier. -/
theorem greet_extends :
    SigExtends (SigApp.mk [] []).signature (SigApp.mk [] [(greetKey, .string)]).signature :=
  SigApp.services_append (SigApp.mk [] []) [(greetKey, .string)] (fun entry hmem => by
    rw [List.mem_singleton] at hmem
    rw [hmem]
    exact greet_fresh)

-- tested: the declared key reads its carrier; a built-in code keeps its own
#guard (SigApp.mk [] [(greetKey, .string)]).serviceTy greetKey = some .string
#guard (SigApp.mk [] [(greetKey, .string)]).serviceTy natKey = some .nat

def keyA : ServiceKey := ⟨⟨20⟩, ⟨12⟩⟩
def keyB : ServiceKey := ⟨⟨21⟩, ⟨12⟩⟩

/-- **Red control (proved).** The per-key table types one code at two carriers. -/
theorem one_code_two_carriers :
    keyA.service = keyB.service ∧
      nativeServiceTyWith [(keyA, .string), (keyB, .nat)] keyA = some .string ∧
      nativeServiceTyWith [(keyA, .string), (keyB, .nat)] keyB = some .nat := by
  decide +kernel

/-- **Positive control (proved).** The per-code table gives the two keys one carrier. -/
theorem per_code_one_carrier :
    (SigApp.mk [] [(keyA, .string), (keyB, .nat)]).serviceTy keyA =
      (SigApp.mk [] [(keyA, .string), (keyB, .nat)]).serviceTy keyB :=
  SigApp.serviceTy_code _ rfl (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-! ## C3's reflection: refusals included, on Σ-programs only -/

/-- `yield* A.a(1)`: row 0's request is `unit`, so the checker refuses it. -/
def badCall : NativeEff := .perform (.external 0) (.lit (.nat 1))

theorem badCall_sigProgram : SigProgram (nativeSignature [rowA]) badCall := rfl

/-- **Positive control (proved).** The refusal is the same under the appended table: C3's
reflection, refusals included. -/
theorem badCall_same_refusal :
    Checker.check (nativeSignature ([rowA] ++ [rowB])) [] [] badCall =
      Checker.check (nativeSignature [rowA]) [] [] badCall :=
  check_restrict (rows_append [rowA] [rowB]) badCall_sigProgram [] []

-- tested: and it is a refusal
#guard (Checker.check (nativeSignature [rowA]) [] [] badCall).toOption.isNone

/-- `yield* B.b()` at index 1: outside the shorter table's domain. -/
def callB : NativeEff := .perform (.external 1) (.lit .unit)

theorem callB_refused_short : (Checker.check (nativeSignature [rowA]) [] [] callB).toOption = none := by
  decide +kernel

theorem callB_typed_long :
    (Checker.check (nativeSignature ([rowA] ++ [rowB])) [] [] callB).toOption =
      some ⟨.string, .never, Requirement.empty⟩ := by
  decide +kernel

/-- **Red control (proved).** Without the Σ-program premise the checker's answer changes under
an extension: an operation outside the shorter domain is refused there and typed in the longer. -/
theorem reflection_needs_sigProgram :
    ¬ ∀ e : NativeEff, Checker.check (nativeSignature ([rowA] ++ [rowB])) [] [] e =
        Checker.check (nativeSignature [rowA]) [] [] e := by
  intro h
  have hl := callB_typed_long
  rw [h callB, callB_refused_short] at hl
  cases hl

#print axioms prepend_not_extends
#print axioms append_keeps_call
#print axioms natKey_ty
#print axioms natKey_bool
#print axioms shadow_not_extends
#print axioms shadow_not_fresh
#print axioms greet_fresh
#print axioms greet_extends
#print axioms one_code_two_carriers
#print axioms per_code_one_carrier
#print axioms badCall_sigProgram
#print axioms badCall_same_refusal
#print axioms callB_refused_short
#print axioms callB_typed_long
#print axioms reflection_needs_sigProgram

/-! The step's own theorems: shape A (`World.lean`, `Membership.lean`) and the signature. -/
#print axioms Effect4.Program.Typed.order_refl
#print axioms Effect4.Program.Typed.order_trans
#print axioms Effect4.Program.Typed.le_serviceTy
#print axioms Effect4.Program.Typed.park_extension
#print axioms Effect4.Program.Typed.fork_extension
#print axioms Effect4.Program.Typed.refMake_extension
#print axioms Effect4.Program.Typed.promise_extension
#print axioms Effect4.Program.Typed.serviceTy_of_le
#print axioms Effect4.Program.Typed.servicesFit_map
#print axioms Effect4.Program.Typed.fits_map
#print axioms Effect4.Program.Typed.fits_mono
#print axioms Effect4.Program.argTy_congr
#print axioms Effect4.Program.argsTy_congr
#print axioms Effect4.Program.termTy_congr
#print axioms Effect4.Program.causeTy_congr
#print axioms Effect4.Program.SigExtends.refl
#print axioms Effect4.Program.SigExtends.trans
#print axioms Effect4.Program.SigExtends.termTy
#print axioms Effect4.Program.SigExtends.causeTy
#print axioms Effect4.Program.SigExtends.bodyRequires
#print axioms Effect4.Program.hasTy_ext
#print axioms Effect4.Program.stmtsHasTy_ext
#print axioms Effect4.Program.effsHasTy_ext
#print axioms Effect4.Program.actionHasTy_ext
#print axioms Effect4.Program.layerHasTy_ext
#print axioms Effect4.Program.layersHasTy_ext
#print axioms Effect4.Program.check_ext
#print axioms Effect4.Program.effTy_ext
#print axioms Effect4.Program.typeOfProgram_ext
#print axioms Effect4.Program.checkLayer_ext
#print axioms Effect4.Program.rows_append
#print axioms Effect4.Program.SigApp.serviceTy_nil
#print axioms Effect4.Program.SigApp.signature_nil
#print axioms Effect4.Program.SigApp.serviceTy_code
#print axioms Effect4.Program.SigApp.rows_append
#print axioms Effect4.Program.SigApp.services_append
#print axioms Effect4.Program.Typed.servicesFit_restrict
#print axioms Effect4.Program.Typed.fits_restrict
#print axioms Effect4.Program.cata_eff_congr_on
#print axioms Effect4.Program.cata_stmt_congr_on
#print axioms Effect4.Program.cata_stmts_congr_on
#print axioms Effect4.Program.cata_effs_congr_on
#print axioms Effect4.Program.cata_action_congr_on
#print axioms Effect4.Program.cata_layer_congr_on
#print axioms Effect4.Program.cata_layers_congr_on
#print axioms Effect4.Program.term?_ext
#print axioms Effect4.Program.check_alg_agreeOn
#print axioms Effect4.Program.check_restrict
#print axioms Effect4.Program.effTy_restrict

end Test.Program.SignatureControls
