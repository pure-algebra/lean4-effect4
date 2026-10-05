import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Typed.Admission
import Effect4.Program.Authoring.Services

/-!
# Σ_app (decisions rows 111–116): the extension's red and positive controls

`Program/SigApp.lean` defines the signature an application's tables give the checker, and
`Laws/Program/Signature.lean` states extension along it. These are the fixtures the rows rule on
(the model probe's TREE and pedigree seats and Codex's audit proved them as probes; kept here as
controls):

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

/-! ## Lawful signatures: each clause refuses with its own located reason -/

-- tested: the empty signature and one lawful row are admitted
#guard admitSig (SigApp.mk [] []) = .ok ()
#guard admitSig (SigApp.mk [rowA] []) = .ok ()
#guard admitSig (SigApp.mk [] [(greetKey, .string)]) = .ok ()

/-- A declaration at the memo map's reserved name (row 114). -/
def memoKey : ServiceKey := ⟨⟨3⟩, ⟨3⟩⟩

/-- A row whose request is the empty product DI-67 admitted (row 127). -/
def emptyRequestRow : Row := { rowA with request := .prod .never .nat }

/-- A row that answers a cell handle (row 97). -/
def cellRow : Row := { rowA with answer := .refOf .nat }

-- tested: each clause refuses, located
#guard admitSig (SigApp.mk [] [(memoKey, .nat)]) = .error (.service 0 .reservedName)
#guard admitSig (SigApp.mk [] [(greetKey, .option .nat)]) = .error (.service 0 .nonFlatCarrier)
#guard admitSig (SigApp.mk [] [(natKey, .bool)]) = .error (.service 0 .conflictsBuiltin)
#guard admitSig (SigApp.mk [] [(keyA, .string), (keyB, .string)]) = .error (.duplicateCode ⟨12⟩)
#guard admitSig (SigApp.mk [emptyRequestRow] []) = .error (.row 0 (.emptyColumn "request"))
#guard admitSig (SigApp.mk [cellRow] []) = .error (.row 0 (.internalHandle "answer"))
#guard admitSig (SigApp.mk [rowA, rowA] []) = .error (.duplicateRow ("A.a", []))

/-- **Red control (proved).** One code declared twice is not lawful (row 113), whatever the
carriers. -/
theorem one_code_twice_not_lawful : ¬ LawfulSig (SigApp.mk [] [(keyA, .string), (keyB, .string)]) := by
  decide +kernel

/-- **Red control (proved, row 127).** A host row whose request is `prod never nat` is not
lawful: `E4-TYPED-CE-015` at a table column. -/
theorem empty_request_not_lawful : ¬ LawfulSig (SigApp.mk [emptyRequestRow] []) := by
  decide +kernel

/-- A lawful signature is what `admitSig` admits (both directions, `admitSig_ok_iff`). -/
theorem rowA_lawful : LawfulSig (SigApp.mk [rowA] []) := (admitSig_ok_iff _).mp (by decide +kernel)

/-! The step's own theorems: shape A (`World.lean`, `Membership.lean`) and the signature. -/

/-! Decisions row 155 (a): a supplied row's template columns read a parameter as inhabited
(`admitRowColumn`), so a well-scoped template row is admitted; a program's own column reads it as
uninhabited (`admitColumn`: no value fits a parameter). -/

/-- A host row from `List<A>` to `Option<A>`. -/
def templateRow : Row := { rowA with request := .list (.var 0), answer := .option (.var 0) }

#guard admitSig (SigApp.mk [templateRow] []) = .ok ()
#guard admitRowColumn (.var 0) = true
-- red: the program's column check refuses a bare parameter
#guard admitColumn (.var 0) = false

end Test.Program.SignatureControls
