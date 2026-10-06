import Effect4.Laws.Codegen.PrintReadable
import Effect4.Laws.Program.Typed.Mask
import Effect4.Laws.Program.Typing.Sound

/-!
# Laws.Codegen.Mask — the mask's two rows and its printed form

Decisions rows 245 and 246; the mask's second note
(`docs/research/2026-10-05-claude-lead/mask-second-note.md`, F5 and F6). Two registry claims
(`tools/Tools/SemanticsRegistry.lean`) have their statements here.

* **`mask-rows-table-premises`** (concept `exact-codecs`, requirement R8) is
  `mask_rows_table_premises`, a `MaskRowsPremises`: the two rows are rows of the table, with
  two reserved heads; the table's nine decided premises hold at the extended table; a restore
  site is readable exactly when its saved term is a readable leaf and its body is readable,
  and the getter is readable at every depth; `read_print` and `read_exact` keep their
  statements.
* **`mask-printed-form-profile`** (concept `translation-simulation`, requirements R10 and
  R11) is `mask_printed_form_profile`, a `MaskFormProfile`: the mask as a derived form types
  as its body does, under the saved state's binder; it is readable when its body is, so it
  prints and reads back; and its entry has two checkpoints that the native mask does not
  have, each stated on the frame machine.

Each top node is a decomposition: its proof cites one theorem for each field
(`#plan_status`). No field rests on a planned goal.

Reach. Program syntax at any signature with a lawful spelling; the checker at any signature;
the frame machine at the program's interpreter. What they do not establish: no typing in the
first claim, and no behaviour of a target in either. **No equality with the native spelling**:
the printed form is the program's own expansion, three checkpoints longer than the native
mask, and it is not the native mask at the two checkpoints of its entry. Its agreement with a
named release on a named observation is not stated here: the truth lane's programs are finite
checks (`harness/truth/Truth.lean`, `pMaskWait` and `pMaskedRestore`). The form's contract has
one premise for its clients: nothing is acquired or registered before the body begins.

Consumers. The checked module production and reading (`ModuleEmission`, `admitModule`) read
the first claim through `read_print` and `read_exact`. The Queue's waiting wrapper and the
Semaphore's protected permit read the second.
-/

set_option autoImplicit false

namespace Effect4.Program

open TypeScript (Expr Stmt)
open Effect4.Codegen
open Effect4.Codegen.Template
open Effect4.Codegen.Templates (RowOut ArgPat Fixed table tableLayer printAlg printArg printArgs
  argDepth argSortOf Carrier Out)
open Effect4.Codegen.Classes (Classes)

/-! ## 4. The two rows keep the table's premises (`mask-rows-table-premises`) -/

/-- The getter's row: the mask that answers its own restore. -/
def getterRow : Templates.Row :=
  ⟨.action, "getInterruptible", [],
    .tpl (Templates.call "Effect.uninterruptibleMask"
      [Templates.lam (Templates.call "Effect.succeed" [.binderRef 0])])⟩

/-- A restore site's row: the root export `pipe`, the body and then the saved term. -/
def restoreRow : Templates.Row :=
  ⟨.eff, "restore", [], .tpl (Templates.call "pipe" [.hole 1, .hole 0])⟩

section Readability

variable {Op : Type} {classes : Classes} {sig : Signature Op}

/-- Two predicates that agree on a list find the same element. -/
@[semantics "exact-codecs"]
private theorem find?_agree {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find?_agree l fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- **The printer's row at a constructor that no row classifies** is the first row with the
constructor, whatever the node's arguments: a row that fixes no argument selects by its family
and its constructor alone. -/
@[semantics "exact-codecs"]
theorem find?_selects_unfixed {R : EffFam → Type} (fam : EffFam) (ctor : String)
    (args : List (ArgF Op R))
    (unfixed : table.all (fun row =>
      !(row.fam == fam && row.ctor == ctor) || row.fixed.isEmpty) = true) :
    (table.find? fun row => row.selects fam ctor args) =
      table.find? fun row => row.fam == fam && row.ctor == ctor := by
  refine find?_agree table fun row hrow => ?_
  have here := List.all_eq_true.mp unfixed row hrow
  unfold Templates.Row.selects
  cases hhead : (row.fam == fam && row.ctor == ctor) with
  | false => rfl
  | true =>
    rw [hhead, Bool.not_true, Bool.false_or, List.isEmpty_iff] at here
    rw [here]
    rfl

/-- The printer's row at a restore node is the restore row. -/
@[semantics "exact-codecs"]
theorem find?_restoreRow {R : EffFam → Type} (args : List (ArgF Op R)) :
    (table.find? fun row => row.selects .eff "restore" args) = some restoreRow := by
  rw [find?_selects_unfixed .eff "restore" args (by decide)]
  rfl

/-- **The getter is readable at every depth**: its row is a skeleton with no hole. -/
@[semantics "exact-codecs"]
theorem getInterruptible_readable (n : Nat) :
    Readable classes sig n (.withFiber .getInterruptible) = true := rfl

/-- **A restore site is readable exactly when its saved term is a readable leaf and its body is
readable**, typed or not: the row has no condition of its own. -/
@[semantics "exact-codecs"]
theorem restore_readable (n : Nat) (saved : Term) (body : Eff Op) :
    Readable classes sig n (.restore saved body) =
      (saved.scoped n && saved.covers classes && saved.unannotated &&
        Readable classes sig n body) := by
  show (domLayer.rowDom classes sig .eff "restore"
    [ArgF.term saved, ArgF.child .eff (cata_eff (readableAlg classes sig) body)] n).isSome = _
  unfold domLayer.rowDom
  rw [find?_restoreRow]
  show (if argsReadable classes sig .eff n restoreRow.out (rowDaemon restoreRow)
    [ArgF.term saved, ArgF.child .eff (cata_eff (readableAlg classes sig) body)] 0 = true
    then some 0 else none).isSome = _
  have args : argsReadable classes sig .eff n restoreRow.out (rowDaemon restoreRow)
      [ArgF.term saved, ArgF.child .eff (cata_eff (readableAlg classes sig) body)] 0 =
      (saved.scoped n && saved.covers classes && saved.unannotated &&
        Readable classes sig n body) := by
    simp only [argsReadable, argReadable, leafReadable, Readable, Bool.and_true]
    rfl
  rw [args]
  cases (saved.scoped n && saved.covers classes && saved.unannotated &&
    Readable classes sig n body) <;> rfl

/-- **The mask's derived form is readable exactly when its body is**, one level up, under the
saved state's binder: the `bind`, the getter and the body's mask add no condition. -/
@[semantics "exact-codecs"]
theorem mask_readable (n : Nat) (body : Eff Op) :
    Readable classes sig n (.bind (.withFiber .getInterruptible) (.uninterruptible body)) =
      Readable classes sig (n + 1) body := by
  have inner : cata_eff (readableAlg classes sig) (.uninterruptible body) (n + 1) =
      if (cata_eff (readableAlg classes sig) body (n + 1)).isSome then some 0 else none := by
    show domLayer.rowDom classes sig .eff "uninterruptible"
      [ArgF.child .eff (cata_eff (readableAlg classes sig) body)] (n + 1) = _
    unfold domLayer.rowDom
    rw [find?_selects_unfixed .eff "uninterruptible" _ (by decide)]
    show (if argsReadable classes sig .eff (n + 1) _ _
      [ArgF.child .eff (cata_eff (readableAlg classes sig) body)] 0 = true then some 0
      else none) = _
    simp only [argsReadable, argReadable, Bool.and_true]
    rfl
  show (domLayer.rowDom classes sig .eff "bind"
    [ArgF.child .eff (cata_eff (readableAlg classes sig) (.withFiber .getInterruptible)),
      ArgF.child .eff (cata_eff (readableAlg classes sig) (.uninterruptible body))] n).isSome = _
  unfold domLayer.rowDom
  rw [find?_selects_unfixed .eff "bind" _ (by decide)]
  show (if argsReadable classes sig .eff n _ _
    [ArgF.child .eff (cata_eff (readableAlg classes sig) (.withFiber .getInterruptible)),
      ArgF.child .eff (cata_eff (readableAlg classes sig) (.uninterruptible body))] 0 = true
    then some 0 else none).isSome = _
  have args : argsReadable classes sig .eff n
      (.tpl (Templates.call "Effect.flatMap" [.hole 0, Templates.lam (.hole 1)])) false
      [ArgF.child .eff (cata_eff (readableAlg classes sig) (.withFiber .getInterruptible)),
        ArgF.child .eff (cata_eff (readableAlg classes sig) (.uninterruptible body))] 0 =
      (cata_eff (readableAlg classes sig) body (n + 1)).isSome := by
    simp only [argsReadable, argReadable, Bool.and_true]
    show ((cata_eff (readableAlg classes sig) (.withFiber .getInterruptible) n).isSome &&
      (cata_eff (readableAlg classes sig) (.uninterruptible body) (n + 1)).isSome) = _
    rw [inner]
    cases (cata_eff (readableAlg classes sig) body (n + 1)).isSome <;> rfl
  show (if argsReadable classes sig .eff n
      (.tpl (Templates.call "Effect.flatMap" [.hole 0, Templates.lam (.hole 1)])) false
      [ArgF.child .eff (cata_eff (readableAlg classes sig) (.withFiber .getInterruptible)),
        ArgF.child .eff (cata_eff (readableAlg classes sig) (.uninterruptible body))] 0 = true
    then some 0 else none).isSome = _
  rw [args]
  show _ = (cata_eff (readableAlg classes sig) body (n + 1)).isSome
  cases (cata_eff (readableAlg classes sig) body (n + 1)).isSome <;> rfl

end Readability

/-- The statements of the claim `mask-rows-table-premises` (decisions row 245; the note's
F5). -/
structure MaskRowsPremises : Prop where
  /-- The two rows are the printer's rows at their constructors. -/
  rows : (table.find? fun row => row.fam == EffFam.action && row.ctor == "getInterruptible") =
      some getterRow ∧
    (table.find? fun row => row.fam == EffFam.eff && row.ctor == "restore") = some restoreRow
  /-- Both heads are reserved, so no row of a signature takes either spelling. -/
  heads : "Effect.uninterruptibleMask" ∈ reserved ∧ "pipe" ∈ reserved
  /-- The table's nine decided premises, at the extended table: the reader's four, the round
  trip's four with the separation of the rows by their heads, and the printer's one. -/
  linear : table.all rowLinear = true
  family : table.all rowFamily = true
  fixedNoHole : table.all rowFixedNoHole = true
  holesLt : table.all rowHolesLt = true
  complete : table.all rowComplete = true
  apart : (List.range table.length).all (fun k => (List.range k).all fun j =>
    match table[j]?, table[k]? with
    | some rj, some rk => rj.fam != rk.fam || rowsApart rj rk
    | _, _ => true) = true
  shape : table.all rowShape = true
  actionHeaded : table.all actionRowHeaded = true
  holeKinds : table.all rowHoleKinds = true
  /-- The getter is readable at every depth. A restore site is readable exactly when its saved
  term is a readable leaf and its body is readable: `Readable` is unchanged in meaning, and it
  reads no type. -/
  getterReadable : ∀ (classes : Classes) (sig : Signature NativeOp) (n : Nat),
    Readable classes sig n (.withFiber .getInterruptible) = true
  restoreReadable : ∀ (classes : Classes) (sig : Signature NativeOp) (n : Nat) (saved : Term)
    (body : Eff NativeOp), Readable classes sig n (.restore saved body) =
      (saved.scoped n && saved.covers classes && saved.unannotated &&
        Readable classes sig n body)
  /-- `read_print` and `read_exact` keep their statements, at every signature with a lawful
  spelling and at every program, the two constructors included. -/
  readPrint : ∀ (classes : Classes) (sig : Signature NativeOp)
    (spell : String → List String → Option NativeOp), LawfulSpelling sig spell →
    ∀ (n : Nat) (e : Eff NativeOp) (x : Expr), Readable classes sig n e = true →
      print sig n e = .ok x → readEff classes sig spell n x = .ok e
  readExact : ∀ (classes : Classes) (sig : Signature NativeOp)
    (spell : String → List String → Option NativeOp), LawfulSpelling sig spell →
    ∀ (n : Nat) (x : Expr) (e : Eff NativeOp), readEff classes sig spell n x = .ok e →
      print sig n e = .ok x

/-- **The mask's two rows keep the table's premises** (the claim `mask-rows-table-premises`;
concept `exact-codecs`, requirement R8; decisions row 245).

Reach: program syntax. The table is the one table of `Codegen/Templates.lean`, and each
premise is decided again by the kernel at the extended table. It does not establish typing: a
restore site of an ill-typed saved term reads back as well. It establishes no behaviour of a
target. An annotated position prints and is not read, as before: `Readable` excludes it. Its
consumers are the checked module production and reading, through `read_print` and
`read_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem mask_rows_table_premises : MaskRowsPremises where
  rows := ⟨rfl, rfl⟩
  heads := ⟨by decide, by decide⟩
  linear := table_linear
  family := table_family
  fixedNoHole := table_fixedNoHole
  holesLt := table_holesLt
  complete := table_complete
  apart := table_apart
  shape := table_shape
  actionHeaded := table_actionHeaded
  holeKinds := table_holeKinds
  getterReadable := fun _ _ n => getInterruptible_readable n
  restoreReadable := fun _ _ n saved body => restore_readable n saved body
  readPrint := fun _ _ _ hl _ _ _ hr hp => read_print hl hr hp
  readExact := fun _ _ _ hl _ _ _ h => read_exact hl h

/-! ## 5. The printed form's profile (`mask-printed-form-profile`) -/

open Effect4.Machine in
/-- The mask as a derived form: the getter bound to the body under `uninterruptible`. The
body is one level up, under the saved state's binder. -/
abbrev maskForm {Op : Type} (body : Eff Op) : Eff Op :=
  .bind (.withFiber .getInterruptible) (.uninterruptible body)

section FormTyping

open Conform.Effect4.Typing
open Effect4.Machine.Env (Requirement)

/-- **The derived form types as its body**, under the saved state's binder: the getter answers
the saved state's type with no error and no requirement, and a mask changes no column. -/
@[semantics "translation-simulation"]
theorem maskForm_typed (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp)
    (t : EffTy) (hb : effTy sig (env ++ [Ty.maskRestore]) body = some t) :
    effTy sig env (maskForm body) =
      some ⟨t.answer, Ty.never.join t.error, Requirement.empty.union t.requires⟩ :=
  effTy_complete sig _ env _
    (.bind (.withFiber .getInterruptible) (.uninterruptible (effTy_sound sig body _ t hb)))

/-- **A restore site types as its body**, when its saved term has the saved state's type. -/
@[semantics "translation-simulation"]
theorem restore_typed (sig : Signature NativeOp) (env : TyEnv) (saved : Term)
    (body : Eff NativeOp) (t : EffTy) (hs : termTy sig env saved = some Ty.maskRestore)
    (hb : effTy sig env body = some t) : effTy sig env (.restore saved body) = some t :=
  effTy_complete sig _ env _ (.restore hs (effTy_sound sig body env t hb))

/-- A restore site of any other saved term has no type: the Boolean use that row 239's
selection would admit is refused. -/
@[semantics "translation-simulation"]
theorem restore_untyped (sig : Signature NativeOp) (env : TyEnv) (saved : Term)
    (body : Eff NativeOp) (s : Ty) (hs : termTy sig env saved = some s) (hne : s ≠ Ty.maskRestore) :
    effTy sig env (.restore saved body) = none := by
  cases h : effTy sig env (.restore saved body) with
  | none => rfl
  | some t =>
    have typed := effTy_sound sig _ env t h
    cases typed with
    | restore hsaved _ => exact absurd (Option.some.inj (hs.symm.trans hsaved)) hne

end FormTyping

section Profile

open Effect4.Machine Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Machine.Env (Requirement)

/-- The statements of the claim `mask-printed-form-profile` (decisions rows 245 and 246; the
note's F5 and F6). -/
structure MaskFormProfile : Prop where
  /-- The surface's builder is the form: the program's own expansion, node for node, with no
  constructor of its own. -/
  expansion : ∀ (saved : String) (body : Authoring.Src NativeOp) (env : Authoring.Env)
    (p : List Nat) (b : Eff NativeOp), body (env.push [saved]) (p ++ [1] ++ [0]) = .ok b →
      Authoring.uninterruptibleMask saved body env p = .ok (maskForm b)
  /-- The form types as its body does, under the saved state's binder. -/
  typed : ∀ (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp) (t : EffTy),
    effTy sig (env ++ [Ty.maskRestore]) body = some t →
      effTy sig env (maskForm body) =
        some ⟨t.answer, Ty.never.join t.error, Requirement.empty.union t.requires⟩
  /-- A restore site types as its body when its saved term has the saved state's type, and has
  no type at any other saved term. -/
  siteTyped : ∀ (sig : Signature NativeOp) (env : TyEnv) (saved : Term) (body : Eff NativeOp)
    (t : EffTy), termTy sig env saved = some Ty.maskRestore → effTy sig env body = some t →
      effTy sig env (.restore saved body) = some t
  siteRefused : ∀ (sig : Signature NativeOp) (env : TyEnv) (saved : Term) (body : Eff NativeOp)
    (s : Ty), termTy sig env saved = some s → s ≠ Ty.maskRestore →
      effTy sig env (.restore saved body) = none
  /-- The form is readable exactly when its body is, one level up. So it prints row by row,
  and what it prints reads back to it. -/
  readable : ∀ (classes : Classes) (sig : Signature NativeOp) (n : Nat) (body : Eff NativeOp),
    Readable classes sig n (maskForm body) = Readable classes sig (n + 1) body
  roundTrip : ∀ (sig : Signature NativeOp) (spell : String → List String → Option NativeOp),
    LawfulSpelling sig spell → ∀ (n : Nat) (body : Eff NativeOp),
    Readable (classesOf (maskForm body)) sig n (maskForm body) = true →
      Program.roundTrip sig spell n (maskForm body) = .ok (maskForm body)
  /-- **The first checkpoint of the entry.** Inside the getter the fiber is masked, whatever
  its caller was, and the restoring frame is on the stack of an interruptible caller only. -/
  insideGetter : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool),
    (evaluatePrim.withFiber interp m f y
        WithFiberAction.getInterruptible).fiber.frame.interruptible = false ∧
      (evaluatePrim.withFiber interp m f y WithFiberAction.getInterruptible).fiber.frame.stack =
        if f.frame.interruptible = true then Prim.setInterruptible true :: f.frame.stack
        else f.frame.stack
  /-- An interrupt requested there stays pending, and the getter's restoring frame then fails
  the fiber with it: the form ends before its body starts. -/
  getterPending : ∀ (cause : CauseV) (fr : FFiber), fr.interruptedCause = some cause →
    ((Prim.setInterruptible true : NCode).ensure fr).snd = some (Prim.failure cause)
  /-- **The second checkpoint.** When that frame is passed the flag is true again: between the
  getter and the body's mask an interruptible caller is interruptible. -/
  between : ∀ fr : FFiber,
    ((Prim.setInterruptible true : NCode).ensure fr).fst.interruptible = true
  /-- A masked caller has neither checkpoint: the getter pushes no frame on its stack, and the
  body's mask leaves it masked. -/
  maskedCaller : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool),
    f.frame.interruptible = false →
      (evaluatePrim.withFiber interp m f y WithFiberAction.getInterruptible).fiber.frame.stack =
        f.frame.stack

/-- **The printed form's profile** (the claim `mask-printed-form-profile`; concept
`translation-simulation`, requirements R10 and R11; decisions rows 245 and 246).

Reach: the checker at any signature; program syntax at any lawful spelling; the frame machine
at any interpreter, machine and fiber. The two checkpoints are stated as steps and frame
passes of the machine, from `saved_mask_restoration`.

It does not establish equality with the native spelling, and it states no agreement with a
named release: that the compiled form and the pin's printed form answer one observation is a
finite check (`harness/truth/Truth.lean`, `pMaskWait` and `pMaskedRestore`), and the cuts at
the two checkpoints on the pin are Codex's runs. That the form spends three operations more
than the native mask is measured, not proved (`Test/Program/MaskContract.lean`, S8). The
form's contract has one premise for its clients: nothing is acquired or registered before the
body begins. Under it an interrupt at either checkpoint equals an interrupt before the form.

Its consumers are the Queue's waiting wrapper and the Semaphore's protected permit, whose
first step is inside the body. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem mask_printed_form_profile : MaskFormProfile where
  expansion := fun saved body env p b hb =>
    Authoring.uninterruptibleMask_elaborates saved body env p b hb
  typed := maskForm_typed
  siteTyped := restore_typed
  siteRefused := restore_untyped
  readable := fun _ _ n body => mask_readable n body
  roundTrip := fun _ _ hl _ _ hr => roundTrip_of_readable hl hr
  insideGetter := fun interp m f y =>
    ⟨by rw [withFiber_getInterruptible]; exact FrameFiber.uninterruptible_flag f.frame,
      saved_mask_restoration.getterSaved interp m f y⟩
  getterPending := saved_mask_restoration.pendingExit
  between := fun fr => (saved_mask_restoration.returned true fr).1
  maskedCaller := fun interp m f y masked => by
    rw [saved_mask_restoration.getterSaved interp m f y, masked]
    rfl

end Profile

end Effect4.Program
