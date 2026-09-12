import Effect4.Program.Admit
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.TypeAlgebra

/-!
# Program.Admit — what a checked decision and a checked replay establish

Rows: DI-26 (the failure branch of an external answer), DI-62 (the error image), DI-17
(environments at an allocation state). Battery: `Test/Api/ExternalContract.lean`,
`Test/Api/AcquireHandleContract.lean`, and the pins in `Test/Program/TypedContract.lean`.

This module owns the laws of `src/Effect4/Program/Admit.lean`: which row a passed decision
check identifies, what the accepted answer's converted value is typed as and in which
allocation table, that an accepted completion names only live handles, and that a checked
replay walks exactly the tape the unchecked one walks. Since 2026-09-09 it also owns the
error side of that boundary — the round-trip laws of `errOf`/`valOfErr`, the bridge from
`errAdmits` (`src/Effect4/Program/Compile.lean`) to the parameterised fold `reasonAdmits`
(`src/Effect4/Program/ErrorImage.lean`), `hasTyCause`, and the two failure-branch theorems
that stand beside the three success-only ones.

What it refuses to claim: nothing here types a whole machine, a reachable point or a
retained state; `external_error_typed` is a statement about one accepted completion at one
parked call, and `hasTyCause` reads a *reified* cause, never a live fiber's.

`Program/ErrorImage` is below `Native` and `Typed`; the executable wrappers live in
`Program/Typed`. The laws here import those definitions and do not duplicate them.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The executable lookup reads exactly the handle kinds counted by `MintedIn`. -/
theorem handleLive_eq (m : NativeMachine) (code : UInt8 × Nat) :
    handleLive m code =
      match Handle.ofCode code with
      | some h => h.existsIn m.world
      | none => true := by
  unfold handleLive Handle.ofCode
  cases hk : HandleKind.ofByte? code.1 with
  | none => rfl
  | some kind =>
    cases kind <;> simp [Handle.existsIn, RunMachine.world] <;> rfl

/-- Every recognized handle in the value is live, in the existing judgment. -/
theorem mintedIn_iff_MintedIn (m : NativeMachine) (v : Val) :
    mintedIn m v = true ↔ MintedIn m v.keys := by
  constructor
  · intro hm handle hh
    rw [Val.keys_eq_handles] at hh
    obtain ⟨code, hc, hd⟩ := List.mem_filterMap.mp hh
    have hv := List.all_eq_true.mp hm code hc
    rw [handleLive_eq, hd] at hv
    exact hv
  · intro hm
    apply List.all_eq_true.mpr
    intro code hc
    rw [handleLive_eq]
    cases hd : Handle.ofCode code with
    | none => rfl
    | some handle =>
      apply hm handle
      rw [Val.keys_eq_handles]
      exact List.mem_filterMap.mpr ⟨code, hc, hd⟩

/-- A successful decision check identifies the row of the actual guard token. -/
theorem admitted_row (table : RowTable) (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann)
    (h : admit table m (.answerAsync fiber token answer) = none) :
    ∃ i request row, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧ admitAnswer row m fiber token answer = none := by
  simp only [admit] at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  exact ⟨_, _, _, by assumption, by assumption, h⟩

/-- A successful conversion returns a value with the declared type in the resulting
allocation table. The input scalar index is not itself claimed to have a handle type. -/
theorem externalValue_typed (ty : Ty) (allocated allocated' : List String) (value result : Val)
    (h : externalValue ty allocated value = some (allocated', result)) :
    Val.hasTy result ty allocated' = true := by
  unfold externalValue at h
  split at h
  · rename_i target index
    split at h
    · rename_i ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨ht, rfl⟩ := ha
      have hk : HandleKind.ofByte? 7 = some .external := rfl
      simp only [Val.hasTy, hk, ht, Bool.true_and]
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero]
      change decide (target = target) = true
      exact of_decide_eq_self_eq_true target
    · cases h
  · split at h
    · rename_i ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact (Bool.and_eq_true_iff.mp ha).1
    · cases h

/-- Admission returns a conversion whose actual output, including a freshly minted
handle, inhabits the parked row's answer type. -/
theorem external_answer_typed (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (value : Val)
    (h : admit table m (.answerAsync fiber token (.ofExit (.success value))) = none) :
    ∃ i request row allocated result, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧
      externalValue row.answer m.state.externals.allocated value = some (allocated, result) ∧
      Val.hasTy result row.answer allocated = true := by
  obtain ⟨i, request, row, hp, hr, ha⟩ := admitted_row table m fiber token _ h
  cases hv : externalValue row.answer m.state.externals.allocated value with
  | none => simp [admitAnswer, hv] at ha
  | some converted =>
    obtain ⟨allocated, result⟩ := converted
    exact ⟨i, request, row, allocated, result, hp, hr, hv,
      externalValue_typed _ _ _ _ _ hv⟩

/-- The oracle has the same typed conversion as the delayed decision path. -/
theorem external_oracle_typed (table : RowTable) (i : Nat) (value : Val)
    (allocated : List String)
    (h : externalAdmits table i (.ofExit (.success value)) allocated = true) :
    ∃ row allocated' result, externalRow table i = some row ∧
      externalValue row.answer allocated value = some (allocated', result) ∧
      Val.hasTy result row.answer allocated' = true := by
  cases hr : externalRow table i with
  | none => simp [externalAdmits, hr] at h
  | some row =>
    cases hv : externalValue row.answer allocated value with
    | none => simp [externalAdmits, hr, hv] at h
    | some converted =>
      obtain ⟨allocated', result⟩ := converted
      exact ⟨row, allocated', result, rfl, hv, externalValue_typed _ _ _ _ _ hv⟩

/-! ## The error image and the failure branch

Rows DI-62 and DI-26. The three theorems above are success-only, and `errAdmits`
(`src/Effect4/Program/Compile.lean`) was cited by no theorem at all. What follows closes
that side: `errOf` and `valOfErr` are partial inverses, `errAdmits` *is* the parameterised
fold of `src/Effect4/Program/ErrorImage.lean` at `Val.hasTy`, and an accepted failing
completion carries a cause every reason of which stays inside the parked row's error column.

The bridge is the load-bearing one. At the S2 cutover `errAdmits`'s body is replaced by
`reasonAdmits (fun v t => Val.hasTy v t) ty r`; `errAdmits_eq_reasonAdmits` is the receipt
that the replacement changes no verdict on any reason, so `admitAnswer`, `externalAdmits`,
every tape and every golden read the same. Source of the proofs: scout B
(`docs/research/2026-09-09-scout-proof-statements.md` §3), reproved here against the
production definitions unchanged. -/

/-- A value read out of the error alphabet rebuilds the same error (`errOf` on the left
inverse of `valOfErr`). `boom` has no image, so it is excluded by the hypothesis rather than
by a side condition. -/
theorem errOf_valOfErr (e : Err) (v : Val) (h : valOfErr e = some v) : errOf v = e := by
  cases e with
  | boom => cases h
  | tag n => cases Option.some.inj h; rfl
  | tagged t m => cases Option.some.inj h; rfl
  | text s => cases Option.some.inj h; rfl

/-- A value that is not collapsed by `errOf` is recovered by `valOfErr`. The premise is the
collapse itself: `errOf` sends every unrecognised shape to `boom`, and a collapse has no
inverse. Natural, text, and two-string payloads all have an exact inverse (DI-62). -/
theorem valOfErr_errOf (v : Val) (h : errOf v ≠ .boom) : valOfErr (errOf v) = some v := by
  unfold errOf at h ⊢
  split at h <;> simp_all [valOfErr]

theorem hasTy_isTagTy_allocation (ty : Ty) (v : Val) (allocated : List String)
    (ht : isTagTy ty = true) : Val.hasTy v ty allocated = Val.hasTy v ty [] := by
  induction ty with
  | string | lit _ => rfl
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp ht
    simp only [Val.hasTy, iha ha, ihb hb]
  | _ => contradiction

theorem isTagTy_string (ty : Ty) (v : Val) (allocated : List String)
    (ht : isTagTy ty = true) (hv : Val.hasTy v ty allocated = true) :
    ∃ s : String, v = Val.str s := by
  induction ty with
  | string =>
    cases v with
    | str s => exact ⟨s, rfl⟩
    | _ => simp [Val.hasTy] at hv
  | lit s =>
    cases v with
    | str s' => exact ⟨s', rfl⟩
    | _ => simp [Val.hasTy] at hv
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp ht
    obtain h | h := Bool.or_eq_true_iff.mp hv
    · exact iha ha h
    · exact ihb hb h
  | _ => contradiction

/-- The structural error profile has allocation-independent membership. -/
private theorem hasTy_rawSupported_allocation (ty : Ty) (v : Val) (allocated : List String)
    (hs : rawSupportedErrTy ty = true) : Val.hasTy v ty allocated = Val.hasTy v ty [] := by
  induction ty with
  | never | nat | string | lit _ => rfl
  | prod a b _ _ =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs
    have hb' : b = .string := by
      revert hb
      cases b <;> intro hb <;> try contradiction
      rfl
    subst hb'
    simp only [Val.hasTy]
    cases v with
    | list vs =>
      cases vs with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y ys =>
          cases ys with
          | nil =>
            simp only [hasTy_isTagTy_allocation a x allocated ha]
          | cons _ _ => rfl
    | _ => rfl
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs
    simp only [Val.hasTy, iha ha, ihb hb]
  | unit | int | bool | handle | option | list | except | exitOf | causeOf | fiberOf =>
    simp only [rawSupportedErrTy] at hs
    contradiction

/-- Row DI-62. Supported error membership does not depend on resource allocation. -/
theorem hasTy_supported_allocation (ty : Ty) (v : Val) (allocated : List String)
    (hs : supportedErrTy ty = true) : Val.hasTy v ty allocated = Val.hasTy v ty [] := by
  rw [← hasTy_normalize ty v allocated, ← hasTy_normalize ty v []]
  exact hasTy_rawSupported_allocation ty.normalize v allocated hs

/-- Values in the structural error profile recover from the closed error image. -/
private theorem valOfErr_errOf_rawSupported (ty : Ty) (v : Val) (allocated : List String)
    (hs : rawSupportedErrTy ty = true) (hv : Val.hasTy v ty allocated = true) :
    valOfErr (errOf v) = some v := by
  induction ty with
  | never => simp only [Val.hasTy] at hv; contradiction
  | nat =>
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    rfl
  | string =>
    obtain ⟨s, rfl⟩ := Val.hasTy_string_inv hv
    rfl
  | lit s =>
    cases v with
    | str s' =>
      simp only [Val.hasTy, beq_iff_eq] at hv
      subst hv
      rfl
    | _ => simp [Val.hasTy] at hv
  | prod a b _ _ =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs
    have hb' : b = .string := by
      revert hb
      cases b <;> intro hb <;> try contradiction
      rfl
    subst hb'
    cases v with
    | list vs =>
      cases vs with
      | nil => simp [Val.hasTy] at hv
      | cons x xs =>
        cases xs with
        | nil => simp [Val.hasTy] at hv
        | cons y ys =>
          cases ys with
          | cons _ _ => simp [Val.hasTy] at hv
          | nil =>
            simp only [Val.hasTy, Bool.and_eq_true_iff] at hv
            obtain ⟨hx, hy⟩ := hv
            obtain ⟨s, rfl⟩ := isTagTy_string a x allocated ha hx
            obtain ⟨m, rfl⟩ := Val.hasTy_string_inv hy
            rfl
    | _ => simp [Val.hasTy] at hv
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs
    obtain h | h := Bool.or_eq_true_iff.mp hv
    · exact iha ha h
    · exact ihb hb h
  | unit | int | bool | handle | option | list | except | exitOf | causeOf | fiberOf =>
    simp only [rawSupportedErrTy] at hs
    contradiction

/-- Row DI-62. Every admitted error value is recovered exactly from its closed error image. -/
theorem valOfErr_errOf_supported (ty : Ty) (v : Val) (allocated : List String)
    (hs : supportedErrTy ty = true) (hv : Val.hasTy v ty allocated = true) :
    valOfErr (errOf v) = some v := by
  apply valOfErr_errOf_rawSupported ty.normalize v allocated hs
  rw [hasTy_normalize]
  exact hv

/-- Row DI-62. The admitted error language excludes the payload-discarding `boom` case. -/
theorem errOf_ne_boom_of_supported (ty : Ty) (v : Val) (allocated : List String)
    (hs : supportedErrTy ty = true) (hv : Val.hasTy v ty allocated = true) :
    errOf v ≠ .boom := by
  intro collapsed
  have recovered := valOfErr_errOf_supported ty v allocated hs hv
  rw [collapsed] at recovered
  cases recovered

/-- A decoded closed error image contains no resource handles. -/
theorem valOfErr_keys (e : Err) (v : Val) (h : valOfErr e = some v) : v.keys = [] := by
  cases e with
  | boom => cases h
  | tag n => cases Option.some.inj h; rfl
  | tagged t m => cases Option.some.inj h; rfl
  | text s => cases Option.some.inj h; rfl

/-- Row DI-62. Converting a well-typed supported error gives an admitted failure reason. -/
theorem errAdmits_errOf (ty : Ty) (v : Val) (allocated : List String)
    (a : ReasonAnnotations Ann)
    (hs : supportedErrTy ty = true) (hv : Val.hasTy v ty allocated = true) :
    errAdmits ty (.fail (errOf v) a) = true := by
  simp only [errAdmits, reasonAdmits, valOfErr_errOf_supported ty v allocated hs hv]
  rw [← hasTy_supported_allocation ty v allocated hs]
  exact hv

/-- Row DI-31. `orDie` retains text and package payloads, and the historical numeric/raw cases. -/
theorem orDieCause_fail (e : Err) :
    orDieCause (Cause.fail e) =
      Cause.die (match e with
        | .boom => Defect.badName
        | .tag n => Defect.user n
        | .tagged t m => Defect.error (.tagged t m)
        | .text s => Defect.error (.text s)) := by
  cases e <;> rfl

/-- The production reason predicate is the shared fold at default-allocation membership. -/
theorem errAdmits_eq_reasonAdmits (ty : Ty) (r : Reason Err Defect FiberId Ann) :
    errAdmits ty r = reasonAdmits (fun v t => Val.hasTy v t) ty r := rfl

/-- The bridge as an equality of the two predicates. Stated because it is the shape a
rewrite under a higher-order argument wants; it needs `funext`, so it carries `Quot.sound`
and nothing below depends on it. -/
theorem reasonAdmits_hasTy (ty : Ty) :
    reasonAdmits (fun v t => Val.hasTy v t) ty = errAdmits ty :=
  funext fun r => (errAdmits_eq_reasonAdmits ty r).symm

/-- The cause fold at `Val.hasTy` is the reason-wise `errAdmits` the admission check runs
(`admitAnswer`'s failure branch, `src/Effect4/Program/Admit.lean`). Proved by induction on
the reason list rather than by `funext` on the predicate, so it stays at `[propext]` and so
do the two failure-branch theorems below. -/
theorem causeAdmits_hasTy (ty : Ty) (c : CauseV) :
    causeAdmits (fun v t => Val.hasTy v t) ty c = c.reasons.all (errAdmits ty) := by
  unfold causeAdmits
  generalize c.reasons = rs
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    rw [List.all_cons, List.all_cons, ih, errAdmits_eq_reasonAdmits]

/-- On a reified failed exit the fold is applied to the cause it was built from. -/
theorem hasTyCause_exitErr_fold (c : CauseV) (e : Ty) :
    hasTyCause (Val.exitErr c) e = causeAdmits (fun w t => Val.hasTy w t) e c := by
  simp only [hasTyCause, Val.cause?_exitErr]

/-- The same, spelled with the production `errAdmits`: scout B's statement. -/
theorem hasTyCause_exitErr (c : CauseV) (e : Ty) :
    hasTyCause (Val.exitErr c) e = c.reasons.all (errAdmits e) := by
  rw [hasTyCause_exitErr_fold, causeAdmits_hasTy]

/-- Row DI-26. An accepted failing completion identifies the parked external row, and every
reason of its cause stays inside that row's declared error column. The counterpart of
`external_answer_typed` on the failure branch: no induction over programs or executions, only
the decision check's own arms. Defects and interruptions are admitted at every error column,
including `never` — a computation with no typed failure can still die or be interrupted. -/
theorem external_error_typed (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (c : CauseV)
    (h : admit table m (.answerAsync fiber token (.ofExit (.failure c))) = none) :
    ∃ i request row, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧ hasTyCause (Val.exitErr c) row.error = true := by
  obtain ⟨i, request, row, hp, hr, ha⟩ := admitted_row table m fiber token _ h
  refine ⟨i, request, row, hp, hr, ?_⟩
  rw [hasTyCause_exitErr]
  change (if c.reasons.all (errAdmits row.error) then (none : Option Refusal)
    else some (.errorType fiber token row.error)) = none at ha
  split at ha
  · assumption
  · cases ha

/-- The oracle registration path has the same failure-branch guarantee as the delayed
decision path (`external_oracle_typed` is its success half). -/
theorem external_oracle_error_typed (table : RowTable) (i : Nat) (c : CauseV)
    (allocated : List String)
    (h : externalAdmits table i (.ofExit (.failure c)) allocated = true) :
    ∃ row, externalRow table i = some row ∧ hasTyCause (Val.exitErr c) row.error = true := by
  cases hr : externalRow table i with
  | none => simp [externalAdmits, hr] at h
  | some row => exact ⟨row, rfl, by simpa [hasTyCause_exitErr, externalAdmits, hr] using h⟩

/-- A successful oracle registration resumes with its converted value, typed against
exactly the allocations in the store it produces. -/
theorem external_registration_typed (program : NativeEff) (table : RowTable)
    (i : Nat) (request : Val) (row : Row) (fiber : FiberId) (token : Nat)
    (before after : Stores) (value : Val)
    (rest : List (Completion Val Err Defect FiberId Ann)) (code : NCode)
    (hrow : externalRow table i = some row)
    (hhead : before.externals.answers = .ofExit (.success value) :: rest)
    (hreg : (interpOf program table).registerAsync (.external (.external i) request)
      fiber token before = (after, some code)) :
    ∃ result, code = .success result ∧ Val.hasTy result row.answer after.externals.allocated = true := by
  have hne : table.isEmpty = false := by
    cases table with
    | nil => simp [externalRow] at hrow
    | cons row rest => rfl
  by_cases ha : externalAdmits table i (.ofExit (.success value)) before.externals.allocated = true
  · cases hv : externalValue row.answer before.externals.allocated value with
    | none => simp [externalAdmits, hrow, hv] at ha
    | some converted =>
      obtain ⟨allocated, result⟩ := converted
      simp only [interpOf, hrow, Option.isNone_some, Bool.false_eq_true, if_false,
        hhead, ha, if_true, prepareExternalAnswer, hv, hne] at hreg
      obtain ⟨rfl, hc⟩ := Prod.mk.inj hreg
      have hc := Option.some.inj hc
      exact ⟨result, hc.symm, externalValue_typed _ _ _ _ _ hv⟩
  · simp only [interpOf, hrow, Option.isNone_some, Bool.false_eq_true, if_false,
      hhead, ha] at hreg
    have hc := congrArg Prod.snd hreg
    cases hc

/-- The request projection identifies the exact current code at the matching guard. -/
theorem requestOf_current (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (op : NativeOp) (request : Val) (h : requestOf m fiber token = some (op, request)) :
    ∃ f controller cancel, m.fiber? fiber = some f ∧ f.parked = .withGuard token ∧
      f.frame.current = .async (.external op request) controller cancel := by
  cases hf : m.fiber? fiber with
  | none => simp [requestOf, hf] at h
  | some f =>
    by_cases hp : f.parked = .withGuard token
    · simp [requestOf, hf, hp, guard] at h
      split at h
      · try simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨f, _, _, rfl, hp, by assumption⟩
      · cases h
    · simp [requestOf, hf, hp, guard] at h
      cases h

/-- An admitted delayed success on a live machine prepares the actual typed resume
code, using exactly the allocation table returned beside that code. -/
theorem external_prepared_answer_typed (program : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : FiberId) (token : Nat) (value : Val)
    (hs : m.stuck = none)
    (ha : admit table m (.answerAsync fiber token (.ofExit (.success value))) = none) :
    ∃ i request row result, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧
      (prepareAsyncAnswer (interpOf program table) m fiber token (.ofExit (.success value))).2 =
        .success result ∧
      Val.hasTy result row.answer
        (prepareAsyncAnswer (interpOf program table) m fiber token
          (.ofExit (.success value))).1.externals.allocated = true := by
  obtain ⟨i, request, row, allocated, result, hreq, hrow, hv, ht⟩ :=
    external_answer_typed table m fiber token value ha
  obtain ⟨f, controller, cancel, hf, hp, hc⟩ := requestOf_current m fiber token _ _ hreq
  have hne : table.isEmpty = false := by
    cases table with
    | nil => simp [externalRow] at hrow
    | cons row rest => rfl
  refine ⟨i, request, row, result, hreq, hrow, ?_, ?_⟩ <;>
    simp only [prepareAsyncAnswer, hs, Option.isSome_none, Bool.false_eq_true, if_false,
      hf, hp, if_true, interpOf, prepareExternalAnswer, hne, hc, hrow, hv]
  exact ht

/-- Every accepted completion names only handles present before the answer. -/
theorem admitAnswer_minted (row : Row) (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann)
    (h : admitAnswer row m fiber token answer = none) : MintedIn m answer.keys := by
  cases answer with
  | ofExit exit =>
    cases exit with
    | success value =>
      cases ht : externalValue row.answer m.state.externals.allocated value with
      | none => simp [admitAnswer, ht] at h
      | some converted =>
        cases hm : mintedIn m value with
        | false => simp [admitAnswer, ht, hm] at h
        | true => exact (mintedIn_iff_MintedIn m value).mp hm
    | failure cause => simp [Completion.keys, exitKeys, MintedIn, Ok]
  | ofRefGet cell =>
    cases hc : m.state.refs[cell.index]? with
    | none => simp [admitAnswer, hc] at h
    | some value =>
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hc
      simp [Completion.keys, MintedIn, Ok, Handle.existsIn, RunMachine.world, hlt]

/-- Admission strengthens the existing tape premise at each inspected decision. -/
theorem admitted_decision_minted (table : RowTable) (m : NativeMachine) (d : NativeDecision)
    (h : admit table m d = none) :
    (match d with
      | .answerAsync _ _ answer => decide (MintedIn m answer.keys)
      | _ => true) = true := by
  cases d with
  | answerAsync fiber token answer =>
    obtain ⟨_, _, row, _, _, ha⟩ := admitted_row table m fiber token answer h
    exact decide_eq_true (admitAnswer_minted row m fiber token answer ha)
  | _ => rfl

/-- A checked replay which returns a run satisfies `AnswersValidAt`'s exact walk,
including its stopping rules at a stuck machine or exhausted driver fuel. -/
theorem replayCheckedFrom_answersValid (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) (r : NativeReplay)
    (h : replayCheckedFrom program fuel answers table position tape m = .inl r) :
    letI := evaluatorFor program table
    AnswersValidAt (interpOf program table) fuel tape m := by
  letI := evaluatorFor program table
  change answersValid (interpOf program table) fuel tape m = true
  induction tape generalizing position m r with
  | nil => rfl
  | cons decision rest ih =>
    cases hs : m.stuck with
    | some why => simp [answersValid, hs]
    | none =>
      cases ha : admit table m decision with
      | some why => simp only [replayCheckedFrom, hs, ha] at h; cases h
      | none =>
        simp only [answersValid, hs]
        apply Bool.and_eq_true_iff.mpr
        constructor
        · have hd := admitted_decision_minted table m decision ha
          cases decision <;> exact hd
        ·
          generalize he : stepDecisionState (interpOf program table) fuel m decision = next at h ⊢
          rcases next with ⟨m', continued⟩
          cases continued with
          | false => rfl
          | true =>
            simp only [replayCheckedFrom, hs, ha, he, if_true] at h
            cases ho : oracleRefusal answers table m' with
            | some why => simp only [ho] at h; cases h
            | none =>
              simp only [ho] at h
              exact ih (position + 1) m' r h

/-- Successful checking returns the very run obtained by the original tape walker. -/
theorem replayCheckedFrom_eq_replay (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) (r : NativeReplay)
    (h : replayCheckedFrom program fuel answers table position tape m = .inl r) :
    letI := evaluatorFor program table
    r = replayEval (interpOf program table) fuel tape m := by
  letI := evaluatorFor program table
  induction tape generalizing position m r with
  | nil =>
    simp only [replayCheckedFrom] at h
    exact Sum.inl.inj h.symm
  | cons decision rest ih =>
    cases hs : m.stuck with
    | some why =>
      simp only [replayCheckedFrom, hs] at h
      cases h
      simp only [replayEval, hs]
    | none =>
      cases ha : admit table m decision with
      | some why => simp only [replayCheckedFrom, hs, ha] at h; cases h
      | none =>
        simp only [replayCheckedFrom, hs, ha] at h
        simp only [replayEval, hs]
        generalize he : stepDecisionState (interpOf program table) fuel m decision = next at h ⊢
        rcases next with ⟨m', continued⟩
        cases ho : oracleRefusal answers table m' with
        | some why => simp only [ho] at h; cases h
        | none =>
          simp only [ho] at h
          cases continued with
          | false => exact Sum.inl.inj h.symm
          | true =>
            simp only [if_true] at h ⊢
            exact ih (position + 1) m' r h

/-! ## Environments at a compiled point

Row DI-17. `FitsIn` and its append lemma are stated in `src/Effect4/Laws/Program/Typed.lean`,
where the value typing is; `Point` is a compile-time structure
(`src/Effect4/Program/Compile.lean`), above that module, so the one lemma that mentions a
point lands here instead. It is `FitsIn.append` read at `Point.childWith`: a child point
that binds one answer extends its parent's environment on the right, so the parent's fit at
an allocation table extends to the child's whenever the bound value has the bound type. -/

/-- A child point binding one answer keeps the fit (scout B's `fits_childWith`). -/
theorem fits_childWith (allocated : List String) (p : Point) (ts : TyEnv) (i : Nat)
    (v : Val) (t : Ty) (hf : FitsIn allocated p.env ts)
    (hv : Val.hasTy v t allocated = true) :
    FitsIn allocated (p.childWith i v).env (ts ++ [t]) :=
  FitsIn.append hf hv

end Effect4.Program
