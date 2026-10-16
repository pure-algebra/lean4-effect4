module

public import Effect4.Program.Record
public import Effect4.Program.TyHead
public import Effect4.Store.Carrier.Val

/-!
# Program.Decision — how a value-decided fork selects its arm

**What it is.** The carrier of `Eff.select`'s decision (the `select` packet,
`docs/research/2026-09-16-select-and-iterate-ready-packet.md` §1.1): one function for the
runtime (`decide`, which arm runs and what it binds) and one for the checker (`arms`, what
each arm's environment gains from the scrutinee's type). The compiler, the reference, the
meaning, `effTy` and `HasTy` all read these two, so they agree by construction, as
`catchIf`'s error test does. Child 0 is the arm the decision names first.

**Depends on.** `Ty`, the record classifier and named-value lookup, and the store's
`Val`. No machine state or evaluator is needed.

**Properties.**
* `arms_length`: the arms bind exactly `binds` values, so a reader's binder depth and the
  checker's environment extension cannot drift — *proved*.
* `decide_typed` (`Laws/Program/Decision.lean`): a typed scrutinee always decides and the
  bound value has the arm's type — the whole "no `badShape` on an admitted program" story
  for the construct.
-/

@[expose] public section

namespace Effect4.Program
open Effect4.Store

/-- The payload of a tagged pair `[tag, payload]`; `none` on every other value. The one
reader of a tagged pair; `NativeAtom.tagHit` is its Boolean image joined with the record
reader's, `Record.tagHit` (`NativeAtom.tagHit_eq`, `Laws/Program/Decision.lean`). -/
def Val.tagPayload? (tag : String) : Val → Option Val
  | .list [.str t, payload] => if t == tag then some payload else none
  | _ => none

/-- How a value-decided fork selects its arm, and what the arm binds. -/
inductive Decision
  /-- `true` runs child 0, `false` child 1; neither binds: the conditional `t ? a : b`. -/
  | bool
  /-- `none` runs child 0; `some a` runs child 1 with `a` bound. -/
  | option
  /-- A tagged pair `[tag, payload]` runs child 0 with the payload bound; every other value
  runs child 1 with the whole value bound, at the residual type (DI-39). -/
  | tag (tag : String)
  /-- A literal-tagged record selects a branch and binds the whole record on both sides. -/
  | recordTag (tag : String)
deriving DecidableEq, Repr

namespace Decision

/-- The runtime selection: whether child 0 was chosen, and the value that child binds.
`none` is the wrong shape (`badShape`; under `.bool`, a test that is not a Boolean). -/
def decide : Decision → Val → Option (Bool × Option Val)
  | .bool, .bool b => some (b, none)
  | .bool, _ => none
  | .option, .none => some (true, none)
  | .option, .some a => some (false, some a)
  | .option, _ => none
  | .tag t, v =>
    match Val.tagPayload? t v with
    | some payload => some (true, some payload)
    | none => some (false, some v)
  | .recordTag name, value => some (Record.tagHit name value, some value)

end Decision

namespace Member

/-- The member rule of the option rule: the element type of one option type, by the head of the
raw type. It refuses `never` and every union. -/
def option : Ty → Option Ty
  | .option a => some a
  | _ => none

end Member

/-- The element type of an option input, read at its normal form.
Every retained normal member must be an option. Their element types join.
At `never` it answers `never`. It keeps the existing normalized answer at a raw option type. -/
def optionTy : Ty → Option Ty := UnionRule.lift Member.option

/-- The element type of an option input under a declaration table: every union member under the
table must be an option. At the empty table it is `optionTy`. -/
def optionTyIn (decls : TyDecls) : Ty → Option Ty := UnionRule.liftIn decls Member.option

/-- The option rule refuses a declared reference. -/
theorem Member.option_ref {decls : TyDecls} :
    ∀ m x, decls.unfold? m = some x → Member.option m = none := by
  intro m x h
  obtain ⟨n, rfl | ⟨args, rfl⟩⟩ := TyDecls.ref_of_unfold? h <;> rfl

/-- **Where the option rule answers, the option rule under a table answers the same.** -/
theorem optionTyIn_of_optionTy {decls : TyDecls} {t a : Ty} (h : optionTy t = some a) :
    optionTyIn decls t = some a :=
  UnionRule.liftIn_of_lift Member.option_ref h

namespace Decision

/-- What child 0 and child 1 bind, from the scrutinee's type; `none` refuses the scrutinee.
`.bool` tests that the scrutinee's type is below `.bool` (`Ty.sub t.normalize .bool`). -/
def arms : Decision → Ty → Option (List Ty × List Ty)
  | .bool, t => if Ty.sub t.normalize .bool then some ([], []) else none
  | .option, t => (optionTy t).map fun a => ([], [a])
  | .tag name, t =>
    let c := t.normalize
    if Ty.taggedColumn c then (Ty.payloadTy name c).map fun p => ([p], [Ty.diffTag name c])
    else none
  | .recordTag name, t => (Record.tagArms name t).map fun arms => ([arms.1], [arms.2])

@[simp] theorem arms_bool_of_sub {t : Ty} (h : Ty.sub t.normalize .bool = true) :
    arms .bool t = some ([], []) := by
  simp only [arms, h, ↓reduceIte]

@[simp] theorem arms_bool : arms .bool .bool = some ([], []) :=
  arms_bool_of_sub (Ty.sub_refl _)

/-- How many values each child binds, for the readers' binder depth. -/
def binds : Decision → Nat × Nat
  | .bool => (0, 0)
  | .option => (0, 1)
  | .tag _ | .recordTag _ => (1, 1)

theorem arms_length (d : Decision) (t : Ty) (e0 e1 : List Ty) (h : d.arms t = some (e0, e1)) :
    (e0.length, e1.length) = d.binds := by
  cases d with
  | bool =>
    simp only [arms, binds] at h ⊢
    split at h
    · cases h; rfl
    · exact nomatch h
  | option =>
    simp only [arms, binds] at h ⊢
    obtain ⟨a, _, heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    rfl
  | tag name =>
    simp only [arms, binds] at h ⊢
    split at h
    · obtain ⟨payload, _, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      rfl
    · exact nomatch h
  | recordTag name =>
    obtain ⟨parts, _, heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    rfl

/-- **What each child binds under a declaration table**: the option and the record-tag decisions
read the scrutinee's union members under the table, so a declared name is read by its body
(the wiring plan, `docs/research/2026-10-16-usability-scope/wiring-plan.md`). At the empty table
it is `arms`. -/
def armsIn (decls : TyDecls) (d : Decision) (t : Ty) : Option (List Ty × List Ty) :=
  match decls with
  | [] => d.arms t
  | _ =>
    match d with
    | .option => (optionTyIn decls t).map fun a => ([], [a])
    | .recordTag name => (Record.tagArmsIn decls name t).map fun arms => ([arms.1], [arms.2])
    | d => d.arms t

/-- The tag of a record member is no declared reference's. -/
theorem _root_.Effect4.Program.Record.tagOf_ref {decls : TyDecls} {m : Ty} {x : String × Ty}
    (h : decls.unfold? m = some x) : Record.tagOf m = none := by
  obtain ⟨n, rfl | ⟨args, rfl⟩⟩ := TyDecls.ref_of_unfold? h <;> rfl

/-- **Where the tag dispatch answers, the tag dispatch under a table answers the same**: every
union member carries a tag, so none is a declared reference. -/
theorem _root_.Effect4.Program.Record.tagArmsIn_of_tagArms {decls : TyDecls} {tag : String}
    {t : Ty} {arms : Ty × Ty} (h : Record.tagArms tag t = some arms) :
    Record.tagArmsIn decls tag t = some arms := by
  simp only [Record.tagArms] at h
  split at h
  · rename_i hall
    have hnone : ∀ m ∈ t.normalize.members, decls.unfold? m = none := by
      intro m hm
      cases hu : decls.unfold? m with
      | none => rfl
      | some x =>
        have htag := List.all_eq_true.mp hall m hm
        rw [Record.tagOf_ref hu] at htag
        cases htag
    have hmembers : Ty.membersIn decls t = t.normalize.members := Ty.membersIn_of_noRefs hnone
    simp only [Record.tagArmsIn, hmembers, hall, ↓reduceIte]
    exact h
  · cases h

/-- **Where the decision's arms answer, they answer the same under a table.** -/
theorem armsIn_of_arms {decls : TyDecls} {d : Decision} {t : Ty} {r : List Ty × List Ty}
    (h : d.arms t = some r) : d.armsIn decls t = some r := by
  cases decls with
  | nil => exact h
  | cons e es =>
    cases d with
    | bool => exact h
    | tag name => exact h
    | option =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      show (optionTyIn (e :: es) t).map (fun a => ([], [a])) = _
      rw [optionTyIn_of_optionTy ha]
      rfl
    | recordTag name =>
      obtain ⟨arms, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      show (Record.tagArmsIn (e :: es) name t).map (fun arms => ([arms.1], [arms.2])) = _
      rw [Record.tagArmsIn_of_tagArms ha]
      rfl

/-- The arms under a table bind exactly `binds` values. -/
theorem armsIn_length (decls : TyDecls) (d : Decision) (t : Ty) (e0 e1 : List Ty)
    (h : d.armsIn decls t = some (e0, e1)) : (e0.length, e1.length) = d.binds := by
  cases decls with
  | nil => exact arms_length d t e0 e1 h
  | cons e es =>
    cases d with
    | bool => exact arms_length .bool t e0 e1 h
    | tag name => exact arms_length (.tag name) t e0 e1 h
    | option =>
      obtain ⟨a, _, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      rfl
    | recordTag name =>
      obtain ⟨parts, _, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      rfl

end Decision
end Effect4.Program
