module

public import Effect4.Program.Record
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

/-- What child 0 and child 1 bind, from the scrutinee's type; `none` refuses the scrutinee.
`.bool` tests the type syntactically (`t = .bool`), the rule the retired `branch` had, which
made its retirement an equality of typing. -/
def arms : Decision → Ty → Option (List Ty × List Ty)
  | .bool, t => if t = .bool then some ([], []) else none
  | .option, t =>
    match t.normalize with
    | .option a => some ([], [a])
    | _ => none
  | .tag name, t =>
    let c := t.normalize
    if Ty.taggedColumn c then (Ty.payloadTy name c).map fun p => ([p], [Ty.diffTag name c])
    else none
  | .recordTag name, t => (Record.tagArms name t).map fun arms => ([arms.1], [arms.2])

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
    split at h
    · cases h; rfl
    · exact nomatch h
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

end Decision
end Effect4.Program
