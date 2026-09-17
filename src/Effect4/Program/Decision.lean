import Effect4.Program.Ty
import Effect4.Store.Val

/-!
# Program.Decision — how a value-decided fork selects its arm

**What it is.** The carrier of `Eff.select`'s decision (the `select` packet,
`docs/research/2026-09-16-select-and-iterate-ready-packet.md` §1.1): one function for the
runtime (`decide`, which arm runs and what it binds) and one for the checker (`arms`, what
each arm's environment gains from the scrutinee's type). The compiler, the reference, the
meaning, `effTy` and `HasTy` all read these two, so they agree by construction, as
`catchIf`'s error test does. Child 0 is the arm the decision names first.

**Depends on.** `Ty` (the tag algebra `taggedColumn`, `payloadTy`, `diffTag`) and the store's
`Val`. Nothing about the machine.

**Properties.**
* `arms_length`: the arms bind exactly `binds` values, so a reader's binder depth and the
  checker's environment extension cannot drift — *proved*.
* `decide_typed` (`Laws/Program/Decision.lean`): a typed scrutinee always decides and the
  bound value has the arm's type — the whole "no `badShape` on an admitted program" story
  for the construct.
-/

namespace Effect4.Program
open Effect4.Store

/-- The payload of a tagged pair `[tag, payload]`; `none` on every other value. The one
reader of a tagged value; `NativeAtom.tagHit` is its Boolean image
(`NativeAtom.tagHit_eq`, `Laws/Program/Decision.lean`). -/
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

/-- How many values each child binds, for the readers' binder depth. -/
def binds : Decision → Nat × Nat
  | .bool => (0, 0)
  | .option => (0, 1)
  | .tag _ => (1, 1)

theorem arms_length (d : Decision) (t : Ty) (e0 e1 : List Ty) (h : d.arms t = some (e0, e1)) :
    (e0.length, e1.length) = d.binds := by
  cases d with
  | bool =>
    simp only [arms, binds] at h ⊢
    split at h
    · try simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h0, h1⟩ := h
      subst h0; subst h1; rfl
    · simp at h
  | option =>
    simp only [arms, binds] at h ⊢
    split at h
    · try simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h0, h1⟩ := h
      subst h0; subst h1; rfl
    · simp at h
  | tag name =>
    simp only [arms, binds] at h ⊢
    split at h
    · cases hp : Ty.payloadTy name t.normalize
      · simp [hp] at h
      · try simp only [hp, Option.map, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h0, h1⟩ := h
        subst h0; subst h1; rfl
    · simp at h

end Decision
end Effect4.Program
