import Effect4.Program.Typing.CheckCache

/-!
# Certified checking

`CheckInput` names a module check or a part check. `run` uses the existing checking owners.
`Oracle` carries pointwise agreement with `run`. `Checked` records valid answers in request order.
`Memo` learns only these traces and answers through a rule that carries its agreement law.

The generated OCaml interface seals `Oracle`, `Checked`, `Memo`, and `HitRule` as whole packages.
The native boundary uses the existing LCNF translation trust. No arbitrary callback is certified.

Placement: `checker-oracle-agrees`, host-session-protocol, R6/R14.
`Oracle.eq_uncached` states the claim. The trace and memo proofs construct its consumer packages.
Their observation is each check's exact verdict. They assert no native execution or progress theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Effect4.Program
open Effect4 Effect4.Program Effect4.Store

/-! ## 1. Checking -/

namespace Check

/-- Everything one check reads; its canonical bytes are a complete key. -/
inductive CheckInput where
  /-- a sketch through its layer references, at the application extended by its holes; the root
  address `[]` is always checked through this key -/
  | module (app : SigApp) (holes : RowTable) (program : NativeEff)
  /-- a part of an expansion, or a filling inside its candidate's expansion, in its context -/
  | part (sig : SigData) (env : TyEnv) (program : NativeEff)
deriving DecidableEq

/-- A check's answer, rooted at the empty path. -/
structure Verdict where
  result : Except TypeRefusal EffTy
  table : List Table.Entry

/-- The uncached meaning: the existing owners, unchanged. -/
def run : CheckInput → Verdict
  | .module app holes p =>
      let s : Sketch := { program := p, holes := holes }
      ⟨s.sourceCheck app, s.sourceAnnotate app⟩
  | .part d env q =>
      let o := Annotate.check d.signature env [] q
      ⟨o.2, o.1⟩

/-- A certified oracle: the only way a consumer checks. Its agreement field erases. -/
structure Oracle where
  ask : CheckInput → Verdict
  agrees : ∀ i, ask i = run i

def Oracle.uncached : Oracle := ⟨run, fun _ => rfl⟩

/-- **The oracle has one value up to equality.** So a memo or Incremental behind an oracle can
change cost and never an answer, for every consumer at once. -/
theorem Oracle.eq_uncached (o : Oracle) : o = Oracle.uncached := by
  cases o with
  | mk ask agrees =>
    have h : ask = run := funext agrees
    subst h
    rfl

/-- The consequence every consumer inherits, with no proof of its own. -/
theorem Oracle.transparent {α : Sort _} (f : Oracle → α) (o : Oracle) :
    f o = f Oracle.uncached := by
  rw [Oracle.eq_uncached o]

/-- The checks a computation asked, each with its answer, in order. -/
abbrev Trace := List (CheckInput × Verdict)

/-- Every entry is the uncached answer of its key. -/
def TraceValid (t : Trace) : Prop := ∀ p ∈ t, p.2 = run p.1

/-- A consumer's result with its trace: a writer over the certified oracle. The constructor is
private and the validity is a field, so the only traces are those `pure`, `bind` and `ask` build.
The generated OCaml interface keeps the whole package abstract; the trace feeds `Memo.learn` and
never a reply. -/
structure Checked (α : Type) where
  private mk ::
  value : α
  trace : Trace
  valid : TraceValid trace

namespace Checked

def pure' {α : Type} (a : α) : Checked α := ⟨a, [], fun _ h => nomatch h⟩

def bind' {α β : Type} (x : Checked α) (f : α → Checked β) : Checked β :=
  let next := f x.value
  ⟨next.value, x.trace ++ next.trace, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact x.valid p h
    · exact next.valid p h⟩

instance : Monad Checked where
  pure := pure'
  bind := bind'

/-- Ask the oracle and record the key with its answer. Module decomposition lands in V1. -/
def ask (o : Oracle) (i : CheckInput) : Checked Verdict :=
  ⟨o.ask i, [(i, o.ask i)], fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    exact o.agrees i⟩

theorem ask_value (o : Oracle) (i : CheckInput) : (ask o i).value = run i := o.agrees i

end Checked

/-- The learning memo, in-process only. The constructor is private and the validity is a field:
the only memos are `empty` and what `learn` builds from `Checked` traces. Nothing imports
entries, so no call site is trusted; in OCaml the memo's trust is the generated code's, the
existing lowering boundary. -/
structure Memo where
  private mk ::
  entries : Trace
  valid : TraceValid entries

def Memo.empty : Memo := ⟨[], fun _ h => nomatch h⟩

def Memo.learn {α : Type} (m : Memo) (c : Checked α) : Memo :=
  ⟨c.trace ++ m.entries, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact c.valid p h
    · exact m.valid p h⟩

/-- When an entry may answer an asked key. A rule is sound when a valid entry it selects is the
uncached answer of the asked key; the oracle's agreement then follows for every memo. -/
structure HitRule where
  hit : CheckInput → CheckInput × Verdict → Bool
  sound : ∀ i e, hit i e = true → e.2 = run e.1 → e.2 = run i

/-- An exact hit: the entry's key is the asked key. -/
def HitRule.exact : HitRule where
  hit i e := decide (e.1 = i)
  sound i e h he := by
    have hk : e.1 = i := of_decide_eq_true h
    rw [he, hk]

/-- Either rule. -/
def HitRule.or (r s : HitRule) : HitRule where
  hit i e := r.hit i e || s.hit i e
  sound i e h he := by
    simp only [Bool.or_eq_true] at h
    cases h with
    | inl h => exact r.sound i e h he
    | inr h => exact s.sound i e h he

/-- A memo-backed oracle under a sound hit rule: a hit, else `run`. -/
def Memo.oracle (m : Memo) (r : HitRule) : Oracle where
  ask i := match m.entries.find? (r.hit i) with
    | some e => e.2
    | none => run i
  agrees i := by
    show (match m.entries.find? (r.hit i) with
      | some e => e.2
      | none => run i) = run i
    split
    · rename_i e he
      exact r.sound i e (List.find?_some (p := r.hit i) he)
        (m.valid e (List.mem_of_find?_eq_some he))
    · rfl


/-- The native export of the existing value projection. -/
def Checked.readVerdict (c : Checked Verdict) : Verdict := c.value

end Check
end Effect4.Program
