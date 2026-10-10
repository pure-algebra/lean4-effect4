import Effect4.Laws.Api.SessionMeaning

/-!
# Program.RowProtocol — the row table's types as a protocol of its hosts

The type algebra meets the coalgebra here. A row of the table has an answer column and an error
column, types of `Ty`. Its protocol (`rowProtocol`) admits an exit at a row exactly when the
row's columns admit it (`externalAdmits`, `Program/Compile.lean`): a success value is a member of
the answer type, and a failure's causes fit the error type. It is the session's admission at the
row's template. `guardRows` turns any host into one that meets it (`Effects.Comodel.guard`), and
guarding a host that already meets it changes nothing.

So H9 holds for the typed host: a run whose answers a host gave, each admitted by its row, is a run
whose answers the guarded host gave (`hostAnswered_guardRows`), and the host's run of the call tree
under the guarded host is the run's observation.

Placement: concept `host-session-protocol`, a compatibility helper; claim: none of its own yet,
a step toward R6's open part "the host as a relation between the machine's calls and its answers".
Consumer: typed hosts on the run interface (the coalgebra note, slice CO-6). It does not establish
the session's admission at a call's checked instance, which reads the call's site
(`acceptAtInstance`): a protocol at sites needs a signature indexed by the call site, the note's
CO-7.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-- Whether a row's columns admit an exit: the row's template admission. -/
def rowAdmits (table : RowTable) : (op : (RowSig table).Op) → (RowSig table).Answer op → Bool :=
  fun op ex => externalAdmits table op.1.val (.ofExit ex) []

/-- **The row table's protocol**: at a row, the exits its columns admit. -/
def rowProtocol (table : RowTable) : Effects.Protocol (RowSig table) :=
  fun op ex => rowAdmits table op ex = true

/-- A host behind the row table's protocol: it refuses every exit its row does not admit. -/
def guardRows (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ) :
    Effects.Comodel (RowSig table) σ :=
  host.guard (rowAdmits table)

/-- The guarded host meets the row table's protocol. -/
theorem guardRows_meets (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ) :
    (guardRows table host).Meets (rowProtocol table) :=
  Effects.Comodel.guard_meets (rowAdmits table) host

/-- Guarding a host that meets the row table's protocol changes nothing. -/
theorem guardRows_of_meets (table : RowTable) {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    (h : host.Meets (rowProtocol table)) : guardRows table host = host :=
  Effects.Comodel.guard_of_meets h

/-- The guarded host answers as the host does, where the row admits the answer. -/
theorem guardRows_answer (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    {op : (RowSig table).Op} {st st' : σ} {ex : ExitV} (h : host.answer op st = some (ex, st'))
    (hadmit : rowAdmits table op ex = true) : (guardRows table host).answer op st = some (ex, st') := by
  show (host.answer op st).filter (fun result => rowAdmits table op result.1) = _
  rw [h]
  exact if_pos hadmit

/-- **Each answer of a tape is admitted by its row**: at each answer decision, the row the machine
calls admits the decision's exit. -/
def RowsAdmit (table : RowTable) (program : Api.Program) (fuel : Nat) :
    List Api.Decision → Api.Machine → Prop
  | [], _ => True
  | .answerAsync f t (.ofExit ex) :: T, m =>
    (∀ i v, Program.requestOf m f t = some (.external i, v) →
      externalAdmits table i (.ofExit ex) [] = true) ∧
    RowsAdmit table program fuel T (steppedBy program fuel table m (.answerAsync f t (.ofExit ex)))
  | d :: T, m => RowsAdmit table program fuel T (steppedBy program fuel table m d)

/-- **A host's answers, each admitted by its row, are the guarded host's.** -/
theorem hostAnswered_guardRows (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (program : Api.Program) (fuel : Nat) :
    ∀ (T : List Api.Decision) (m : Api.Machine) (st st' : σ),
      HostAnswered table host program fuel T m st st' → RowsAdmit table program fuel T m →
      HostAnswered table (guardRows table host) program fuel T m st st'
  | [], _, _, _, h, _ => h
  | .answerAsync f t (.ofExit ex) :: T, m, st, st'', h, ⟨hadm, hrest⟩ => by
    obtain ⟨i, v, hi, st', hrq, hans, hA⟩ := h
    exact ⟨i, v, hi, st', hrq, guardRows_answer table host hans (hadm i v hrq),
      hostAnswered_guardRows table host program fuel T _ st' st'' hA hrest⟩
  | .answerAsync _ _ (.ofRefGet _) :: T, _, st, st', h, hr =>
    hostAnswered_guardRows table host program fuel T _ st st' h hr
  | .fire _ :: T, _, st, st', h, hr | .flush :: T, _, st, st', h, hr
  | .evaluate _ :: T, _, st, st', h, hr | .yieldVerdict _ _ :: T, _, st, st', h, hr
  | .interruptFrom _ _ _ :: T, _, st, st', h, hr | .installMiddleware :: T, _, st, st', h, hr
  | .advance _ :: T, _, st, st', h, hr =>
    hostAnswered_guardRows table host program fuel T _ st st' h hr

end Effect4.Run
