import Cas.Lang.Roots

/-!
# The word extension — history as an operation (ruling: cas_word)

The word is the run's history: bindings in admission order, strictly
more information than the store it projects onto — `Word.toStore` is
many-to-one, and the `shared-chunk` vector's fifth binding is history,
not content. That the extra information is unreachable from inside
`CasSig` — that no program of the store language recovers it — is
COMMISSIONED, not proved here (decision 28, docket item 8): the
many-to-one-ness of `Word.toStore` is a fact about the projection, and
an unreachability claim quantifies over programs. Until this module,
the word was interpreter state only: threaded by `step`, carried by
`RootedState`, answered per `cas_run` call, and never readable from
inside the language. This module makes reading it an operation.

`WordSig` speaks one operation, `since (mark : Nat)`: answer the suffix
of the word from a zero-based index. The mark is an index, never a
timestamp — half-open, so `since 0` is the whole history, `since
(w.length)` is what is new, and an empty answer is "nothing happened".
Browse, history, and change feed are one operation because the word is
append-only.

The worded language is the signature sum `WordedSig := StoreSig ⊕ₛ
WordSig`, on `RootSig`'s exact precedent — publication was the last
signature growth, and history enters the same way: its own signature,
never baked into the core. `CasSig` stays frozen at put/load/fail.

No new state is minted: the interpreter runs over `RootedState`
unchanged, because the word `since` reads is the exact word `step` has
been threading all along — the first component. Store operations
DELEGATE to `stepRooted` (and through it to `step`), so admission
still lives in one place; `since` reads and never writes.

The laws carried here: `since_suffix` (the answer is `w.drop mark`,
a suffix of the word, and the state is untouched), `since_zero`
(`since 0` answers the whole word), `since_cas_agrees` (on a Cas
operation the worded STATE evolves exactly as `step` evolves the word,
and the roots are unchanged — the state component only; see its own
docstring), and `stepWorded_preserves_wf` (the worded interpreter
preserves word admission, through the delegation). Beside them, the
feed laws: `since_next` (reading from your last cursor answers exactly
what happened since — why the history document's `next` can be trusted
across growth), `since_compose` (the answer at a composed mark IS the
fetched page re-marked, so a client may re-mark inside a page and the
store agrees), and `runWorded_preserves_wf` (preservation through any
fuel).

Statement triage against the commissioned shape
(`.staging/paper-notes/11-api-contract.md:454-503`): the contract
spells the operation `since (from : Nat)`; `from` is a Lean keyword
and cannot be a binder, so the field is `mark` — the same correction
the dispatch itself anticipated. The contract folds "`since 0` is the
word" into `since_suffix`'s prose; here it is its own named theorem,
because the two claims quantify differently. Everything else lands as
commissioned: the sum parses as `(CasSig ⊕ₛ RootSig) ⊕ₛ WordSig`
(`⊕ₛ` is left-associative), which is `StoreSig ⊕ₛ WordSig`.
-/

namespace Cas.Lang

/-- The word operation: read the history from a mark. The mark is a
zero-based word index, half-open — never a timestamp. -/
inductive WordE where
  | since (mark : Nat)

/-- What the interpreter owes the word operation: the word's suffix
from the mark. -/
abbrev WordE.Ans : WordE → Type
  | .since _ => Word

/-- The word extension: history as a signature. -/
def WordSig : Sig := ⟨WordE, WordE.Ans⟩

/-- The worded store language: store, publication, and history. -/
def WordedSig : Sig := StoreSig ⊕ₛ WordSig

/-- A rooted store program, spoken inside the worded language. -/
def liftWordedStore : Prog StoreSig A → Prog WordedSig A := Prog.inl

/-- Read the history from a mark: the word's suffix, in admission
order. `since 0` is the whole history; an empty answer is "nothing
happened since the mark". -/
def since (mark : Nat) : Prog WordedSig Word :=
  .vis (Sum.inr (.since mark)) .pure

section InterpWorded

variable (H : Bytes → Addr32)

/-- Consume exactly one operation of the worded language. A store
operation (Cas or roots) delegates to `stepRooted` — the residual
program is re-injected and bound to the waiting continuation, so
admission and publication live where they always did. `since` answers
the word's suffix from the mark and changes nothing. -/
def stepWorded : Prog WordedSig A → RootedState →
    Status WordedSig A × RootedState
  | .pure a, s => (.done a, s)
  | .vis (Sum.inl e) k, s =>
    match stepRooted H (.vis e .pure) s with
    | (.running rest, s') => (.running (rest.inl.bind k), s')
    | (.done r, s') => (.running (k r), s')
    | (.refused why, s') => (.refused why, s')
  | .vis (Sum.inr (.since mark)) k, (w, roots) =>
    (.running (k (w.drop mark)), (w, roots))

/-- The answer `since` binds is `w.drop mark` — a suffix of the word —
and the state is untouched: reading history changes nothing. -/
theorem since_suffix {A} (mark : Nat) (k : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    stepWorded H (.vis (Sum.inr (.since mark)) k) (w, roots)
        = (.running (k (w.drop mark)), (w, roots))
      ∧ w.drop mark <:+ w :=
  ⟨rfl, ⟨w.take mark, List.take_append_drop mark w⟩⟩

/-- `since 0` answers the whole word — the mark's zero is the whole
history, by the index being zero-based. -/
theorem since_zero {A} (k : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    stepWorded H (.vis (Sum.inr (.since 0)) k) (w, roots)
      = (.running (k w), (w, roots)) := by
  simp [stepWorded]

/-- On a Cas operation the worded STATE evolves exactly as `step`
evolves the word, and the roots are unchanged. Delegation through
`stepRooted`, stated end to end.

The equation is over the state component — the `.2` — and constrains
nothing else: it does not say what status the step returns, and so it
is not the claim that wording changes no Cas answer. That the answer
is the same one `step` binds is `stepWorded`'s delegation clause by
construction, which is a different kind of fact than this theorem. -/
theorem since_cas_agrees {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) := by
  cases hs : step H (.vis e .pure) w with
  | mk st w' => cases st <;> simp [stepWorded, stepRooted, hs]

/-- The worded interpreter preserves word admission — through the
delegation, `stepRooted_preserves_wf` does the work; `since` reads and
never writes. -/
theorem stepWorded_preserves_wf {A} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (stepWorded H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl e) k =>
    have h := stepRooted_preserves_wf H (.vis e .pure) roots hw
    cases hs : stepRooted H (.vis e .pure) (w, roots) with
    | mk st s' =>
      rw [hs] at h
      cases st <;> simpa [stepWorded, hs] using h
  | .vis (Sum.inr (.since mark)) k => exact hw

/-- THE FEED LAW: reading from your last cursor answers exactly what
happened since. When the word has grown from `w` to `w ++ v`, `since
w.length` binds exactly `v` — which is why the history document's
`next` is a cursor a client can trust across growth, and why polling
`since` and streaming it are the same operation under different
handlers. -/
theorem since_next {A} (k : Word → Prog WordedSig A)
    (w v : Word) (roots : List Addr32) :
    stepWorded H (.vis (Sum.inr (.since w.length)) k) (w ++ v, roots)
      = (.running (k v), (w ++ v, roots)) := by
  simp [stepWorded]

/-- MARKS COMPOSE, as an operation of the language: what the store
answers at mark `a + b` IS the page fetched at mark `a`, re-marked
from `b` inside it. So a client holding a page may re-mark within it
and be sure the store agrees — the client never has to re-fetch to
find out. Stated over `stepWorded` rather than over `List.drop`,
because the claim is about what the operation answers; the drop lemma
is how the proof goes, not what the theorem says. -/
theorem since_compose {A} (a b : Nat) (k : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    stepWorded H (.vis (Sum.inr (.since (a + b))) k) (w, roots)
      = (.running (k ((w.drop a).drop b)), (w, roots)) := by
  have h : (w.drop a).drop b = w.drop (a + b) := by
    rw [List.drop_drop, Nat.add_comm]
  simp [stepWorded, h]

/-- Iterated `stepWorded` with fuel, mirroring `runRooted`. -/
def runWorded (fuel : Nat) (p : Prog WordedSig A) (s : RootedState) :
    Status WordedSig A × RootedState :=
  match fuel with
  | 0 => (.running p, s)
  | fuel + 1 =>
    match stepWorded H p s with
    | (.running rest, s') => runWorded fuel rest s'
    | halted => halted

/-- Running preserves word admission through any fuel — the worded
face of `run_preserves_wf`: no program of the worded language can
un-close a store's history. -/
theorem runWorded_preserves_wf (fuel : Nat) (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (runWorded H fuel p (w, roots)).2.1 = true := by
  induction fuel generalizing p w roots with
  | zero => exact hw
  | succ f ih =>
    unfold runWorded
    have hstep := stepWorded_preserves_wf H p roots hw
    cases hs : stepWorded H p (w, roots) with
    | mk st s' =>
      rw [hs] at hstep
      cases st with
      | running rest =>
        obtain ⟨w', roots'⟩ := s'
        exact ih rest roots' hstep
      | done a => exact hstep
      | refused why => exact hstep

end InterpWorded

end Cas.Lang
