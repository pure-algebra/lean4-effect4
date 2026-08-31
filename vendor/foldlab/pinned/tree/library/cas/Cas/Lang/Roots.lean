import Cas.Lang.Interp

/-!
# Roots — the publication extension (ruling 5)

Roots enter as their own signature, never baked into the core:
`RootSig` speaks `publish`/`listRoots`, mirroring the TypeScript
RootStore seam, and the store-with-roots language is the signature sum
`StoreSig`. Presence stays derived; CasSig stays frozen at
put/load/fail.

The interpreter's state is the word plus the published roots — a
grow-only list. Cas operations DELEGATE to `step` on the word
component; admission is not re-derived here. `publish` is fail-closed:
an address publishes only if the word already binds it (`.noObject`
otherwise — publication of absent content is refused). `listRoots`
answers the list.

The laws carried here: `stepRooted_cas_agrees` (on a Cas op the word
evolves exactly as `step` and roots are unchanged),
`stepRooted_preserves_wf` (delegating to `step_preserves_wf`), and
`publish_mem` (a successful publish's address has a binding in the
word).
-/

namespace Cas.Lang

/-- The root operations: publish an address, list the published. -/
inductive RootE where
  | publish (a : Addr32)
  | listRoots

/-- What the interpreter owes each root operation. -/
abbrev RootE.Ans : RootE → Type
  | .publish _ => Unit
  | .listRoots => List Addr32

/-- The root extension: the RootStore seam as a signature. -/
def RootSig : Sig := ⟨RootE, RootE.Ans⟩

/-- The store-with-roots language: store plus publication. -/
def StoreSig : Sig := CasSig ⊕ₛ RootSig

/-- A store program, spoken inside the rooted language. -/
def liftRootedCas : Prog CasSig A → Prog StoreSig A := Prog.inl

/-- Publish an address as a root. -/
def publish (a : Addr32) : Prog StoreSig Unit :=
  .vis (Sum.inr (.publish a)) .pure

/-- List the published roots. -/
def listRoots : Prog StoreSig (List Addr32) :=
  .vis (Sum.inr .listRoots) .pure

section InterpRooted

variable (H : Bytes → Addr32)

/-- The rooted interpreter state: the word and the published roots,
grow-only. -/
abbrev RootedState := Word × List Addr32

/-- Consume exactly one operation of the rooted language. A Cas
operation delegates to `step` on the word component — the residual
program `step` answers is re-injected and bound to the waiting
continuation, so admission lives in one place. `publish` appends the
address to the roots only if the word binds it; `listRoots` answers
the list. -/
def stepRooted : Prog StoreSig A → RootedState →
    Status StoreSig A × RootedState
  | .pure a, s => (.done a, s)
  | .vis (Sum.inl e) k, (w, roots) =>
    match step H (.vis e .pure) w with
    | (.running rest, w') => (.running (rest.inl.bind k), (w', roots))
    | (.done r, w') => (.running (k r), (w', roots))
    | (.refused why, w') => (.refused why, (w', roots))
  | .vis (Sum.inr (.publish a)) k, (w, roots) =>
    match Word.find w a with
    | some _ => (.running (k ()), (w, roots ++ [a]))
    | none => (.refused (.noObject a), (w, roots))
  | .vis (Sum.inr .listRoots) k, (w, roots) => (.running (k roots), (w, roots))

/-- On a Cas operation the state evolves exactly as `step` evolves the
word, and the roots are unchanged — delegation, stated. -/
theorem stepRooted_cas_agrees {A} (e : CasE)
    (k : CasE.Ans e → Prog StoreSig A) (w : Word) (roots : List Addr32) :
    (stepRooted H (.vis (Sum.inl e) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) := by
  cases hs : step H (.vis e .pure) w with
  | mk st w' => cases st <;> simp [stepRooted, hs]

/-- The rooted interpreter preserves word admission — through the
delegation, `step_preserves_wf` does the work. -/
theorem stepRooted_preserves_wf {A} (p : Prog StoreSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (stepRooted H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl e) k =>
    have h := step_preserves_wf H (.vis e .pure) hw
    cases hs : step H (.vis e .pure) w with
    | mk st w' =>
      rw [hs] at h
      cases st <;> simpa [stepRooted, hs] using h
  | .vis (Sum.inr (.publish a)) k =>
    cases hf : Word.find w a <;> simp [stepRooted, hf, hw]
  | .vis (Sum.inr .listRoots) k => exact hw

/-- A successful publish's address has a binding in the word — the
fail-closed guard, read back. -/
theorem publish_mem {A} {a : Addr32} {k : Unit → Prog StoreSig A}
    {w : Word} {roots : List Addr32} {rest : Prog StoreSig A}
    {s' : RootedState}
    (h : stepRooted H (.vis (Sum.inr (.publish a)) k) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w := by
  cases hf : Word.find w a with
  | none => simp [stepRooted, hf] at h
  | some n => exact ⟨n, Word.find_mem hf⟩

/-- Iterated `stepRooted` with fuel, mirroring `run`. -/
def runRooted (fuel : Nat) (p : Prog StoreSig A) (s : RootedState) :
    Status StoreSig A × RootedState :=
  match fuel with
  | 0 => (.running p, s)
  | fuel + 1 =>
    match stepRooted H p s with
    | (.running rest, s') => runRooted fuel rest s'
    | halted => halted

end InterpRooted

end Cas.Lang
