import Cas.Lang.Tower

/-!
# Representation — what may be equated, and at which stratum

The stable effects API to reason over (EFFECTS-BACKEND R14). Effectful
computation has FOUR literal representations in Lean, and each carries
its own equality:

1. **First-order content** — signatures' operations, nodes, words,
   schema codes, and (at F3) defunctionalized program tables. Equality
   is `DecidableEq` — structural, hashable, addressable. THIS is the
   metaprogrammatic stratum: what generators, gates, and the store
   reason over. Canonical spelling makes structural equality coincide
   with byte equality (the rendering theorems).
2. **`Prog S A`** — the higher-order proof carrier: pure data whose
   continuations are functions. Equality is propositional and needs
   `funext`; invisible to hashing, ideal for induction. The theorems
   below make it SAFE to treat as pure: it is a lawful monad, and it
   is initial — agreement under every interpretation IS equality.
3. **Handler images** — `interpret h p` in a target monad. Semantic
   values; equated only by theorem (`SemEq`, `ObsEq`), never identity.
   Per R5, cross-host agreement is observed at the word.
4. **Host `IO`** — the admitted seams. No equational theory at all;
   reasoning stops at the trust statement.

"What we can equate to pure": strata 1 and 2 are pure by construction —
1 decidably, 2 propositionally. The monad laws (`LawfulMonad`) license
every metaprogrammatic rewrite a normalizer needs; `interpret_id` and
`eq_of_forall_interpret` license replacing "same under all semantics"
by plain equality. Stratum 3 equations are certificates; stratum 4 has
none.
-/

namespace Cas.Lang

/-! ## `Prog` is a lawful monad — the equational core of the API -/

theorem Prog.bind_pure_right (p : Prog S A) : p.bind .pure = p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    simp only [Prog.bind]
    exact congrArg (Prog.vis op) (funext fun a => ih a)

theorem Prog.bind_assoc' (p : Prog S A) (f : A → Prog S B) (g : B → Prog S C) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    simp only [Prog.bind]
    exact congrArg (Prog.vis op) (funext fun a => ih a)

instance : LawfulMonad (Prog S) :=
  LawfulMonad.mk'
    (id_map := fun p => Prog.bind_pure_right p)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun p f g => Prog.bind_assoc' p f g)

/-! ## Initiality — syntax is the universal semantics -/

/-- The syntactic identity handler: every operation means itself. -/
def idHandler : Handler S (Prog S) where
  handle op := .vis op .pure

/-- Interpreting through the identity handler is the identity — the
syntax interprets itself faithfully. -/
theorem interpret_id (p : Prog S A) : interpret idHandler p = p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    show Prog.bind (.vis op .pure) _ = _
    simp only [Prog.bind]
    exact congrArg (Prog.vis op) (funext fun a => ih a)

/-- Initiality: programs agreeing under EVERY lawful interpretation
are equal. This is the license to treat `Prog` as pure data in proofs:
"same meaning everywhere" collapses to structural identity, so no
finer program equality exists to account for. -/
theorem eq_of_forall_interpret {p q : Prog S A}
    (h : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
      (hd : Handler S M), interpret hd p = interpret hd q) : p = q := by
  have := h (Prog S) idHandler
  rwa [interpret_id, interpret_id] at this

/-! ## The pure discipline (R14a) — what keeps proofs wieldy

`pure` is the effect boundary, and the discipline has three rules:

- **P1 — everything effect-free stays OUTSIDE `Prog`.** A function
  that performs no operation is a plain Lean definition on
  first-order data, with ordinary `simp`/`rfl` reasoning — never
  lifted into the program type. Computation between operations
  happens in Lean and enters through `pure`/`let`. Programs carry
  the minimum `vis` nodes; every induction is exactly as long as the
  operation tree, so short trees are short proofs.
- **P2 — continuations end in `.pure`; programs are authored as
  smart constructors composed by `bind`.** The proved monad laws
  then normalize any program, lemmas are stated against the
  constructors, and the leaf case of every induction closes by
  `interpret_pure` (rfl) while each operation closes by
  `interpret_op`.
- **P3 — constructor form in statements, typeclass form in program
  text.** `.pure a` and `pure a` are definitionally equal; the
  constructor keeps patterns structural and `rfl`-friendly, the
  typeclass keeps programs readable and generic. -/

/-- The leaf law: interpreting a finished program is `pure` — by
definition, so every induction's base case is `rfl`. -/
theorem interpret_pure [Monad M] (h : Handler S M) (a : A) :
    interpret h (.pure a) = pure a := rfl

/-- The operation law: interpreting a single operation IS the
handler's meaning for it — the one-step case of every proof. -/
theorem interpret_op [Monad M] [LawfulMonad M] (h : Handler S M)
    (e : S.Op) : interpret h (Prog.op e) = h.handle e := by
  simp [Prog.op, interpret]

/-! ## The semantic equalities — stratum 3, always by theorem -/

/-- Equality under one chosen semantics. -/
def SemEq [Monad M] (h : Handler S M) (p q : Prog S A) : Prop :=
  interpret h p = interpret h q

/-- Structural equality is semantic equality everywhere — the trivial
direction, stated so rewriting may cross the boundary. -/
theorem SemEq.of_eq [Monad M] (h : Handler S M) {p q : Prog S A}
    (hpq : p = q) : SemEq h p q := by rw [SemEq, hpq]

/-- Observational equality for the store language: the same outcome
and the same WORD from every starting word — the estate's chosen
observation (R5), the equality the cross-host run gate decides
per-program. -/
def ObsEq (H : Bytes → Addr32) (p q : Prog CasSig A) : Prop :=
  ∀ w, interpretRef H p w = interpretRef H q w

theorem ObsEq.of_eq (H : Bytes → Addr32) {p q : Prog CasSig A}
    (hpq : p = q) : ObsEq H p q := fun w => by rw [hpq]

/-! ### `ObsEq` decided by the run — the R5 gate and stratum 3 are one

`ObsEq` is stated over `interpretRef`, but nothing in the estate
executes `interpretRef`: the gates run `run` (and, on the
defunctionalized fragment, `runP`). The bridge (`Handler.lean`,
`run_interpretRef_agree`) is what closes that gap, and these three
corollaries are the closure — the licence to read a run-gate verdict as
a stratum-3 equality, and the exact statement of what the gate can and
cannot see.

The asymmetry the bridge's triage found survives here, and is the point
of the third statement: `ObsEq` transfers a `done` outcome with its
word, but a `refused` outcome with only its refusal. Two observationally
equal programs may leave DIFFERENT partial words when they refuse, and
`ObsEq` — being an equation in `Except Refusal (A × Word)` — cannot
say otherwise. A gate that compared refusal words would be deciding
something strictly finer than the estate's chosen observation. -/

/-- The run gate decides `ObsEq`: if for every starting word the two
programs have halted runs that agree — same status, same word, at
whatever fuel each needs — the programs are observationally equal. This
is the direction the gate uses. -/
theorem ObsEq.of_run (H : Bytes → Addr32) {p q : Prog CasSig A}
    (h : ∀ w : Word, ∃ fp fq : Nat,
      run H fp p w = run H fq q w ∧ (run H fp p w).1.isRunning = false) :
    ObsEq H p q := by
  intro w
  obtain ⟨fp, fq, heq, hhalt⟩ := h w
  cases hp : run H fp p w with
  | mk st w' =>
    have hq : run H fq q w = (st, w') := by rw [← heq, hp]
    rw [hp] at hhalt
    cases st with
    | done a =>
      rw [interpretRef_of_run_done H fp hp, interpretRef_of_run_done H fq hq]
    | refused r =>
      rw [interpretRef_of_run_refused H fp hp,
        interpretRef_of_run_refused H fq hq]
    | running rest => simp [Status.isRunning] at hhalt

/-- What `ObsEq` gives back on success: the whole outcome, value and
word, realized at some fuel on the other program. -/
theorem ObsEq.run_done (H : Bytes → Addr32) {p q : Prog CasSig A}
    (h : ObsEq H p q) {fuel : Nat} {w w' : Word} {a : A}
    (hp : run H fuel p w = (.done a, w')) :
    ∃ g, run H g q w = (.done a, w') := by
  obtain ⟨g, hg⟩ := run_of_interpretRef H q w
  refine ⟨g, ?_⟩
  have hi : interpretRef H q w = .ok (a, w') := by
    rw [← h w]; exact interpretRef_of_run_done H fuel hp
  have := hg g (Nat.le_refl g)
  rw [hi] at this
  exact this

/-- What `ObsEq` gives back on refusal, and no more: the refusal, at
some fuel, leaving SOME word. The partial words the two runs leave are
unconstrained — `interpretRef`'s error branch does not carry a word, so
this is the whole of what the observation says. -/
theorem ObsEq.run_refused (H : Bytes → Addr32) {p q : Prog CasSig A}
    (h : ObsEq H p q) {fuel : Nat} {w w' : Word} {r : Refusal}
    (hp : run H fuel p w = (.refused r, w')) :
    ∃ g w'', run H g q w = (.refused r, w'') := by
  obtain ⟨g, hg⟩ := run_of_interpretRef H q w
  have hi : interpretRef H q w = .error r := by
    rw [← h w]; exact interpretRef_of_run_refused H fuel hp
  have := hg g (Nat.le_refl g)
  rw [hi] at this
  obtain ⟨w'', hw''⟩ := this
  exact ⟨g, w'', hw''⟩

end Cas.Lang
