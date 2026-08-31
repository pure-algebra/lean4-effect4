import Cas.Backend.Canon
import Cas.Core.Canonicalize
import Cas.Lang.Defun

/-
FORWARD SCOUT PROBE — `EC1-T007 normalizeRaw_alpha`.

Row (PROOF-DAG.md §3, line 199):
  `normalizeRaw_alpha : alphaEq r s -> normalizeRaw r = normalizeRaw s`
  PENDING THEOREM; depends on `D2`, `T006`.
  Local-anchor lane classed it SIMULATES / "No anchor".

`alphaEq` is NOT a proposed term. It occurs exactly twice in the whole packet
(`PROOF-DAG.md:199` and `:244`), both times inside a theorem row, and never in
any `PROPOSED TERM` block. `RawProgram` and `normalizeRaw` are `EC1-D020`/`D026`
and do not exist in Lean; `formal/effect-core-v1/EffectCore/Syntax/Raw.lean` is
an empty stub. So this probe carries the row's SHAPE, on the estate's own
objects, and asks what a proof attempt runs into. Nothing here is proposed for
the library and no packet name is introduced.

Five questions, five answers:

  §1  Can `alphaEq` be defined so the row is free?   YES — `Canonicalizer.Equiv`
                                                     makes the proof `fun h => h`.
  §2  Is the row vacuous at the estate's carrier?    YES — `PIn` is positional,
                                                     so the only equivalence is
                                                     `Eq` and the row is `congrArg`.
  §3  What is the row's real content?                Exactly renaming-STABILITY
                                                     of `normalizeRaw` — an
                                                     obligation with no DAG row.
  §4  Does `T006` (+ a BIJECTIVE renaming) give it?  NO — refuted at the estate's
                                                     only shipped keyed-table
                                                     normalizer.
  §5  So what must the row actually say?             §5, stated but not proved
                                                     (the carrier does not exist).

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T007.lean
```
-/

namespace ScoutT007

/-! ## §1 — the tautology trap

The estate already owns a canonicalizer whose induced equivalence is DEFINED as
equality of normal forms (`Cas/Core/Canonicalize.lean:81`,
`Canonicalizer.Equiv c a b := c.canon a = c.canon b`). If the packet spells
`alphaEq` that way — and `EC1-T007`'s stated dependency on `EC1-T006` is
evidence that a normal-form route is intended — the row's proof term is the
hypothesis itself. `PROOF-DAG.md` §3 already deleted two rows of exactly this
defect class; scout `EC1-T002` found the same trap at `rowEq`. -/

/-- **The trap, at the estate's object.** `EC1-T007` under a normal-form
definition of `alphaEq` is the identity function on its own hypothesis. -/
theorem alphaEq_as_canon_equiv_makes_the_row_free
    {α : Type} (c : Cas.Canonicalizer α) (r s : α) (h : c.Equiv r s) :
    c.canon r = c.canon s := h

/-- And it is an `Iff`, so no direction of it carries content either. -/
theorem alphaEq_as_canon_equiv_is_iff_rfl
    {α : Type} (c : Cas.Canonicalizer α) (r s : α) :
    c.Equiv r s ↔ c.canon r = c.canon s := Iff.rfl

/-! ## §2 — the vacuity trap, at the estate's real serializable carrier

The local-anchor lane reports "no anchor: the estate's serializable carrier has
positional operands, so alpha-equivalence is identity and the theorem never
arose". That is checked here rather than taken on trust: `PIn`
(`Cas/Lang/Defun.lean:167`) has exactly two constructors and neither carries a
name. There is no binder to rename, so the only available `alphaEq` at `PProg`
is `Eq`, and the row collapses to `congrArg`. -/

/-- The operand census: an operand is a literal address or a POSITION. No name
field exists, in either arm. -/
theorem pin_is_positional (i : Cas.Lang.PIn) :
    (∃ a : Cas.Addr32, i = .lit a) ∨ (∃ n : Nat, i = .ans n) := by
  cases i with
  | lit a => exact Or.inl ⟨a, rfl⟩
  | ans n => exact Or.inr ⟨n, rfl⟩

/-- Consequently, at any carrier whose only structural equivalence is `Eq`, the
row is `congrArg` for EVERY function — it says nothing about the normalizer. -/
theorem alpha_as_eq_is_congrArg {α β : Type} (norm : α → β) {r s : α}
    (h : r = s) : norm r = norm s := congrArg norm h

/-! ## §3 — the row's real content is renaming-stability

Read `alphaEq r s` the only non-degenerate way available: `s` is `r` with its
identifiers renamed, i.e. `∃ g, act g r = s` for a renaming action `act`. Then
the row is EQUIVALENT to a statement about `normalizeRaw` alone — that it is
constant on renaming orbits. That statement is not `EC1-T006`, is not implied by
`EC1-T006`, and has no row anywhere in `PROOF-DAG.md`. -/

/-- **`EC1-T007` is exactly renaming-stability.** Both directions, over an
arbitrary renaming action, so this is a claim about the row's shape and not
about any particular carrier. -/
theorem alpha_row_iff_renaming_stable
    {α σ : Type} (norm : α → α) (act : σ → α → α) :
    (∀ r s : α, (∃ g : σ, act g r = s) → norm r = norm s)
      ↔ (∀ (g : σ) (r : α), norm (act g r) = norm r) := by
  constructor
  · intro h g r
    exact (h r (act g r) ⟨g, rfl⟩).symm
  · intro h r s hrs
    obtain ⟨g, rfl⟩ := hrs
    exact (h g r).symm

/-! ## §4 — idempotence does not deliver stability, even for a BIJECTION

The row's stated dependencies are `D2` and `EC1-T006`. `EC1-T006` is
idempotence. The witness below is the estate's only shipped keyed-table
normalizer, `canonServices` (`Cas/Backend/EmitLayer.lean:220`), which satisfies
idempotence (`canonServices_idem`, `Cas/Backend/Canon.lean:297`) and every other
law of its ledger — and it is refuted by a renaming that is a BIJECTION on the
key namespace. So no premise strengthening `alphaEq` rescues the row: the
missing obligation is on `normalizeRaw`, not on `alphaEq`.

Scope, stated plainly: `ServiceRef.key` is a FREE name (a service key), not a
bound identifier. That is precisely the point. `EC1-A11`'s raw carrier holds
eight tables whose identifiers include registry keys, a `publicSurface` ledger
identity, and an `alphabetVersion` alongside internal `BlockId`/`CodeId`s, and
the packet nowhere declares which namespaces are BOUND. Until that split is
declared, `alphaEq` ranges over renamings that change meaning, and this witness
is one of them. -/

open Cas.Backend Cas.Schema

/-- A renaming of the key namespace. Not a packet term — the local spelling of
"apply a renaming to every identifier occurrence". -/
def renameKeys (σ : String → String) (xs : List ServiceRef) : List ServiceRef :=
  xs.map fun r => { r with key := σ r.key }

/-- The renaming: the transposition of the two keys used below. -/
def swapKey (k : String) : String :=
  if k = "a" then "b" else if k = "b" then "a" else k

/-- It is an involution, hence a bijection — this is a genuine alpha-style
renaming under any reading that requires one. -/
theorem swapKey_involutive (k : String) : swapKey (swapKey k) = k := by
  by_cases h1 : k = "a"
  · subst h1; rfl
  · by_cases h2 : k = "b"
    · subst h2; rfl
    · simp [swapKey, h1, h2]

theorem swapKey_injective : Function.Injective swapKey := by
  intro x y h
  rw [← swapKey_involutive x, h, swapKey_involutive]

/-- Witness, left. -/
def refA : ServiceRef := { key := "a", name := "A", path := "pa" }

/-- Witness, right. -/
def refB : ServiceRef := { key := "b", name := "B", path := "pb" }

def src : List ServiceRef := [refA, refB]

def tgt : List ServiceRef := renameKeys swapKey src

theorem tgt_spelled :
    tgt = [{ key := "b", name := "A", path := "pa" },
           { key := "a", name := "B", path := "pb" }] := by
  rfl

theorem src_nodup_keys : (src.map (·.key)).Nodup := by
  decide

theorem tgt_nodup_keys : (tgt.map (·.key)).Nodup := by
  rw [tgt_spelled]; decide

/-- `src` and `tgt` are not permutations of one another: the key/name pairing
moved, which is exactly what a renaming does and what a key-preserving
normalizer cannot undo. -/
theorem src_not_perm_tgt : ¬ src.Perm tgt := by
  intro h
  have hp := h.map (fun r => (r.key, r.name))
  have hmem : (("a", "A") : String × String) ∈ src.map (fun r => (r.key, r.name)) := by
    decide
  have hin := hp.mem_iff.mp hmem
  rw [tgt_spelled] at hin
  revert hin
  decide

/-- **The refutation.** A normalizer can satisfy `EC1-T006` (idempotence) — and
every other law in the shipped ledger — and still fail `EC1-T007` for a
BIJECTIVE renaming. Proved through `PRESERVE-exact`
(`canonServices_perm_of_nodup_keys`, `Cas/Backend/Canon.lean:288`), so no
`mergeSort` is computed. -/
theorem idempotence_does_not_give_alpha :
    canonServices src ≠ canonServices tgt := by
  intro heq
  refine src_not_perm_tgt ?_
  have p1 : (canonServices src).Perm src :=
    canonServices_perm_of_nodup_keys src_nodup_keys
  have p2 : (canonServices tgt).Perm tgt :=
    canonServices_perm_of_nodup_keys tgt_nodup_keys
  rw [heq] at p1
  exact p1.symm.trans p2

/-- The same fact packaged as the row's own shape: there is a normalizer
satisfying `EC1-T006` and a bijective renaming action under which the
`EC1-T007` implication is false. -/
theorem T006_does_not_imply_T007 :
    ∃ (norm : List ServiceRef → List ServiceRef)
      (act : (String → String) → List ServiceRef → List ServiceRef),
      (∀ xs, norm (norm xs) = norm xs) ∧
      ¬ (∀ (r s : List ServiceRef),
          (∃ σ, Function.Injective σ ∧ act σ r = s) → norm r = norm s) :=
  ⟨canonServices, renameKeys, canonServices_idem, fun h =>
    idempotence_does_not_give_alpha
      (h src tgt ⟨swapKey, swapKey_injective, rfl⟩)⟩

/-! ## §4b — the adequacy hole: `T006` + `T007` are satisfied by a normalizer
that throws the whole program away

`Cas/Backend/Canon.lean:199-215` makes this argument for `canonServices` in the
estate's own words — idempotence and order-blindness are jointly satisfied by a
canonicalizer that DISCARDS rows — and the estate closed the hole with three
PRESERVE laws (`mem_keys_canonServices` `:259`, `mem_of_mem_canonServices`
`:266`, `canonServices_last_wins` `:278`). `EC1-T006` and `EC1-T007` are exactly
"idempotence" and "order-blindness" one level up, and the foundation bundle has
no PRESERVE row for `normalizeRaw`. -/

/-- The constant normalizer satisfies `EC1-T006` and `EC1-T007` together, for
every renaming action. Neither row constrains what `normalizeRaw` keeps. -/
theorem T006_and_T007_hold_of_a_discarding_normalizer
    {α σ : Type} (c : α) (act : σ → α → α) :
    (∀ x : α, (fun _ => c) ((fun _ => c) x) = (fun _ => c) x) ∧
    (∀ r s : α, (∃ g : σ, act g r = s) →
      (fun _ => c) r = (fun _ => c) s) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-! ## §5 — what the row must say, and what it still owes

Not proved here; the carrier does not exist. Recorded so the obligation is
visible rather than discovered during implementation.

1. `alphaEq` must become a declared term with a BOUND/FREE split over
   `RawProgram`'s eight identifier namespaces. Renamings may move `BlockId`,
   `CodeId`, `RegionId`, region tokens and local pure/handler names; they may
   NOT move `alphabetVersion`, the `publicSurface` ledger identity, operation
   IDs, or `foreignTable` registry keys — those are keys into host code
   (`EFFECTS-BACKEND.md` R7) and renaming them is not meaning-preserving.
   §4 is a witness for what happens when the split is absent.
2. The renaming must be a bijection on each bound namespace, and
   capture-avoiding — `TYPE-CLOSURE.md:121` already names "alias capture" as a
   red control for this exact carrier row.
3. The row needs a duplicate-free / `ProgramWF` premise. `EC1-A11` says
   duplicate identifiers are DELIBERATELY representable in `RawProgram`, and
   `EC1-CE030` is the estate-verified statement that a last-wins keyed
   normalizer is not blind to reordering when keys repeat. That is the same
   defect one level up, so the premise `EC1-T002` was forced to carry is owed
   here too. (Inferred by transfer, not proved at `RawProgram`.)
3b. The bundle owes a PRESERVE row for `normalizeRaw` (§4b) and, by the same
   argument that made `EC1-T002` an IFF, a completeness half
   `normalizeRaw r = normalizeRaw s -> alphaEq r s` on admitted programs.
4. The load-bearing lemma is renaming-stability, by §3 — `normalizeRaw` must
   canonically RENUMBER the bound namespaces, which no declared obligation
   states. `EC1-T006` is idempotence and, by §4, does not reach it.
5. Two consequences the packet has not costed: a canonical renumbering is
   driven by reachability from `entry`, so unreachable blocks have no canonical
   position (either a WF premise excludes them or `normalizeRaw` drops them,
   and dropping them collides with `EC1-T013 check_erase`); and `RawProgram`
   carries a `presentation` source-span map keyed by the identifiers a renaming
   moves, so `normalizeRaw` must normalize or erase it, which `EC1-T013` also
   feels. (Inferred from `ALGEBRA.md` §4.1, not proved.) -/

end ScoutT007

/-! ## Kernel receipts

`Classical.choice` appears on `idempotence_does_not_give_alpha` and
`T006_does_not_imply_T007` only. It is INHERITED, not introduced: both estate
lemmas they call already carry it —
`#print axioms Cas.Backend.canonServices_perm_of_nodup_keys` and
`#print axioms Cas.Backend.canonServices_idem` both report
`[propext, Classical.choice, Quot.sound]`, from `List.mergeSort`'s well-founded
recursion. `EC1-CE030` records the same three for the same family. No
`sorry`, no `axiom`, no `native_decide`, no `#eval`. -/

#print axioms ScoutT007.alphaEq_as_canon_equiv_makes_the_row_free
#print axioms ScoutT007.alphaEq_as_canon_equiv_is_iff_rfl
#print axioms ScoutT007.pin_is_positional
#print axioms ScoutT007.alpha_as_eq_is_congrArg
#print axioms ScoutT007.alpha_row_iff_renaming_stable
#print axioms ScoutT007.swapKey_involutive
#print axioms ScoutT007.swapKey_injective
#print axioms ScoutT007.tgt_spelled
#print axioms ScoutT007.src_nodup_keys
#print axioms ScoutT007.tgt_nodup_keys
#print axioms ScoutT007.src_not_perm_tgt
#print axioms ScoutT007.idempotence_does_not_give_alpha
#print axioms ScoutT007.T006_does_not_imply_T007
#print axioms ScoutT007.T006_and_T007_hold_of_a_discarding_normalizer
