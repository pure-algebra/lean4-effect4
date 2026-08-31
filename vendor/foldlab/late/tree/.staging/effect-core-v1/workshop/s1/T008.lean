import Cas.Lift.Taxonomy

/-!
# Effect Core v1 — `EC1-T008` (`surface_disposition_total`), implemented

Slice `EC1-S1`. Skill stage: **`lean-model-invariants`** — the row is about a
generated ledger's representation, its coverage/duplicate-free/exclusion
invariants, the checked boundary that decides them, and the total function that
boundary buys. It is not about sequencing, protocol state, or interpreters, so
`lean-algebraic-systems` is not the stage.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T008.lean
```

Nothing here is proposed for `library/` or for `formal/effect-core-v1/`. This
file is outside every lake target, exactly like `../exhibits.lean`,
`../counterexamples/Nondeterminism.lean` and `../../breaker-exhibits.lean`. It
adds nothing to `Cas`, moves no byte and promotes no name. `Cas.Lift.Taxonomy`
is imported read-only, to instantiate §10's closed-enum gate at the estate's own
shipped twenty-row enum rather than assert that the shape transfers.

## Outcome

The DAG's schematic row (`PROOF-DAG.md:200`)

    surface_disposition_total :
      PublicSurfaceWF s -> forall row in s, exists! d, disposition row = d

is **restated**, and the restatement is proved **strictly stronger**: §12 proves
the restatement implies the schematic row, and §3/§6 exhibit ledgers satisfying
the schematic row that the restatement rejects.

Three defects force the restatement, each with a kernel behind it here.

* **§1 — the row is fully vacuous.** `∃! d, f x = d` holds for every function
  into every type. Both stated premises are discharged with the hypothesis
  visibly unused, axiom-free. It is strictly emptier than the sibling
  `EC1-T004`, whose `Option` codomain at least leaves an `isSome` residue. This
  is the family `PROOF-DAG.md:207` already deleted twice.
* **§3 — the row's own falsifier is unstateable against it.** `EC1-F60`
  (`CONTRACT-PACKET.md:741`) is *drop or duplicate a public row's seven-way
  disposition*, and drop and duplicate are exactly the two mutations a total
  Lean function cannot exhibit. Both mutants are built and the schematic row is
  proved **TRUE of each**, along with a third that violates `EC1-K07`'s
  `excludedInternal` clause outright.
* **§10 — the row cannot express "seven-value enum".** §1's proof is
  indifferent to the codomain, so the row holds verbatim of a disposition map
  into `Option SurfaceDisposition`, whose `none` **is** the null disposition
  `REIFICATION-CHECKLIST.md:488` forbids in a closed ledger.

## What is new here, beyond the scout

The scout (`scout-T008.lean`) recommended an existence-plus-agreement theorem
under a three-clause `PublicSurfaceWF`. That is proved here as
`surface_disposition_exact` (§5) with both premises shown load-bearing (§6). It
is **not adequate on its own**, and three further sections say why:

* **§8 — a theorem under `PublicSurfaceWF s` cannot turn red.** `EC1-F60`
  mutates the *generated ledger*. On a mutated ledger the hypothesis is simply
  undischargeable, so §5 goes quiet rather than false, and nothing fails. What
  makes `EC1-F60` fire is a **decider**: `checkSurface`, with a two-sided
  `checkSurface s = .ok () ↔ PublicSurfaceWF s`, an accurate first diagnostic,
  and proofs that each `EC1-F60` mutant is rejected by name. This is the
  estate's own shape (`Cas/Core/Admission.lean:60 checkRefs_ok_iff`,
  `Cas/Schema/Guarded.lean:421`), and the `lean-model-invariants`
  wire → validate → checked-core boundary.
* **§7 — the word "total" becomes true with content only on the checked
  carrier.** `CheckedSurface.dispositionAt` is a **total function** from the
  public key universe into the six-value non-excluded disposition set, agreeing
  with the ledger. That is what `surface_disposition_total` should have named;
  on the raw carrier no such function exists, and §6 proves it.
* **§11 — `PublicSurfaceWF` says nothing about census completeness.** A ledger
  that simply omits the deep `MultipartParser` module from `keys` is fully
  well-formed. So `EC1-CE020` (`VERIFIED-TOOL`) attacks a clause that is not in
  this row at all, `EC1-F59` and `EC1-F60` are independent, and the census
  obligation must be stated separately — which §11 does, and then proves what
  the pair buys jointly.

§9 keeps the checker inside ruling **R16**: it reports the first condemning
clause only, and a two-defect ledger is exhibited on which it names one. No
diagnostic-completeness claim is made anywhere in this file.

## Receipts

**63 theorems, 63 `#print axioms` lines** in the block at the foot — one per
theorem, checked by name against the declaration list. `lake env lean` exits 0
with no errors and no warnings. Ceiling `[propext, Quot.sound]`; `Quot.sound`
enters only through `List` `simp` normalization inside the `Nodup` induction and
the `find?` case splits, and `propext` through `decide` on `∈`.

**22 are axiom-free**, including every one of the vacuity findings
(`bang_is_free`, `T008_as_written_ignores_both_premises`,
`T008_needs_no_surface`, all four `T008_holds_*` mutant theorems,
`T008_holds_of_every_total_disposition`,
`T008_holds_with_a_null_disposition_arm`,
`restatement_implies_the_schematic_row`) — which is itself the point: they need
nothing at all.

No `sorryAx`, no `Classical.choice`, no `axiom`, no `sorry`, no `native_decide`,
and no `#eval` carrying a claim.

## Anchors re-verified this pass (not taken from the scout)

`Cas/Schema/Declarations.lean:202` `DeclarationId.all_complete`, `:207` the
elaboration-time `#guard` on wire `Nodup`, `:276` `General.all_complete`, `:281`
`General.row_not_dedicated`, `:288` `General.row_surjective`, `:297`
`General.row_inj`; `Cas/Lift/Taxonomy.lean:215` `RefusalCode.all_complete`,
`:220` the `#guard`, and the module docstring at `:12-16`;
`Cas/Lang/RefusalMap.lean:120`, `:192`, and the HAND MIRROR caveat at
`:172-176`. All resolve at the cited lines, read rather than grepped for.

Two line/count defects in `.staging/agent-reports/2026-08-31-effect-core-local-anchors.md`
are confirmed independently: `:718` calls `Declarations.lean` a *seven-row
registry* when `DeclarationId` has **four** rows of which `General` spells
**three**; and `:769` cites `RefusalMap.lean:181` for the HAND MIRROR caveat,
which is at `:172-176` (`:181` is the constructor `| danglingReference`).
Neither defect invalidates its anchor, and that report's classification of
`EC1-T008` as vacuous is correct.

## Scope — what a green check here does and does not establish

It establishes the stated propositions about the carriers defined below, and
nothing else. §4-§9 are proved **generically** over any key universe with
decidable equality, so they are statements about ledgers rather than about the
scratch three-key model; §3, §6, §9 and §11's witnesses live at the scratch
model, where their only job is to refute universals.

It is **not** evidence that any generated `rc.112` ledger exists, is complete,
or satisfies `PublicSurfaceWF`. No such ledger is in the tree in any
Lean-consumable form: `EC1-H11` is `PENDING HARNESS`, and `covers`/`keysNodup`
are facts about generated data that only that harness can supply. `EC1-CE020`
is the live `VERIFIED-TOOL` counterexample to the completeness of the census
that would supply `s.keys`, and §11 proves this row cannot see it.

## Checks omitted, stated

* I did not run the TypeScript surface probe, and made no host-side claim.
* I did not attempt `covers`/`keysNodup` against real generated rows; there are
  none.
* I did not model the rest of `REIFICATION-CHECKLIST.md:540-600`'s ledger row —
  no `admissionProfiles`, `familyRoles`, `effectReachability`, `A/E/R`, or
  `primaryCarrierId`. `EC1-T009` owns the profile half and this file does not
  touch it.
* I did not verify `EC1-CE031`'s own witness by re-running `LocalAnchors.lean`;
  §9 transplants its lesson with a fresh witness at this carrier instead of
  citing it.
* The `SurfaceRowKey` universe here is a three-value scratch enum. The real one
  is thousands of rows, and its `Nodup`/coverage facts are `EC1-H11`'s to
  discharge, not this file's.
-/

namespace EffectCoreT008

/-! ## §0 — carriers

`EC1-D006`-`EC1-D009`, minimal and first-order. Nothing is minted that the
estate already owns: `List.Nodup`, `List.find?`, `Option`, `Except` and
`Subtype` are core, and no `Sig`, `Prog`, `Handler`, `PProg`, `Refusal`,
`Status`, `wp`, `wlp`, `Envelope` or `Word` is touched — correct per
`EFFECTS-BACKEND` R14a P1, since this is effect-free work on first-order data
and stays outside `Prog`. -/

/-- `EC1-D008`. The seven-way source-to-model disposition, transcribed verbatim
from `CONTRACT-PACKET.md:212-215` (`EC1-K07`) and tabulated at
`REIFICATION-CHECKLIST.md:494-502`. -/
inductive SurfaceDisposition where
  | reifiedPrimitive
  | derivedExpansion
  | separateSubcalculus
  | pureOrHostOnlyClosedOutsideProg
  | projectOwnedReplacementOrForeignOp
  | targetOnly
  | excludedInternal
  deriving DecidableEq, Repr

/-- One generated ledger row. `REIFICATION-CHECKLIST.md:564` makes
`surfaceDisposition` a required FIELD of `SurfaceRow`, so the disposition is a
projection out of ledger data, never a standalone Lean function — which is
exactly the difference §1 and §3 turn on. -/
structure SurfaceRow (κ : Type) where
  rowKey : κ
  surfaceDisposition : SurfaceDisposition
  deriving DecidableEq, Repr

/-- `EC1-D006`. The recursively resolved public key universe `U_row`, and the
generated disposition ledger over it. The two are SEPARATE fields: the source
hoover owns the first and Lean consumes the second (`PROOF-DAG.md:91`).
Collapsing them is what makes the schematic row vacuous. -/
structure PublicSurface (κ : Type) where
  keys : List κ
  rows : List (SurfaceRow κ)
  deriving DecidableEq, Repr

/-- The lookup the row's `disposition row` presumes once the ledger is data. It
is `Option`-valued for the reason `EC1-CE033`'s repair gives one level up: the
raw carrier deliberately admits keys the ledger does not classify. -/
def PublicSurface.dispositionOf {κ : Type} [DecidableEq κ]
    (s : PublicSurface κ) (k : κ) : Option SurfaceDisposition :=
  (s.rows.find? (fun r => decide (r.rowKey = k))).map (·.surfaceDisposition)

/-- `EC1-D007`, scratch. `multipartHeaders` is the deep
`effect/unstable/http/MultipartParser/HeadersParser` module that `EC1-CE020`
proved absent from the old 359-module bank and that `EC1-F59` requires present;
it is the concretely droppable key throughout. -/
inductive RowKey where
  | succeed
  | failCause
  | multipartHeaders
  deriving DecidableEq, Repr

/-! ## §1 — the schematic row is vacuous, with no residue at all

`PROOF-DAG.md:206-208` already deleted `exists! v, evalPure e env = v` and the
same-input function-equality forms as "tautologies for any Lean function".
`EC1-T008` is that deleted form. `EC1-T004` escaped the same deletion only
because `lookup` is `Option`-valued and `some` can be `none`; `disposition` is
not, so `EC1-T008` has no escape at all. -/

/-- The DAG's `exists! d, v = d`, spelled out. §2 records why it must be. -/
def UniqueEq {δ : Type} (v : δ) : Prop :=
  ∃ d, v = d ∧ ∀ e, v = e → e = d

/-- **Finding 1.** `exists! d, f x = d` holds for EVERY function into EVERY
type. No hypothesis, no `Option`, no ledger, no surface, no axiom. -/
theorem bang_is_free {α δ : Type} (f : α → δ) (x : α) : UniqueEq (f x) :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- **`EC1-T008` as written, with both stated premises visibly discarded.** The
underscore is the finding: `PublicSurfaceWF s` does no work, and `row ∈ s` is
consumed only to name a row that the conclusion then ignores. -/
theorem T008_as_written_ignores_both_premises {κ : Type}
    (_wf : True) (s : PublicSurface κ) :
    ∀ r ∈ s.rows, UniqueEq r.surfaceDisposition :=
  fun r _ => bang_is_free SurfaceRow.surfaceDisposition r

/-- The row does not even need a `PublicSurface` to be about: any list of any
records with any field satisfies it. -/
theorem T008_needs_no_surface {α δ : Type} (g : α → δ) (l : List α) :
    ∀ x ∈ l, UniqueEq (g x) :=
  fun x _ => bang_is_free g x

/-! ## §2 — the connective is not available in this environment

Re-verified this pass: `library/cas` pins `leanprover/lean4:v4.33.1` with an
EMPTY `.lake/packages` (`lake-manifest.json` reads `"packages": []`); there is
no Mathlib. `#check @ExistsUnique` reports *Unknown identifier* and `∃!` fails
to parse. `grep -rn 'ExistsUnique\|∃!' library/cas/Cas` is empty: the estate has
never used the connective.

Every DAG row spelled `exists!` — `EC1-T004` (`:193`), **`EC1-T008`** (`:200`),
`EC1-T016` (`:225`), `EC1-T035` (`:288`) — therefore owes either a definition or
an explicit spelling before it can be stated at all. `UniqueEq` is that
spelling, and it is the one the estate's own prototype
(`../EffectCoreProbe.lean:331`) independently reached. -/

/-- Nothing in §1 is an artifact of how `∃!` was spelled: the unfolding is the
definition. -/
theorem UniqueEq_is_the_unfolding {δ : Type} (v : δ) :
    UniqueEq v ↔ ∃ d, v = d ∧ ∀ e, v = e → e = d :=
  Iff.rfl

/-! ## §3 — `EC1-F60` is unstateable against the row

`CONTRACT-PACKET.md:741` reads:

> `EC1-F60` | Drop or duplicate a public row's seven-way disposition. |
> Disposition totality/uniqueness fails while proof status remains irrelevant.

A reader takes `surface_disposition_total` to be the theorem this falsifier
turns red. It is not, and it cannot be: the falsifier mutates the generated
LEDGER, while the row quantifies over a total FUNCTION, which is single-valued
by construction and defined everywhere by typing. Both mutants are built here
and the row is proved TRUE of each.

`Cas/Lift/Taxonomy.lean:12-16` says this in the estate's own voice, and also
says where the content went: totality "is by construction — it is a function on
an inductive, not a partial map — which is precisely the statement the mirrored
TypeScript `Record` cannot make for itself." The thing that can drop or
duplicate is the generated ledger on the far side of the mirror. -/

/-- **`EC1-F60`, mutation one: DROP.** `multipartHeaders` is in the public key
universe and has no ledger row. -/
def droppedSurface : PublicSurface RowKey where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.failCause, .reifiedPrimitive⟩]

/-- The mutant really is the forbidden one: a public key with no disposition. -/
theorem droppedSurface_really_drops :
    RowKey.multipartHeaders ∈ droppedSurface.keys
      ∧ droppedSurface.dispositionOf .multipartHeaders = none := by
  decide

/-- **`EC1-F60`, mutation two: DUPLICATE.** One key, two ledger rows, two
DIFFERENT dispositions. `EC1-K07` (`CONTRACT-PACKET.md:227-228`) names multiply
classified rows as not permitted. -/
def dupSurface : PublicSurface RowKey where
  keys := [.succeed]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.succeed, .targetOnly⟩]

/-- The mutant really is the forbidden one: the key is multiply classified. -/
theorem dupSurface_really_duplicates :
    (⟨.succeed, .reifiedPrimitive⟩ : SurfaceRow RowKey) ∈ dupSurface.rows
      ∧ (⟨.succeed, .targetOnly⟩ : SurfaceRow RowKey) ∈ dupSurface.rows
      ∧ (SurfaceDisposition.reifiedPrimitive ≠ .targetOnly) := by
  decide

/-- The ledger search silently keeps the first row and discards the second.
This is `EC1-CE030`'s "a permutation with duplicate keys selects different last
values" (`COUNTEREXAMPLES.md:94`) at the surface carrier — here it is the FIRST
value that wins, because the search is `find?` rather than a last-wins dedup,
but the defect is the same: a duplicate key silently loses information. -/
theorem dupSurface_lookup_picks_the_first :
    dupSurface.dispositionOf .succeed = some .reifiedPrimitive := by
  decide

/-- **`EC1-K07` mutation.** A ledger that classifies a PUBLIC key as
`excludedInternal` — the one value `CONTRACT-PACKET.md:224` forbids outright and
`REIFICATION-CHECKLIST.md:502` calls "invalid for a key in `U_row`". -/
def excludedSurface : PublicSurface RowKey where
  keys := [.succeed]
  rows := [⟨.succeed, .excludedInternal⟩]

/-- **Finding 3a.** The schematic row is TRUE of the DROP mutant. The dropped
key is not a `row in s`, so the statement's own quantifier never reaches it. -/
theorem T008_holds_on_the_drop_mutant :
    ∀ r ∈ droppedSurface.rows, UniqueEq r.surfaceDisposition :=
  fun r _ => bang_is_free SurfaceRow.surfaceDisposition r

/-- **Finding 3b.** The schematic row is TRUE of the DUPLICATE mutant. The `∃!`
sits on the FIELD, which is single-valued by construction, not on the
ASSIGNMENT of dispositions to keys, which is not. -/
theorem T008_holds_on_the_duplicate_mutant :
    ∀ r ∈ dupSurface.rows, UniqueEq r.surfaceDisposition :=
  fun r _ => bang_is_free SurfaceRow.surfaceDisposition r

/-- **Finding 3c.** The schematic row is TRUE of the `EC1-K07` mutant too, so it
carries no exclusion clause either. -/
theorem T008_holds_on_the_excludedInternal_mutant :
    ∀ r ∈ excludedSurface.rows, UniqueEq r.surfaceDisposition :=
  fun r _ => bang_is_free SurfaceRow.surfaceDisposition r

/-- **Finding 3d, the sharp form.** No total-function reading rescues the row.
For a `disposition : κ → SurfaceDisposition` the row holds of EVERY such
function, including the one that answers `excludedInternal` for every public key
— the single assignment `EC1-K07` forbids outright. Neither `EC1-F60` mutation
can even be exhibited at that carrier, so the falsifier has no target. -/
theorem T008_holds_of_every_total_disposition {κ : Type}
    (disposition : κ → SurfaceDisposition) (k : κ) :
    UniqueEq (disposition k) :=
  bang_is_free disposition k

/-- **Finding 3e.** The row cannot see a NULL disposition either. Replace the
codomain by `Option SurfaceDisposition` — whose `none` IS the null disposition
`REIFICATION-CHECKLIST.md:488` forbids in a closed ledger — and §1's proof is
unchanged. Nothing is minted: `Option` is core. -/
theorem T008_holds_with_a_null_disposition_arm {κ : Type}
    (nullable : κ → Option SurfaceDisposition) (k : κ) :
    UniqueEq (nullable k) :=
  bang_is_free nullable k

/-! ## §4 — `EC1-D009` `PublicSurfaceWF`, and its decidability

Each clause is named by the mutation it excludes, and §6 proves each one
load-bearing. The shapes are the estate's, at
`Cas/Schema/Declarations.lean:288` (`General.row_surjective` — "a new row that
forgets its disposition fails to build"), `:297` (`General.row_inj` — one id per
registry row) and `:281` (`General.row_not_dedicated`). The difference — and the
whole finding of this file — is that the estate states them at a FUNCTION on a
closed inductive, where they are `rfl` or `decide`, while a generated ledger is
DATA, where they are contentful and can fail. -/

section Ledger

variable {κ : Type} [DecidableEq κ]

/-- `EC1-D009`. -/
structure PublicSurfaceWF (s : PublicSurface κ) : Prop where
  /-- Nothing is dropped: every public key is classified. Excludes
  `droppedSurface`; this is `EC1-F60`'s drop half. -/
  covers : ∀ k ∈ s.keys, ∃ r ∈ s.rows, r.rowKey = k
  /-- Nothing is multiply classified. Excludes `dupSurface`; this is
  `EC1-F60`'s duplicate half, and `EC1-CE030`'s forced repair
  (`COUNTEREXAMPLES.md:94`, ruling **R16** part 2) at this carrier. -/
  keysNodup : (s.rows.map (·.rowKey)).Nodup
  /-- `EC1-K07`: "No public exposure may be `excludedInternal`". Excludes
  `excludedSurface`. -/
  publicNotExcluded :
    ∀ r ∈ s.rows, r.rowKey ∈ s.keys → r.surfaceDisposition ≠ .excludedInternal

/-- Every clause is decidable, so `PublicSurfaceWF` is a checkable property of
generated data rather than an assumption. §8 turns this into a diagnostic. -/
instance (s : PublicSurface κ) : Decidable (PublicSurfaceWF s) :=
  decidable_of_iff
    ((∀ k ∈ s.keys, ∃ r ∈ s.rows, r.rowKey = k)
      ∧ (s.rows.map (·.rowKey)).Nodup
      ∧ (∀ r ∈ s.rows, r.rowKey ∈ s.keys →
          r.surfaceDisposition ≠ .excludedInternal))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
     fun h => ⟨h.covers, h.keysNodup, h.publicNotExcluded⟩⟩

/-! ## §5 — the statement that has content

Two repairs are forced together, one by each `EC1-F60` mutant:

* quantify over the KEY UNIVERSE and the LEDGER, not over a function's result
  (forced by the DROP mutant); and
* carry a duplicate-free premise on ledger keys, exactly as `EC1-T002` carries
  one (`PROOF-DAG.md:210`) for the same reason (forced by the DUPLICATE
  mutant).

The result is an agreement theorem between the universe, the ledger, and the
search — the real obligation hiding behind the word "total". -/

/-- Distinct entries cannot share a key when the keys are duplicate-free. -/
theorem nodup_key_unique {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α},
      x ∈ l → y ∈ l → f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x y hx _ _; simp at hx
  | cons a t ih =>
    intro hnd x y hx hy h
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨y, hy', h.symm⟩) hnot
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (List.mem_map.mpr ⟨x, hx', h⟩) hnot
      · exact ih hnd' hx' hy' h

/-- A key with no ledger row is not found. Used both ways: it is the search's
half of `covers`, and §8's accuracy proof for the `unclassified` diagnostic. -/
theorem dispositionOf_eq_none (s : PublicSurface κ) {k : κ}
    (h : ∀ r ∈ s.rows, r.rowKey ≠ k) : s.dispositionOf k = none := by
  show ((s.rows.find? (fun r => decide (r.rowKey = k))).map
    (·.surfaceDisposition)) = none
  rw [List.find?_eq_none.mpr (fun r hr hd => h r hr (of_decide_eq_true hd))]
  rfl

/-- **The existence that is not free.** A classified key is found by the search.
FALSE on `droppedSurface`. -/
theorem dispositionOf_isSome (s : PublicSurface κ) {k : κ} {r : SurfaceRow κ}
    (hr : r ∈ s.rows) (hk : r.rowKey = k) :
    (s.dispositionOf k).isSome = true := by
  show ((s.rows.find? (fun x => decide (x.rowKey = k))).map
    (·.surfaceDisposition)).isSome = true
  rcases hl : s.rows.find? (fun x : SurfaceRow κ => decide (x.rowKey = k)) with
    _ | e
  · exact absurd (decide_eq_true hk) (List.find?_eq_none.mp hl r hr)
  · rfl

omit [DecidableEq κ] in
/-- **The uniqueness that is not free.** Under `keysNodup`, every ledger row for
one key carries the same disposition. FALSE on `dupSurface`. -/
theorem disposition_agrees_across_rows (s : PublicSurface κ)
    (h : PublicSurfaceWF s) {k : κ} {r r' : SurfaceRow κ}
    (hr : r ∈ s.rows) (hrk : r.rowKey = k)
    (hr' : r' ∈ s.rows) (hrk' : r'.rowKey = k) :
    r.surfaceDisposition = r'.surfaceDisposition := by
  rw [nodup_key_unique (·.rowKey) h.keysNodup hr hr' (hrk.trans hrk'.symm)]

/-- The search agrees with the ledger. -/
theorem dispositionOf_agrees (s : PublicSurface κ) (h : PublicSurfaceWF s)
    {k : κ} {r : SurfaceRow κ} (hr : r ∈ s.rows) (hrk : r.rowKey = k) :
    s.dispositionOf k = some r.surfaceDisposition := by
  show (s.rows.find? (fun x => decide (x.rowKey = k))).map
    (·.surfaceDisposition) = some r.surfaceDisposition
  rcases hl : s.rows.find? (fun x : SurfaceRow κ => decide (x.rowKey = k)) with
    _ | e
  · exact absurd (decide_eq_true hrk) (List.find?_eq_none.mp hl r hr)
  · have hmem : e ∈ s.rows := List.mem_of_find?_eq_some hl
    have hkey : e.rowKey = k :=
      of_decide_eq_true
        (List.find?_some (p := fun x : SurfaceRow κ => decide (x.rowKey = k)) hl)
    show some e.surfaceDisposition = some r.surfaceDisposition
    rw [disposition_agrees_across_rows s h hmem hkey hr hrk]

/-- **`EC1-T008`, restated so it has content.** For every key in the recursively
resolved public universe the ledger assigns exactly one disposition, that
disposition is what the search returns, and it is not `excludedInternal`.

Unlike the schematic row this is FALSE on `droppedSurface` and FALSE on
`dupSurface` — which is the point, and what makes `EC1-F60` a falsifier OF IT
rather than of nothing. -/
theorem surface_disposition_exact (s : PublicSurface κ) (h : PublicSurfaceWF s)
    {k : κ} (hk : k ∈ s.keys) :
    ∃ d : SurfaceDisposition,
      s.dispositionOf k = some d
        ∧ (∀ r ∈ s.rows, r.rowKey = k → r.surfaceDisposition = d)
        ∧ d ≠ .excludedInternal := by
  obtain ⟨r, hr, hrk⟩ := h.covers k hk
  refine ⟨r.surfaceDisposition, dispositionOf_agrees s h hr hrk, ?_, ?_⟩
  · intro r' hr' hrk'
    exact disposition_agrees_across_rows s h hr' hrk' hr hrk
  · exact h.publicNotExcluded r hr (hrk ▸ hk)

end Ledger

/-! ## §6 — every premise is load-bearing

Each mutant of §3 refutes the restated theorem through exactly one clause, and
the third clause is independent of the other two. Without these three, adding
`PublicSurfaceWF` to the row would be the silent-strengthening move that the
`lean-model-invariants` gate exists to catch. -/

theorem droppedSurface_fails_covers :
    ¬ (∀ k ∈ droppedSurface.keys,
        ∃ r ∈ droppedSurface.rows, r.rowKey = k) := by
  decide

/-- **The coverage premise is necessary.** Without it the existence clause of
`surface_disposition_exact` is FALSE: `multipartHeaders` is a public key whose
disposition the ledger does not carry, and the search answers `none`. This is
`EC1-F60`'s drop half turning the restated row red. -/
theorem coverage_premise_is_necessary :
    ¬ ∀ (s : PublicSurface RowKey) (k : RowKey), k ∈ s.keys →
        ∃ d : SurfaceDisposition, s.dispositionOf k = some d := by
  intro h
  obtain ⟨d, hd⟩ := h droppedSurface .multipartHeaders (by decide)
  rw [droppedSurface_really_drops.2] at hd
  simp at hd

theorem dupSurface_fails_keysNodup :
    ¬ (dupSurface.rows.map (·.rowKey)).Nodup := by decide

/-- **The duplicate-free premise is necessary.** Without it the agreement clause
is FALSE: `dupSurface` declares `.targetOnly` for `succeed` and the search
answers `.reifiedPrimitive`. This is `EC1-CE030`'s forced repair — "add a
duplicate-free premise or make row validity supply it" — at the surface-ledger
carrier, and ruling **R16** part 2. Contrast `T008_holds_on_the_duplicate_mutant`:
the SCHEMATIC row is true on this same ledger, which is the whole argument for
replacing it. -/
theorem nodup_premise_is_necessary :
    ¬ ∀ (s : PublicSurface RowKey) (k : RowKey) (r : SurfaceRow RowKey),
        r ∈ s.rows → r.rowKey = k →
        s.dispositionOf k = some r.surfaceDisposition := by
  intro h
  have hbad := h dupSurface .succeed ⟨.succeed, .targetOnly⟩ (by decide) rfl
  rw [dupSurface_lookup_picks_the_first] at hbad
  exact absurd (Option.some.inj hbad) (by decide)

/-- **The exclusion premise is necessary, and independent.** `excludedSurface`
satisfies coverage and duplicate-freedom and still classifies a public key
`excludedInternal`, so the third clause is not implied by the first two. -/
theorem exclusion_premise_is_necessary_and_independent :
    (∀ k ∈ excludedSurface.keys, ∃ r ∈ excludedSurface.rows, r.rowKey = k)
      ∧ (excludedSurface.rows.map (·.rowKey)).Nodup
      ∧ ¬ (∀ r ∈ excludedSurface.rows, r.rowKey ∈ excludedSurface.keys →
            r.surfaceDisposition ≠ .excludedInternal) := by
  decide

/-- **No total disposition function exists on the raw carrier.** This is why the
DAG's word "total" cannot mean what it says until §7's checked carrier: there is
a `PublicSurface` and a public key at which the ledger simply has no value, so
`dispositionOf` is genuinely partial and no `κ → SurfaceDisposition` reading of
the ledger is available. -/
theorem raw_disposition_is_genuinely_partial :
    ∃ (s : PublicSurface RowKey) (k : RowKey),
      k ∈ s.keys ∧ s.dispositionOf k = none :=
  ⟨droppedSurface, .multipartHeaders, droppedSurface_really_drops⟩

/-! ## §7 — the checked carrier, where "total" becomes true with content

`lean-model-invariants`' boundary is `raw -> validate -> checked core`. On the
checked core the disposition IS a total function from the public key universe
into the SIX-value non-excluded set (§10), agreeing with the ledger. That is
what `surface_disposition_total` should have named. §6's
`raw_disposition_is_genuinely_partial` is the proof that it cannot be named one
step earlier. -/

section Checked

variable {κ : Type} [DecidableEq κ]

/-- The checked core: a ledger together with its well-formedness. -/
def CheckedSurface (κ : Type) [DecidableEq κ] : Type :=
  { s : PublicSurface κ // PublicSurfaceWF s }

/-- The explicit erasure back to raw data, as the stage requires. -/
def CheckedSurface.erase (c : CheckedSurface κ) : PublicSurface κ := c.val

/-- **The total disposition map.** Defined on the public key universe of a
checked surface, with no `Option` and no default arm. -/
def CheckedSurface.dispositionAt (c : CheckedSurface κ)
    (k : { k : κ // k ∈ c.val.keys }) : SurfaceDisposition :=
  (c.val.dispositionOf k.val).get (by
    obtain ⟨r, hr, hrk⟩ := c.property.covers k.val k.property
    exact dispositionOf_isSome c.val hr hrk)

/-- The total map is the ledger's own value, not a fresh invention. -/
theorem CheckedSurface.dispositionOf_eq_dispositionAt (c : CheckedSurface κ)
    (k : { k : κ // k ∈ c.val.keys }) :
    c.val.dispositionOf k.val = some (c.dispositionAt k) :=
  (Option.some_get _).symm

/-- Every ledger row for the key agrees with the total map. -/
theorem CheckedSurface.dispositionAt_agrees (c : CheckedSurface κ)
    (k : { k : κ // k ∈ c.val.keys }) :
    ∀ r ∈ c.val.rows, r.rowKey = k.val →
      r.surfaceDisposition = c.dispositionAt k := by
  intro r hr hrk
  have h := dispositionOf_agrees c.val c.property hr hrk
  rw [CheckedSurface.dispositionOf_eq_dispositionAt] at h
  exact (Option.some.inj h).symm

/-- `EC1-K07`: no public exposure is `excludedInternal`. -/
theorem CheckedSurface.dispositionAt_not_excluded (c : CheckedSurface κ)
    (k : { k : κ // k ∈ c.val.keys }) :
    c.dispositionAt k ≠ .excludedInternal := by
  obtain ⟨d, hd, _, hne⟩ := surface_disposition_exact c.val c.property k.property
  rw [CheckedSurface.dispositionOf_eq_dispositionAt] at hd
  rw [Option.some.inj hd]
  exact hne

end Checked

/-! ## §8 — the decider, which is what makes `EC1-F60` able to fire

A theorem stated UNDER `PublicSurfaceWF s` cannot turn red on a mutated ledger:
the hypothesis simply becomes undischargeable, and §5 goes quiet rather than
false. `EC1-F60` mutates generated data, so the instrument it attacks must be a
DECIDER over that data.

`checkSurface` is that decider, in the estate's own shape
(`Cas/Core/Admission.lean:60 checkRefs_ok_iff`, `Cas/Schema/Guarded.lean:421`)
and in the `lean-model-invariants` `Except Diagnostic` boundary form. Ruling
**R16** governs it: first-error soundness plus existential rejection
completeness, never a diagnostic per condemning clause. §9 exhibits the
two-defect ledger that keeps this file honest about that. -/

section Checker

variable {κ : Type} [DecidableEq κ]

/-- The three condemning clauses, one constructor each. -/
inductive SurfaceDefect (κ : Type) where
  /-- `EC1-F60` drop half: a public key the ledger does not classify. -/
  | unclassified (k : κ)
  /-- `EC1-F60` duplicate half: a key the ledger classifies more than once. -/
  | multiplyClassified (k : κ)
  /-- `EC1-K07`: a public key classified `excludedInternal`. -/
  | publicExcludedInternal (k : κ)
  deriving DecidableEq, Repr

/-- First repeated element, in list order. -/
def firstDupKey [DecidableEq κ] : List κ → Option κ
  | [] => none
  | k :: t =>
    match t.any (fun x => decide (x = k)) with
    | true => some k
    | false => firstDupKey t

theorem firstDupKey_cons_true {k : κ} {t : List κ}
    (h : t.any (fun x => decide (x = k)) = true) :
    firstDupKey (k :: t) = some k := by
  show (match t.any (fun x => decide (x = k)) with
        | true => some k | false => firstDupKey t) = some k
  rw [h]

theorem firstDupKey_cons_false {k : κ} {t : List κ}
    (h : t.any (fun x => decide (x = k)) = false) :
    firstDupKey (k :: t) = firstDupKey t := by
  show (match t.any (fun x => decide (x = k)) with
        | true => some k | false => firstDupKey t) = firstDupKey t
  rw [h]

/-- The duplicate search decides `Nodup`. -/
theorem firstDupKey_eq_none_iff (l : List κ) :
    firstDupKey l = none ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons a t ih =>
    cases hb : t.any (fun x => decide (x = a)) with
    | true =>
      have hmem : a ∈ t := by
        obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp hb
        exact (of_decide_eq_true hxa) ▸ hx
      constructor
      · intro h
        rw [firstDupKey_cons_true hb] at h
        simp at h
      · intro h
        exact absurd hmem (List.nodup_cons.mp h).1
    | false =>
      have hnot : a ∉ t := fun hc => by
        have : t.any (fun x => decide (x = a)) = true :=
          List.any_eq_true.mpr ⟨a, hc, decide_eq_true rfl⟩
        rw [hb] at this
        exact Bool.noConfusion this
      rw [firstDupKey_cons_false hb]
      exact ⟨fun h => List.nodup_cons.mpr ⟨hnot, ih.mp h⟩,
             fun h => ih.mpr (List.nodup_cons.mp h).2⟩

/-- The duplicate diagnostic is accurate: the key it names really does occur
twice, with an explicit split. -/
theorem firstDupKey_eq_some (l : List κ) {k : κ} (h : firstDupKey l = some k) :
    ∃ pre post, l = pre ++ k :: post ∧ k ∈ post := by
  induction l with
  | nil => simp [firstDupKey] at h
  | cons a t ih =>
    cases hb : t.any (fun x => decide (x = a)) with
    | true =>
      rw [firstDupKey_cons_true hb] at h
      obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp hb
      exact ⟨[], t, by rw [← Option.some.inj h]; rfl,
        by rw [← Option.some.inj h]; exact (of_decide_eq_true hxa) ▸ hx⟩
    | false =>
      rw [firstDupKey_cons_false hb] at h
      obtain ⟨pre, post, hl, hm⟩ := ih h
      exact ⟨a :: pre, post, by rw [hl]; rfl, hm⟩

/-- The fail-fast checker. Clause order is the ledger's own: coverage, then
uniqueness, then the `EC1-K07` exclusion. -/
def checkSurface (s : PublicSurface κ) : Except (SurfaceDefect κ) Unit :=
  match s.keys.find?
      (fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) with
  | some k => .error (.unclassified k)
  | none =>
    match firstDupKey (s.rows.map (·.rowKey)) with
    | some k => .error (.multiplyClassified k)
    | none =>
      match s.rows.find?
          (fun r => decide (r.rowKey ∈ s.keys)
            && decide (r.surfaceDisposition = .excludedInternal)) with
      | some r => .error (.publicExcludedInternal r.rowKey)
      | none => .ok ()

theorem coverSearch_eq_none_iff (s : PublicSurface κ) :
    s.keys.find? (fun k => !(s.rows.any (fun r => decide (r.rowKey = k))))
      = none ↔ ∀ k ∈ s.keys, ∃ r ∈ s.rows, r.rowKey = k := by
  rw [List.find?_eq_none]
  constructor
  · intro h k hk
    have hb : s.rows.any (fun r => decide (r.rowKey = k)) = true := by
      cases hc : s.rows.any (fun r => decide (r.rowKey = k)) with
      | true => rfl
      | false => exact absurd (by rw [hc]; rfl) (h k hk)
    obtain ⟨r, hr, hrk⟩ := List.any_eq_true.mp hb
    exact ⟨r, hr, of_decide_eq_true hrk⟩
  · intro h k hk hc
    obtain ⟨r, hr, hrk⟩ := h k hk
    have hb : s.rows.any (fun r => decide (r.rowKey = k)) = true :=
      List.any_eq_true.mpr ⟨r, hr, decide_eq_true hrk⟩
    rw [hb] at hc
    exact Bool.noConfusion hc

theorem exclSearch_eq_none_iff (s : PublicSurface κ) :
    s.rows.find? (fun r => decide (r.rowKey ∈ s.keys)
        && decide (r.surfaceDisposition = .excludedInternal)) = none
      ↔ ∀ r ∈ s.rows, r.rowKey ∈ s.keys →
          r.surfaceDisposition ≠ .excludedInternal := by
  rw [List.find?_eq_none]
  constructor
  · intro h r hr hk hd
    exact h r hr (by rw [decide_eq_true hk, decide_eq_true hd]; rfl)
  · intro h r hr hc
    have hand := Bool.and_eq_true .. |>.mp hc
    exact h r hr (of_decide_eq_true hand.1) (of_decide_eq_true hand.2)

/-- **The decider is exact.** First-error soundness and existential rejection
completeness in one statement, per ruling **R16** — and NOT a diagnostic per
condemning clause, which §9 shows would be false. Shape:
`Cas/Core/Admission.lean:60 checkRefs_ok_iff`. -/
theorem checkSurface_ok_iff (s : PublicSurface κ) :
    checkSurface s = .ok () ↔ PublicSurfaceWF s := by
  constructor
  · intro h
    rw [checkSurface] at h
    cases hcov : s.keys.find?
        (fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) with
    | some k => rw [hcov] at h; simp at h
    | none =>
      rw [hcov] at h
      cases hdup : firstDupKey (s.rows.map (·.rowKey)) with
      | some k => rw [hdup] at h; simp at h
      | none =>
        cases hexc : s.rows.find?
            (fun r => decide (r.rowKey ∈ s.keys)
              && decide (r.surfaceDisposition = .excludedInternal)) with
        | some r => rw [hdup, hexc] at h; simp at h
        | none =>
          exact ⟨(coverSearch_eq_none_iff s).mp hcov,
                 (firstDupKey_eq_none_iff _).mp hdup,
                 (exclSearch_eq_none_iff s).mp hexc⟩
  · intro hwf
    rw [checkSurface,
        (coverSearch_eq_none_iff s).mpr hwf.covers,
        (firstDupKey_eq_none_iff _).mpr hwf.keysNodup,
        (exclSearch_eq_none_iff s).mpr hwf.publicNotExcluded]

/-- **First-error soundness.** Anything the checker reports is a real
violation. -/
theorem checkSurface_error_sound (s : PublicSurface κ) {e : SurfaceDefect κ}
    (h : checkSurface s = .error e) : ¬ PublicSurfaceWF s := by
  intro hwf
  rw [(checkSurface_ok_iff s).mpr hwf] at h
  simp at h

/-- **Existential rejection completeness.** Every ill-formed ledger is
rejected — with SOME diagnostic, not necessarily with every one. -/
theorem checkSurface_rejects (s : PublicSurface κ) (h : ¬ PublicSurfaceWF s) :
    ∃ e : SurfaceDefect κ, checkSurface s = .error e := by
  cases hc : checkSurface s with
  | error e => exact ⟨e, rfl⟩
  | ok u =>
    exact absurd ((checkSurface_ok_iff s).mp (by cases u; exact hc)) h

/-- The `unclassified` diagnostic comes from the coverage search, and names the
key that search found. -/
theorem checkSurface_unclassified_source (s : PublicSurface κ) {k : κ}
    (h : checkSurface s = .error (.unclassified k)) :
    s.keys.find? (fun k => !(s.rows.any (fun r => decide (r.rowKey = k))))
      = some k := by
  rw [checkSurface] at h
  cases hcov : s.keys.find?
      (fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) with
  | some k' =>
    rw [hcov] at h
    simp at h
    subst h
    rfl
  | none =>
    exfalso
    rw [hcov] at h
    cases hdup : firstDupKey (s.rows.map (·.rowKey)) with
    | some k'' => rw [hdup] at h; simp at h
    | none =>
      cases hexc : s.rows.find?
          (fun r => decide (r.rowKey ∈ s.keys)
            && decide (r.surfaceDisposition = .excludedInternal)) with
      | some r => rw [hdup, hexc] at h; simp at h
      | none => rw [hdup, hexc] at h; simp at h

/-- **The `unclassified` diagnostic is accurate**, which mere unsoundness of the
conjunction would not give: the key it names is public and really has no
disposition. This is `EC1-F60`'s drop half, reported. -/
theorem unclassified_diagnostic_is_accurate (s : PublicSurface κ) {k : κ}
    (h : checkSurface s = .error (.unclassified k)) :
    k ∈ s.keys ∧ s.dispositionOf k = none := by
  have hcov := checkSurface_unclassified_source s h
  refine ⟨List.mem_of_find?_eq_some hcov, dispositionOf_eq_none s ?_⟩
  intro r hr hrk
  have hb := List.find?_some
    (p := fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) hcov
  have hany : s.rows.any (fun r => decide (r.rowKey = k)) = true :=
    List.any_eq_true.mpr ⟨r, hr, decide_eq_true hrk⟩
  rw [hany] at hb
  simp at hb

/-- **The `multiplyClassified` diagnostic is accurate**: the key it names really
is written twice in the ledger, with an explicit split. This is `EC1-F60`'s
duplicate half, reported. -/
theorem multiplyClassified_diagnostic_is_accurate (s : PublicSurface κ) {k : κ}
    (h : firstDupKey (s.rows.map (·.rowKey)) = some k) :
    (∃ pre post, s.rows.map (·.rowKey) = pre ++ k :: post ∧ k ∈ post)
      ∧ ¬ (s.rows.map (·.rowKey)).Nodup := by
  refine ⟨firstDupKey_eq_some _ h, fun hnd => ?_⟩
  rw [(firstDupKey_eq_none_iff _).mpr hnd] at h
  simp at h

end Checker

/-! ### §8a — the decider rejects every `EC1-F60` mutant, by name

These are the theorems `EC1-F60` actually turns red. Each is `rfl`: the checker
computes on a literal ledger, so the diagnostic is a definitional fact rather
than a claim. -/

theorem checkSurface_rejects_the_drop_mutant :
    checkSurface droppedSurface
      = .error (.unclassified .multipartHeaders) := rfl

theorem checkSurface_rejects_the_duplicate_mutant :
    checkSurface dupSurface = .error (.multiplyClassified .succeed) := rfl

theorem checkSurface_rejects_the_excludedInternal_mutant :
    checkSurface excludedSurface
      = .error (.publicExcludedInternal .succeed) := rfl

/-- A positive control: the well-formedness structure is not vacuously
unsatisfiable, and the checker accepts. Without this every rejection theorem
above would be consistent with a checker that rejects everything. -/
def goodSurface : PublicSurface RowKey where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows :=
    [⟨.succeed, .reifiedPrimitive⟩,
     ⟨.failCause, .derivedExpansion⟩,
     ⟨.multipartHeaders, .separateSubcalculus⟩]

theorem goodSurface_is_wf : PublicSurfaceWF goodSurface := by decide

theorem checkSurface_accepts_goodSurface : checkSurface goodSurface = .ok () :=
  rfl

/-- The checked carrier is inhabited, so §7's total map is not a statement about
the empty type. -/
def goodChecked : CheckedSurface RowKey := ⟨goodSurface, goodSurface_is_wf⟩

theorem goodChecked_dispositionAt :
    goodChecked.dispositionAt ⟨.multipartHeaders, by decide⟩
      = .separateSubcalculus := rfl

/-! ## §9 — ruling **R16**: the checker is first-error, and this file says so

`EC1-CE031` (`VERIFIED-KERNEL`, `COUNTEREXAMPLES.md:95`) defeats "a fail-fast
checker returns a diagnostic for every condemning clause" at the reference-list
carrier. Ruling **R16** part 1 makes first-error soundness plus existential
rejection completeness the admissible pair, and says a per-clause census "is a
different declaration".

The lesson is transplanted here with a fresh witness rather than cited: a ledger
that violates BOTH `EC1-F60` halves at once, on which `checkSurface` names
exactly one. `checkSurface_ok_iff`, `checkSurface_error_sound` and
`checkSurface_rejects` are the only claims this file makes about the checker,
and all three are inside R16. -/

/-- Two condemning clauses at once: `failCause` and `multipartHeaders` are
public and unclassified, and `succeed` is classified twice. -/
def doubleDefect : PublicSurface RowKey where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.succeed, .targetOnly⟩]

theorem doubleDefect_violates_two_clauses :
    ¬ (∀ k ∈ doubleDefect.keys, ∃ r ∈ doubleDefect.rows, r.rowKey = k)
      ∧ ¬ (doubleDefect.rows.map (·.rowKey)).Nodup := by
  decide

/-- **`EC1-CE031` at this carrier.** The checker names the coverage defect and
is silent about the duplicate. A specification demanding a diagnostic per
condemning clause is therefore FALSE of `checkSurface`, exactly as R16 says. -/
theorem checkSurface_reports_only_the_first :
    checkSurface doubleDefect = .error (.unclassified .failCause) := rfl

/-- Stated as the refutation, so it cannot be mistaken for a passing check. -/
theorem diagnostic_completeness_is_false :
    ¬ ∀ (s : PublicSurface RowKey),
        ¬ (s.rows.map (·.rowKey)).Nodup →
        ∃ k, checkSurface s = .error (.multiplyClassified k) := by
  intro h
  obtain ⟨k, hk⟩ := h doubleDefect doubleDefect_violates_two_clauses.2
  rw [checkSurface_reports_only_the_first] at hk
  simp at hk

/-! ## §10 — the closed seven-value enum, which the schematic row cannot express

`REIFICATION-CHECKLIST.md:488-489` forbids `unknown`, `todo`, `deferred` and
null dispositions in a closed ledger. §1's proof is indifferent to the codomain
(`T008_holds_with_a_null_disposition_arm` makes that concrete), so the schematic
row buys none of it.

What DOES buy it is the estate's shipped shape at
`Cas/Schema/Declarations.lean:273-276` and `Cas/Lift/Taxonomy.lean:208-220`: a
registry list plus a completeness theorem whose `decide` FAILS TO BUILD when an
arm is added without updating the list. That build failure, not `EC1-T008`, is
what keeps an eighth arm out. §10a instantiates the same gate at the estate's
own twenty-row enum, so the shape is demonstrated rather than asserted. -/

/-- Every disposition, in ledger order. Mirror of `General.all` (`:273`). -/
def SurfaceDisposition.all : List SurfaceDisposition :=
  [.reifiedPrimitive, .derivedExpansion, .separateSubcalculus,
   .pureOrHostOnlyClosedOutsideProg, .projectOwnedReplacementOrForeignOp,
   .targetOnly, .excludedInternal]

/-- The table is complete. Mirror of `General.all_complete` (`:276`). An eighth
arm added without extending `all` makes this `decide` fail to build. -/
theorem SurfaceDisposition.all_complete (d : SurfaceDisposition) :
    d ∈ SurfaceDisposition.all := by
  cases d <;> decide

/-- The table has no repeats. Mirror of the `#guard` at `:207`/`:220`. -/
theorem SurfaceDisposition.all_nodup : SurfaceDisposition.all.Nodup := by decide

/-- The enum has exactly seven inhabitants — the row's "seven-value enum"
dependency, proved rather than named. -/
theorem SurfaceDisposition.all_length : SurfaceDisposition.all.length = 7 := by
  decide

/-- The PUBLIC disposition universe, which `EC1-K07` closes at six. -/
def SurfaceDisposition.publicAll : List SurfaceDisposition :=
  [.reifiedPrimitive, .derivedExpansion, .separateSubcalculus,
   .pureOrHostOnlyClosedOutsideProg, .projectOwnedReplacementOrForeignOp,
   .targetOnly]

theorem SurfaceDisposition.mem_publicAll_iff (d : SurfaceDisposition) :
    d ∈ SurfaceDisposition.publicAll ↔ d ≠ .excludedInternal := by
  cases d <;> decide

theorem SurfaceDisposition.publicAll_nodup :
    SurfaceDisposition.publicAll.Nodup := by decide

theorem SurfaceDisposition.publicAll_length :
    SurfaceDisposition.publicAll.length = 6 := by decide

/-- **The sharpened conclusion.** On the checked carrier the total disposition
map lands in the six-value public set — "exactly one of seven, and never the
seventh", in closed-universe form. -/
theorem CheckedSurface.dispositionAt_mem_publicAll {κ : Type} [DecidableEq κ]
    (c : CheckedSurface κ) (k : { k : κ // k ∈ c.val.keys }) :
    c.dispositionAt k ∈ SurfaceDisposition.publicAll :=
  (SurfaceDisposition.mem_publicAll_iff _).mpr
    (CheckedSurface.dispositionAt_not_excluded c k)

/-! ### §10a — the same gate at the estate's own twenty-row enum

`Cas.Lift.RefusalCode` is a shipped closed taxonomy of the same kind as
`EC1-K07`'s disposition enum, at twenty rows against seven, and already mirrored
into TypeScript. `estate_gate_all_complete` is the estate's own theorem cited as
its proof term, not re-proved; the other two are proved here by `decide` and are
this file's, showing that §10's gate is the estate's shape rather than a scratch
invention and that it costs nothing at real scale. Nothing is minted, nothing is
promoted, and `Cas.Lift` is read only.

The caveat the estate puts on itself transfers verbatim and is not discharged
anywhere in this file: `Cas/Lang/RefusalMap.lean:172-176` records that its
host-facing enum is "a HAND MIRROR: this module reads no TypeScript, so the only
thing keeping the two in step today is that they are written down beside each
other." A generated surface ledger inherits exactly that gap at the mirror join,
which is the half of `EC1-F60` no Lean theorem here reaches. -/

theorem estate_gate_all_complete (c : Cas.Lift.RefusalCode) :
    c ∈ Cas.Lift.RefusalCode.all :=
  Cas.Lift.RefusalCode.all_complete c

theorem estate_gate_wire_nodup :
    (Cas.Lift.RefusalCode.all.map Cas.Lift.RefusalCode.wire).Nodup := by decide

theorem estate_gate_length : Cas.Lift.RefusalCode.all.length = 20 := by decide

/-! ## §11 — `PublicSurfaceWF` says nothing about census completeness

`EC1-CE020` (`VERIFIED-TOOL`, `COUNTEREXAMPLES.md:82`) proved the old
359-module bank is not an exhaustive `rc.112` census:
`effect/unstable/http/MultipartParser/HeadersParser` and `/Search` resolve
publicly and are absent. `EC1-F59` (`CONTRACT-PACKET.md:740`) is its falsifier.

Since `covers` quantifies over `s.keys`, an incomplete key universe makes the
restated theorem TRUE and worthless. That is not a caveat here; it is a theorem.
The consequence is a packet obligation: `EC1-F59` and `EC1-F60` attack DIFFERENT
clauses, and the census clause must be stated separately. §11a states it and
proves what the pair buys jointly. -/

/-- A ledger whose key universe simply omits the deep `MultipartParser` module.
Everything it does carry is classified, duplicate-free, and non-excluded. -/
def censusGap : PublicSurface RowKey where
  keys := [.succeed, .failCause]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.failCause, .derivedExpansion⟩]

/-- **`EC1-CE020` at this carrier.** A fully well-formed ledger that the deep
module is missing from entirely, and whose search answers `none` for it. The
checker accepts it. So no strengthening of `EC1-T008` can close `EC1-F59`. -/
theorem wf_does_not_imply_census_completeness :
    PublicSurfaceWF censusGap
      ∧ checkSurface censusGap = .ok ()
      ∧ RowKey.multipartHeaders ∉ censusGap.keys
      ∧ censusGap.dispositionOf .multipartHeaders = none :=
  ⟨by decide, rfl, by decide, by decide⟩

/-- The census clause `EC1-F59` attacks, stated separately as `EC1-CE020`
requires. `U` is the recursively resolved public universe the source hoover
owns; `EC1-H11` is what must supply it. -/
def CensusComplete {κ : Type} (U : List κ) (s : PublicSurface κ) : Prop :=
  ∀ k ∈ U, k ∈ s.keys

/-- **What the two clauses buy jointly**, and only jointly: every module in the
recursively resolved public universe has exactly one disposition, it is what the
search returns, and it is one of the six public values. Dropping either premise
loses the conclusion — `wf_does_not_imply_census_completeness` kills the second,
`coverage_premise_is_necessary` kills the first. -/
theorem census_and_wf_give_disposition {κ : Type} [DecidableEq κ]
    (U : List κ) (s : PublicSurface κ)
    (hc : CensusComplete U s) (h : PublicSurfaceWF s)
    {k : κ} (hk : k ∈ U) :
    ∃ d : SurfaceDisposition,
      s.dispositionOf k = some d
        ∧ (∀ r ∈ s.rows, r.rowKey = k → r.surfaceDisposition = d)
        ∧ d ∈ SurfaceDisposition.publicAll := by
  obtain ⟨d, hd, hag, hne⟩ := surface_disposition_exact s h (hc k hk)
  exact ⟨d, hd, hag, (SurfaceDisposition.mem_publicAll_iff d).mpr hne⟩

/-- `censusGap` fails the census clause at the deep module `EC1-F59` names, so
the premise added above is load-bearing and not decoration. -/
theorem censusGap_fails_the_census_clause :
    ¬ CensusComplete [RowKey.succeed, .failCause, .multipartHeaders]
        censusGap := by
  intro h
  exact absurd (h .multipartHeaders (by decide)) (by decide)

/-! ## §12 — the restatement replaces the row without loss, and strictly

The schematic row is a CONSEQUENCE of the restated one (indeed of nothing at
all), so nothing is lost by replacing it; and there are ledgers satisfying the
schematic row that the restatement rejects, so the replacement is strict in the
direction that matters. -/

theorem restatement_implies_the_schematic_row {κ : Type}
    (s : PublicSurface κ) :
    ∀ r ∈ s.rows, UniqueEq r.surfaceDisposition :=
  fun r _ => bang_is_free SurfaceRow.surfaceDisposition r

/-- **The replacement is strict.** All three `EC1-F60`/`EC1-K07` mutants satisfy
the schematic row and are rejected by the decider. -/
theorem the_replacement_is_strict :
    ((∀ r ∈ droppedSurface.rows, UniqueEq r.surfaceDisposition)
        ∧ ¬ PublicSurfaceWF droppedSurface)
      ∧ ((∀ r ∈ dupSurface.rows, UniqueEq r.surfaceDisposition)
        ∧ ¬ PublicSurfaceWF dupSurface)
      ∧ ((∀ r ∈ excludedSurface.rows, UniqueEq r.surfaceDisposition)
        ∧ ¬ PublicSurfaceWF excludedSurface) :=
  ⟨⟨T008_holds_on_the_drop_mutant, by decide⟩,
   ⟨T008_holds_on_the_duplicate_mutant, by decide⟩,
   ⟨T008_holds_on_the_excludedInternal_mutant, by decide⟩⟩

end EffectCoreT008

/-! ## Kernel receipts

One line per theorem. `propext` and `Quot.sound` are the only axioms reached;
`Classical.choice` is not, and neither is `sorryAx`. -/

#print axioms EffectCoreT008.bang_is_free
#print axioms EffectCoreT008.T008_as_written_ignores_both_premises
#print axioms EffectCoreT008.T008_needs_no_surface
#print axioms EffectCoreT008.UniqueEq_is_the_unfolding
#print axioms EffectCoreT008.droppedSurface_really_drops
#print axioms EffectCoreT008.dupSurface_really_duplicates
#print axioms EffectCoreT008.dupSurface_lookup_picks_the_first
#print axioms EffectCoreT008.T008_holds_on_the_drop_mutant
#print axioms EffectCoreT008.T008_holds_on_the_duplicate_mutant
#print axioms EffectCoreT008.T008_holds_on_the_excludedInternal_mutant
#print axioms EffectCoreT008.T008_holds_of_every_total_disposition
#print axioms EffectCoreT008.T008_holds_with_a_null_disposition_arm
#print axioms EffectCoreT008.nodup_key_unique
#print axioms EffectCoreT008.dispositionOf_eq_none
#print axioms EffectCoreT008.dispositionOf_isSome
#print axioms EffectCoreT008.disposition_agrees_across_rows
#print axioms EffectCoreT008.dispositionOf_agrees
#print axioms EffectCoreT008.surface_disposition_exact
#print axioms EffectCoreT008.droppedSurface_fails_covers
#print axioms EffectCoreT008.coverage_premise_is_necessary
#print axioms EffectCoreT008.dupSurface_fails_keysNodup
#print axioms EffectCoreT008.nodup_premise_is_necessary
#print axioms EffectCoreT008.exclusion_premise_is_necessary_and_independent
#print axioms EffectCoreT008.raw_disposition_is_genuinely_partial
#print axioms EffectCoreT008.CheckedSurface.dispositionOf_eq_dispositionAt
#print axioms EffectCoreT008.CheckedSurface.dispositionAt_agrees
#print axioms EffectCoreT008.CheckedSurface.dispositionAt_not_excluded
#print axioms EffectCoreT008.firstDupKey_cons_true
#print axioms EffectCoreT008.firstDupKey_cons_false
#print axioms EffectCoreT008.firstDupKey_eq_none_iff
#print axioms EffectCoreT008.firstDupKey_eq_some
#print axioms EffectCoreT008.coverSearch_eq_none_iff
#print axioms EffectCoreT008.exclSearch_eq_none_iff
#print axioms EffectCoreT008.checkSurface_ok_iff
#print axioms EffectCoreT008.checkSurface_error_sound
#print axioms EffectCoreT008.checkSurface_rejects
#print axioms EffectCoreT008.checkSurface_unclassified_source
#print axioms EffectCoreT008.unclassified_diagnostic_is_accurate
#print axioms EffectCoreT008.multiplyClassified_diagnostic_is_accurate
#print axioms EffectCoreT008.checkSurface_rejects_the_drop_mutant
#print axioms EffectCoreT008.checkSurface_rejects_the_duplicate_mutant
#print axioms EffectCoreT008.checkSurface_rejects_the_excludedInternal_mutant
#print axioms EffectCoreT008.goodSurface_is_wf
#print axioms EffectCoreT008.checkSurface_accepts_goodSurface
#print axioms EffectCoreT008.goodChecked_dispositionAt
#print axioms EffectCoreT008.doubleDefect_violates_two_clauses
#print axioms EffectCoreT008.checkSurface_reports_only_the_first
#print axioms EffectCoreT008.diagnostic_completeness_is_false
#print axioms EffectCoreT008.SurfaceDisposition.all_complete
#print axioms EffectCoreT008.SurfaceDisposition.all_nodup
#print axioms EffectCoreT008.SurfaceDisposition.all_length
#print axioms EffectCoreT008.SurfaceDisposition.mem_publicAll_iff
#print axioms EffectCoreT008.SurfaceDisposition.publicAll_nodup
#print axioms EffectCoreT008.SurfaceDisposition.publicAll_length
#print axioms EffectCoreT008.CheckedSurface.dispositionAt_mem_publicAll
#print axioms EffectCoreT008.estate_gate_all_complete
#print axioms EffectCoreT008.estate_gate_wire_nodup
#print axioms EffectCoreT008.estate_gate_length
#print axioms EffectCoreT008.wf_does_not_imply_census_completeness
#print axioms EffectCoreT008.census_and_wf_give_disposition
#print axioms EffectCoreT008.censusGap_fails_the_census_clause
#print axioms EffectCoreT008.restatement_implies_the_schematic_row
#print axioms EffectCoreT008.the_replacement_is_strict
