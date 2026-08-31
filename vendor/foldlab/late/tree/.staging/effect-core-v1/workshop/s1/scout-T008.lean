/-!
# Effect Core v1 — scout probe for `EC1-T008` (`surface_disposition_total`)

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T008.lean
```

Stage: `lean-formalization-strategy`, **Pass A** (contract). Pass B is
unavailable: `formal/effect-core-v1/EffectCore/Surface/Disposition.lean` and its
three siblings are 300-byte empty stubs, and `PublicSurface`, `SurfaceRowKey`,
`SurfaceDisposition` have **zero** definitions anywhere in the estate's Lean
(`grep -rn --include='*.lean' PublicSurface .` finds only the stub's own docstring
and an `EffectCore.lean` import line). There is no signature to freeze yet.

Scouting only. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/`. This file is outside every lake target, exactly like
`../exhibits.lean`, `../counterexamples/Nondeterminism.lean` and
`../../breaker-exhibits.lean`. It adds nothing to `Cas`, moves no byte, promotes
no name, and mints no second surface carrier: the scratch model below exists
only to decide the SHAPE of the row's statement.

The DAG's schematic signature (`PROOF-DAG.md:200`) is

    surface_disposition_total :
      PublicSurfaceWF s -> forall row in s, exists! d, disposition row = d

Five findings, each with a kernel behind it:

* §1 the row is **fully vacuous** — `∃! d, f x = d` holds for every function
  into every type, with `PublicSurfaceWF s` and `row ∈ s` both dead. It is
  strictly emptier than `EC1-T004`, whose `Option` codomain at least leaves an
  `isSome` residue. The estate has **already written this theorem**:
  `../EffectCoreProbe.lean:331` `total_disposition_classification`, whose proof
  is `⟨classifyDisposition role, rfl, fun _ found => found.symm⟩` and whose
  receipt reads *does not depend on any axioms*. §1 reproduces that collapse
  from nothing at all.
* §2 the `∃!` connective **does not exist in this environment**, so the row
  cannot be stated as written before someone defines it;
* §3 **`EC1-F60` is unstateable against the row.** The falsifier's two
  mutations — *drop* a public row's disposition and *duplicate* it — are
  exactly the two things a total function cannot exhibit. Both mutants are
  built here and the schematic row is proved TRUE of both;
* §4 the statement that has content, plus proofs that each of its two premises
  is load-bearing. This is `EC1-CE030`'s duplicate-free repair
  (`COUNTEREXAMPLES.md:94`) transplanted to the surface-ledger carrier;
* §5 the "seven-value enum" clause, which the schematic row also does not
  carry, in the shape the estate already ships at
  `Cas/Schema/Declarations.lean:276`/`:281`/`:288`/`:297`.

§6 records the `excludedInternal` clause of `EC1-K07` that the row drops.

## Receipts

26 `#print axioms` receipts, all at the foot. Ceiling `[propext, Quot.sound]`
(`Quot.sound` enters only through the `List` `simp` normalization inside the
`Nodup` induction and the `find?` case split); **13** of the 26 are axiom-free —
including every one of the five vacuity findings, which is itself the point:
they need nothing. No `sorryAx`, no `Classical.choice`, no
`native_decide`, no `#eval`, no `axiom`. `lake env lean` exits 0.

## Scope of what this file establishes

It settles the SHAPE of `EC1-T008`'s statement and nothing else. It is not
evidence that the generated rc.112 ledger is complete — `EC1-CE020` is the live
counterexample to the completeness of the census that would supply
`PublicSurfaceWF`, and that is a `VERIFIED-TOOL` claim about the source hoover,
not about anything below. §4's carrier is a scratch three-key model; the real
`SurfaceRowKey` universe is thousands of rows and its `Nodup`/coverage facts
must be discharged against generated data, not asserted here.

## Anchor defect found while verifying

`.staging/agent-reports/2026-08-31-effect-core-local-anchors.md:718` describes
the anchor as "a `SurfaceDisposition` totality gate already shipped, at a
**seven-row registry** instead of a seven-value enum". The three theorems it
cites resolve exactly (`Cas/Schema/Declarations.lean:281`, `:288`, `:297`), but
the registry is **four** rows (`DeclarationId`: `casRef`, `effectDate`,
`effectUrl`, `effectOption`) of which `General` spells **three**. The count is
wrong; the anchor is not. `Declarations.lean:32-33` is the sentence that makes
it the right anchor: "adding a registry row without dispositioning it is a
build error."

A second line-number defect in the same report: `:769` cites
`Cas/Lang/RefusalMap.lean:181` for the HAND MIRROR caveat (row `T107`). Line 181
is the constructor `| danglingReference`; the caveat's docstring is at
`:172-176`. The caveat itself is real and is quoted verbatim in §7.
-/

namespace EffectCoreScoutT008

/-! ## §0 — the scratch carrier

A row-key universe, a seven-value disposition enum, a ledger of generated rows,
and the surface that pairs them. Deliberately minimal: every finding below is
about the SHAPE of the statement, so richer `SurfaceRow` fields would only add
noise. The enum is transcribed verbatim from `CONTRACT-PACKET.md:212-215`
(`EC1-K07`) and `REIFICATION-CHECKLIST.md:494-502`. -/

/-- The seven-way source-to-model disposition (`EC1-D008`, `EC1-A37`). -/
inductive Disposition where
  | reifiedPrimitive
  | derivedExpansion
  | separateSubcalculus
  | pureOrHostOnlyClosedOutsideProg
  | projectOwnedReplacementOrForeignOp
  | targetOnly
  | excludedInternal
  deriving DecidableEq, Repr

/-- Scratch `SurfaceRowKey` (`EC1-D007`). `multipartHeaders` is the deep
`effect/unstable/http/MultipartParser/HeadersParser` module that `EC1-CE020`
proved absent from the old 359-module bank and that `EC1-F59` requires present;
it is used below as the concretely droppable key. -/
inductive RowKey where
  | succeed | failCause | multipartHeaders
  deriving DecidableEq, Repr

/-- One generated ledger row. `REIFICATION-CHECKLIST.md:564` makes
`surfaceDisposition` a required FIELD of `SurfaceRow`, so the disposition is a
projection out of ledger data, not a standalone function. -/
structure SurfaceRow where
  rowKey : RowKey
  disp : Disposition
  deriving DecidableEq, Repr

/-- Scratch `PublicSurface` (`EC1-D006`): the recursively resolved key universe
`U_row`, plus the generated disposition ledger over it. The two are separate
because the source hoover owns the first and Lean consumes the second
(`PROOF-DAG.md:91`). -/
structure PublicSurface where
  keys : List RowKey
  rows : List SurfaceRow

/-- The lookup the row's `disposition row` presumes once the ledger is data. -/
def PublicSurface.dispositionOf (s : PublicSurface) (k : RowKey) :
    Option Disposition :=
  (s.rows.find? (fun r => decide (r.rowKey = k))).map (·.disp)

/-! ## §1 — the row is vacuous, with no residue at all

`PROOF-DAG.md:207` already deleted `exists! v, evalPure e env = v` and the
same-input function-equality forms as "tautologies for any Lean function".
`EC1-T008` is that deleted form. `EC1-T004` escaped the same deletion only
because `lookup` is `Option`-valued and `some` can be `none`; `disposition` is
not, so `EC1-T008` has no escape. -/

/-- The DAG's `exists! d, v = d`, spelled out (see §2 for why it must be). -/
def UniqueEq {δ : Type} (v : δ) : Prop :=
  ∃ d, v = d ∧ ∀ e, v = e → e = d

/-- **Finding 1.** `exists! d, f x = d` holds for EVERY function into EVERY
type. There is no hypothesis, no `Option`, no ledger, and no surface. -/
theorem bang_is_free {α δ : Type} (f : α → δ) (x : α) : UniqueEq (f x) :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- **`EC1-T008` as written, with both stated premises visibly discarded.** The
underscores are the finding: `PublicSurfaceWF s` and `row ∈ s` do no work. -/
theorem T008_as_written_ignores_both_premises
    (_wf : True) (s : PublicSurface) :
    ∀ r ∈ s.rows, UniqueEq r.disp :=
  fun r _ => bang_is_free SurfaceRow.disp r

/-- The row does not even need a `PublicSurface` to be about. Any list of any
records with any field satisfies it. -/
theorem T008_needs_no_surface {α δ : Type} (g : α → δ) (l : List α) :
    ∀ x ∈ l, UniqueEq (g x) :=
  fun x _ => bang_is_free g x

/-! ## §2 — the connective is not available

Reverified this pass: `library/cas` pins `leanprover/lean4:v4.33.1` with an
EMPTY `.lake/packages` (no Mathlib, no dependency at all). `#check
@ExistsUnique` reports *Unknown identifier*, and `∃!` fails to parse
(*unexpected token '!'*). `grep -rn 'ExistsUnique\|∃!' library/cas/Cas` is
empty: the estate has never used the connective.

Every DAG row spelled with `exists!` — `EC1-T004` (`:193`), **`EC1-T008`**
(`:200`), `EC1-T016` (`:225`), `EC1-T035` (`:288`) — therefore owes either a
definition or an explicit spelling before it can be stated at all. `UniqueEq`
above is that spelling; `../EffectCoreProbe.lean:331` independently reached the
same conclusion and wrote the conjunction out by hand. -/

/-- The unfolded spelling is what the estate's own prototype already uses, so
nothing about §1 is an artifact of how `∃!` was spelled here. -/
theorem UniqueEq_is_the_probe_spelling {δ : Type} (v : δ) :
    UniqueEq v ↔ ∃ d, v = d ∧ ∀ e, v = e → e = d :=
  Iff.rfl

/-! ## §3 — `EC1-F60` is unstateable against the row

`CONTRACT-PACKET.md:741` reads:

> `EC1-F60` | Drop or duplicate a public row's seven-way disposition. |
> Disposition totality/uniqueness fails while proof status remains irrelevant.

A reader expects `surface_disposition_total` to be the theorem this falsifier
turns red. It is not, and it cannot be: the falsifier mutates the generated
LEDGER, while the row quantifies over a total FUNCTION, which is single-valued
by construction and defined everywhere by typing. Both mutants are built below
and the row is proved TRUE of each. -/

/-- **`EC1-F60`, mutation one: DROP.** `multipartHeaders` is in the key
universe and has no ledger row. -/
def droppedSurface : PublicSurface where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.failCause, .reifiedPrimitive⟩]

/-- The mutant really is the forbidden one: a public key with no disposition. -/
theorem droppedSurface_really_drops :
    RowKey.multipartHeaders ∈ droppedSurface.keys
      ∧ droppedSurface.dispositionOf .multipartHeaders = none := by
  decide

/-- **`EC1-F60`, mutation two: DUPLICATE.** One key, two ledger rows, two
DIFFERENT dispositions. -/
def dupSurface : PublicSurface where
  keys := [.succeed]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.succeed, .targetOnly⟩]

/-- The mutant really is the forbidden one: the key is multiply classified,
which `EC1-K07` (`CONTRACT-PACKET.md:227`) names as not permitted. -/
theorem dupSurface_really_duplicates :
    (⟨.succeed, .reifiedPrimitive⟩ : SurfaceRow) ∈ dupSurface.rows
      ∧ (⟨.succeed, .targetOnly⟩ : SurfaceRow) ∈ dupSurface.rows
      ∧ (Disposition.reifiedPrimitive ≠ .targetOnly) := by
  decide

/-- The ledger search silently keeps the first row and discards the second. -/
theorem dupSurface_lookup_picks_the_first :
    dupSurface.dispositionOf .succeed = some .reifiedPrimitive := by
  decide

/-- **Finding 3a.** The schematic row is TRUE of the DROP mutant. The dropped
key is not a `row in s`, so the statement's own quantifier never reaches it. -/
theorem T008_holds_on_the_drop_mutant :
    ∀ r ∈ droppedSurface.rows, UniqueEq r.disp :=
  fun r _ => bang_is_free SurfaceRow.disp r

/-- **Finding 3b.** The schematic row is TRUE of the DUPLICATE mutant. The `∃!`
is on the FIELD, which is single-valued by construction, not on the ASSIGNMENT
of dispositions to keys, which is not. This is `EC1-CE030`
(`COUNTEREXAMPLES.md:94`) at the surface carrier. -/
theorem T008_holds_on_the_duplicate_mutant :
    ∀ r ∈ dupSurface.rows, UniqueEq r.disp :=
  fun r _ => bang_is_free SurfaceRow.disp r

/-- **Finding 3c, the sharp form.** No total-function reading rescues the row:
for a `disposition` of type `RowKey → Disposition`, the row holds of EVERY such
function, including one that answers `excludedInternal` for every public key —
the single assignment `EC1-K07` forbids outright. Neither `EC1-F60` mutation
can be exhibited at that carrier, so the falsifier has no target. -/
theorem T008_holds_of_every_total_disposition
    (disposition : RowKey → Disposition) (k : RowKey) :
    UniqueEq (disposition k) :=
  bang_is_free disposition k

/-! ## §4 — the statement that has content

Two repairs are forced together, and the two mutants of §3 force one each:

* quantify over the KEY UNIVERSE and the LEDGER, not over a function's result
  (the DROP mutant); and
* carry a duplicate-free premise on ledger keys, exactly as `EC1-T002` carries
  one (`PROOF-DAG.md:210`) for the same reason (the DUPLICATE mutant).

The result is an agreement theorem between the universe, the ledger, and the
search — the real obligation hiding behind the word "total". It is the same
move the estate already shipped at `Cas/Schema/Declarations.lean`: a guard
pinning a table map to exactly one function, not a `∃!` on the function. -/

/-- Well-formedness, with each clause named by the mutation it excludes. -/
structure PublicSurfaceWF (s : PublicSurface) : Prop where
  /-- Nothing is dropped: every public key is classified. Excludes §3's
  `droppedSurface`. Shape of `General.row_surjective`
  (`Cas/Schema/Declarations.lean:288`). -/
  covers : ∀ k ∈ s.keys, ∃ r ∈ s.rows, r.rowKey = k
  /-- Nothing is multiply classified. Excludes §3's `dupSurface`. Shape of
  `General.row_inj` (`:297`); forced by `EC1-CE030`. -/
  keysNodup : (s.rows.map (·.rowKey)).Nodup
  /-- `EC1-K07`: "No public exposure may be `excludedInternal`". Shape of
  `General.row_not_dedicated` (`:281`). -/
  publicNotExcluded :
    ∀ r ∈ s.rows, r.rowKey ∈ s.keys → r.disp ≠ .excludedInternal

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

/-- **The existence that is not free.** A classified key is found by the
search. False on `droppedSurface`. -/
theorem dispositionOf_isSome (s : PublicSurface) {k : RowKey} {r : SurfaceRow}
    (hr : r ∈ s.rows) (hk : r.rowKey = k) :
    (s.dispositionOf k).isSome = true := by
  show ((s.rows.find? (fun x => decide (x.rowKey = k))).map (·.disp)).isSome = true
  rcases hl : s.rows.find? (fun x : SurfaceRow => decide (x.rowKey = k)) with _ | e
  · exact absurd (decide_eq_true hk) (List.find?_eq_none.mp hl r hr)
  · rfl

/-- **The uniqueness that is not free.** Under `keysNodup`, every ledger row for
one key carries the same disposition. False on `dupSurface`. -/
theorem disposition_agrees_across_rows (s : PublicSurface)
    (h : PublicSurfaceWF s) {k : RowKey} {r r' : SurfaceRow}
    (hr : r ∈ s.rows) (hrk : r.rowKey = k)
    (hr' : r' ∈ s.rows) (hrk' : r'.rowKey = k) : r.disp = r'.disp := by
  rw [nodup_key_unique (·.rowKey) h.keysNodup hr hr' (hrk.trans hrk'.symm)]

/-- The search agrees with the ledger. -/
theorem dispositionOf_agrees (s : PublicSurface) (h : PublicSurfaceWF s)
    {k : RowKey} {r : SurfaceRow} (hr : r ∈ s.rows) (hrk : r.rowKey = k) :
    s.dispositionOf k = some r.disp := by
  show (s.rows.find? (fun x => decide (x.rowKey = k))).map (·.disp) = some r.disp
  rcases hl : s.rows.find? (fun x : SurfaceRow => decide (x.rowKey = k)) with _ | e
  · exact absurd (decide_eq_true hrk) (List.find?_eq_none.mp hl r hr)
  · have hmem : e ∈ s.rows := List.mem_of_find?_eq_some hl
    have hkey : e.rowKey = k :=
      of_decide_eq_true
        (List.find?_some (p := fun x : SurfaceRow => decide (x.rowKey = k)) hl)
    show some e.disp = some r.disp
    rw [disposition_agrees_across_rows s h hmem hkey hr hrk]

/-- **`EC1-T008`, restated so it has content.** For every key in the recursively
resolved public universe the ledger assigns exactly one disposition, that
disposition is what the search returns, and it is not `excludedInternal`.

Unlike the schematic row this is FALSE on `droppedSurface` and FALSE on
`dupSurface` — which is the point, and which is what makes `EC1-F60` a
falsifier of it rather than of nothing. -/
theorem surface_disposition_exact (s : PublicSurface) (h : PublicSurfaceWF s)
    {k : RowKey} (hk : k ∈ s.keys) :
    ∃ d : Disposition,
      s.dispositionOf k = some d
        ∧ (∀ r ∈ s.rows, r.rowKey = k → r.disp = d)
        ∧ d ≠ .excludedInternal := by
  obtain ⟨r, hr, hrk⟩ := h.covers k hk
  refine ⟨r.disp, dispositionOf_agrees s h hr hrk, ?_, ?_⟩
  · intro r' hr' hrk'
    exact disposition_agrees_across_rows s h hr' hrk' hr hrk
  · exact h.publicNotExcluded r hr (hrk ▸ hk)

/-- The schematic row is a CONSEQUENCE of the restated one, so nothing is lost
by replacing it. -/
theorem restatement_implies_the_schematic_row (s : PublicSurface) :
    ∀ r ∈ s.rows, UniqueEq r.disp :=
  fun r _ => bang_is_free SurfaceRow.disp r

/-! ### §4a — both premises are load-bearing

Each mutant of §3 refutes the restated theorem through exactly one clause. -/

theorem droppedSurface_fails_covers : ¬ (∀ k ∈ droppedSurface.keys,
    ∃ r ∈ droppedSurface.rows, r.rowKey = k) := by
  intro h
  obtain ⟨r, hr, hrk⟩ := h .multipartHeaders (by decide)
  have hsome := dispositionOf_isSome droppedSurface hr hrk
  rw [droppedSurface_really_drops.2] at hsome
  exact Bool.noConfusion hsome

/-- **The coverage premise is necessary.** Without it the existence clause of
`surface_disposition_exact` is FALSE: `multipartHeaders` is a public key whose
disposition the ledger does not carry, and the search answers `none`. -/
theorem coverage_premise_is_necessary :
    ¬ ∀ (s : PublicSurface) (k : RowKey), k ∈ s.keys →
        ∃ d : Disposition, s.dispositionOf k = some d := by
  intro h
  obtain ⟨d, hd⟩ := h droppedSurface .multipartHeaders (by decide)
  rw [droppedSurface_really_drops.2] at hd
  simp at hd

theorem dupSurface_fails_keysNodup :
    ¬ (dupSurface.rows.map (·.rowKey)).Nodup := by decide

/-- **The duplicate-free premise is necessary.** Without it the agreement
clause is FALSE: `dupSurface` declares `.targetOnly` for `succeed`, and the
search answers `.reifiedPrimitive`. This is the `EC1-CE030` repair
(`COUNTEREXAMPLES.md:94` — "add a duplicate-free premise or make row validity
supply it") at the surface-ledger carrier. Contrast §3b: the SCHEMATIC row is
true on this same ledger, which is the whole argument for replacing it. -/
theorem nodup_premise_is_necessary :
    ¬ ∀ (s : PublicSurface) (k : RowKey) (r : SurfaceRow),
        r ∈ s.rows → r.rowKey = k → s.dispositionOf k = some r.disp := by
  intro h
  have hbad := h dupSurface .succeed ⟨.succeed, .targetOnly⟩ (by decide) rfl
  rw [dupSurface_lookup_picks_the_first] at hbad
  exact absurd (Option.some.inj hbad) (by decide)

/-! ## §5 — the "seven-value enum" clause the row does not carry

`REIFICATION-CHECKLIST.md:488` forbids `unknown`, `todo`, `deferred`, and null
dispositions in a closed ledger. The schematic row cannot express that: §1's
proof is indifferent to the codomain, so it holds verbatim of an eight-arm enum
with an `unknown` escape hatch.

What DOES express it is the estate's shipped shape at
`Cas/Schema/Declarations.lean:273-276` — a registry list plus a completeness
theorem whose `decide` FAILS TO BUILD when an arm is added without updating the
list. Three decidable facts pin "seven-value enum" as proved rather than
asserted. -/

/-- Every disposition, in ledger order. Mirror of `General.all` (`:273`). -/
def Disposition.all : List Disposition :=
  [.reifiedPrimitive, .derivedExpansion, .separateSubcalculus,
   .pureOrHostOnlyClosedOutsideProg, .projectOwnedReplacementOrForeignOp,
   .targetOnly, .excludedInternal]

/-- The table is complete. Mirror of `General.all_complete` (`:276`). An eighth
arm added to `Disposition` without extending `all` makes this `decide` fail —
that build failure, not `EC1-T008`, is what keeps `unknown`/`todo`/`deferred`
out of the enum. -/
theorem Disposition.all_complete (d : Disposition) : d ∈ Disposition.all := by
  cases d <;> decide

/-- The table has no repeats. -/
theorem Disposition.all_nodup : Disposition.all.Nodup := by decide

/-- The enum has exactly seven inhabitants. -/
theorem Disposition.all_length : Disposition.all.length = 7 := by decide

/-! ## §6 — the `excludedInternal` clause, separately

`EC1-K07` (`CONTRACT-PACKET.md:224`) states "No public exposure may be
`excludedInternal`", and `REIFICATION-CHECKLIST.md:502` calls the value
"invalid for a key in `U_row`". The schematic row does not carry it; §4's third
conjunct does, and the mutant below shows the clause is not automatic. -/

/-- A ledger that classifies a PUBLIC key as `excludedInternal`. -/
def excludedSurface : PublicSurface where
  keys := [.succeed]
  rows := [⟨.succeed, .excludedInternal⟩]

/-- **Finding 6.** The schematic row is TRUE of this ledger too, so it does not
enforce `EC1-K07`'s exclusion clause either. -/
theorem T008_holds_on_the_excludedInternal_mutant :
    ∀ r ∈ excludedSurface.rows, UniqueEq r.disp :=
  fun r _ => bang_is_free SurfaceRow.disp r

/-- The mutant fails exactly the `publicNotExcluded` clause of §4. -/
theorem excludedSurface_fails_publicNotExcluded :
    ¬ (∀ r ∈ excludedSurface.rows, r.rowKey ∈ excludedSurface.keys →
        r.disp ≠ .excludedInternal) := by
  intro h
  exact h ⟨.succeed, .excludedInternal⟩ (by decide) (by decide) rfl

/-- `excludedSurface` satisfies the other two clauses, so the third is
independent rather than implied by coverage and duplicate-freedom. -/
theorem excludedSurface_covers_and_is_nodup :
    (∀ k ∈ excludedSurface.keys, ∃ r ∈ excludedSurface.rows, r.rowKey = k)
      ∧ (excludedSurface.rows.map (·.rowKey)).Nodup := by
  refine ⟨?_, by decide⟩
  intro k hk
  exact ⟨⟨.succeed, .excludedInternal⟩, by decide, by
    revert hk; cases k <;> intro hk <;> first | rfl | (exact absurd hk (by decide))⟩

/-! ## §7 — the estate has already written down why this row is empty

`Cas/Lift/Taxonomy.lean:12-16`, the module the `Declarations.lean` docstring
names as the shape source for exactly this kind of table, says it outright:

> Totality of `spectrum` is by construction — it is a function on an
> inductive, not a partial map — which is precisely the statement the mirrored
> TypeScript `Record` cannot make for itself.

That sentence is §1 and §3 of this file in the estate's own voice, and it also
says where the content went. In Lean, `disposition` is total because it is a
function on an inductive; the thing that can DROP or DUPLICATE a row is the
generated ledger on the other side of the mirror. `EC1-F60` therefore attacks
the generator and the mirror join, not a Lean function.

The shipped shape for the Lean side is a four-part gate, none of it a `∃!`:
a closed inductive; `RefusalCode.all` (`:208`) with `RefusalCode.all_complete`
(`:215`, twenty rows); an elaboration-time `#guard` that the wire spellings are
`Nodup` (`:220`, mirrored at `Cas/Schema/Declarations.lean:207`); and the
surjectivity/injectivity pair against the registry
(`Declarations.lean:288`/`:297`). §4 and §5 above reassemble that gate at the
surface carrier. `EC1-T008` should be that gate, and the mirror half needs the
same declared-gap discipline `Cas/Lang/RefusalMap.lean:172-176` puts on itself
("this module reads no TypeScript ... the only thing keeping the two in step
today is that they are written down beside each other").
-/

end EffectCoreScoutT008

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT008.bang_is_free
#print axioms EffectCoreScoutT008.T008_as_written_ignores_both_premises
#print axioms EffectCoreScoutT008.T008_needs_no_surface
#print axioms EffectCoreScoutT008.UniqueEq_is_the_probe_spelling
#print axioms EffectCoreScoutT008.droppedSurface_really_drops
#print axioms EffectCoreScoutT008.dupSurface_really_duplicates
#print axioms EffectCoreScoutT008.dupSurface_lookup_picks_the_first
#print axioms EffectCoreScoutT008.T008_holds_on_the_drop_mutant
#print axioms EffectCoreScoutT008.T008_holds_on_the_duplicate_mutant
#print axioms EffectCoreScoutT008.T008_holds_of_every_total_disposition
#print axioms EffectCoreScoutT008.nodup_key_unique
#print axioms EffectCoreScoutT008.dispositionOf_isSome
#print axioms EffectCoreScoutT008.disposition_agrees_across_rows
#print axioms EffectCoreScoutT008.dispositionOf_agrees
#print axioms EffectCoreScoutT008.surface_disposition_exact
#print axioms EffectCoreScoutT008.restatement_implies_the_schematic_row
#print axioms EffectCoreScoutT008.droppedSurface_fails_covers
#print axioms EffectCoreScoutT008.coverage_premise_is_necessary
#print axioms EffectCoreScoutT008.dupSurface_fails_keysNodup
#print axioms EffectCoreScoutT008.nodup_premise_is_necessary
#print axioms EffectCoreScoutT008.Disposition.all_complete
#print axioms EffectCoreScoutT008.Disposition.all_nodup
#print axioms EffectCoreScoutT008.Disposition.all_length
#print axioms EffectCoreScoutT008.T008_holds_on_the_excludedInternal_mutant
#print axioms EffectCoreScoutT008.excludedSurface_fails_publicNotExcluded
#print axioms EffectCoreScoutT008.excludedSurface_covers_and_is_nodup
