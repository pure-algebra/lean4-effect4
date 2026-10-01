H2 can go: nothing the probe found changes the exit judgment's shape, provided the service table enters the typed state as a static component of the world (the TREE seat's shape A) and the shape-defect clause reads only the core `Defect` alphabet and the frame's requirement row; the model's direction stands and R1 still belongs before the M5–M7 proofs (about 22–26 mechanical declarations plus three admission rules, after item G), but R2's "extension is additive" is false as written and R1–R9 ask only that a program stays typed and safe, so the note needs the revisions below before it is folded into the system map.

# The full-program model, probed: synthesis

Status: research synthesis, 2026-09-30. Read at HEAD `7cae243a` on `refactor/phase1-phase3`; the
coordinator's uncommitted edits to `docs/STATE.md`, `docs/core/decisions.md` and
`docs/core/system-map.md` (rows 95, 96 and 110 landed, H2 held) were read as they stood at 22:40.
Nothing tracked was edited. This is the only file this seat wrote under `docs/research/`.

**What it reconciles.**
- The note under review: [`2026-09-30-full-program-model-requirements.md`](../2026-09-30-full-program-model-requirements.md)
  ("the note"), R1–R9.
- Four seats and their adversarial verifiers, in this folder:
  [completeness](completeness/note.md) + [verify](completeness/verify.md) (findings C-01…C-17),
  [pedigree](pedigree/note.md) + [verify](pedigree/verify.md) (P1…P17),
  [TREE](TREE/note.md) + [verify](TREE/verify.md) (TREE-01…16),
  [programs](programs/note.md) + [verify](programs/verify.md) (PROG-1…15, X1…X11).
- The cited sources, wherever two seats or a seat and a source disagree.

**Counting rule.** A seat finding counts only if its verifier confirmed it or partly confirmed it;
"(partly)" marks where this synthesis leans on a partial verdict, and says which part. A verifier's
own new finding is cited as "verifier", with the verifier's evidence word.

**Evidence words.** *Proved*: a kernel theorem at `[propext, Quot.sound]` or less, with the seat
that ran it named. *Tested*: a finite check run by the seat named. *Reading*: read in code or
notes, not run. *Assumed*: not checked. This seat reran seven of the load-bearing probes through
the lock (§7); everything else it states is reading.

Short paths: `Program/…`, `Machine/…`, `Laws/…`, `Api/…`, `Codegen/…` are under `src/Effect4/`;
research notes are named by date and title and live in `docs/research/`.

## 1. For the owner

**Is the requirements model robust?** Its direction is. Programs as the free object over an open
signature, behaviour as a function of the decision tape, typing as a protocol per operation over a
world, and requirements written as theorem shapes: the research behind each holds at HEAD, and every
seat probe reran with the same output under its verifier. As written, the model is not yet robust,
for five reasons.

1. **Two terms it rests on are undefined.** "Every lawful Σ" and "Σ ⊆ Σ′" name nothing in the tree.
   Lawfulness is four separate checks today (C-02, C-03, confirmed).
2. **"Extension is additive" is false as written.** It holds only under conditions, and today
   several fail (proved or tested, §2.2):
   - a row inserted in front re-points every call; the same bytes then call a different row and
     still check;
   - a service declared at a key the built-in table already types retypes old programs;
   - a declaration at the machine's reserved memo-map key types a program at `nat` that finishes
     with a memo-map handle;
   - a fresh service key changes an old program's printed TypeScript, which stops reading back until
     row 105 lands;
   - appending a lawful but unregistrable row revokes admission of programs that never call it;
   - the typed state is not monotone in the row table.
3. **It asks only that a program stays typed and safe.** Nothing asks what a program does: the
   behaviour of composed library modules, the release of resources, frontiers and deadlock, and the
   faces as named connections (C-01 partly, C-05 partly, C-06 partly, C-07 confirmed).
4. **Several of its supports are wrong or superseded** (§3.2): `interpret_pinned` is uniqueness, not
   additivity; `Ψ_S ⊕ Ψ_F` no longer builds the concrete typing judgment; the fiber layer has no
   handler; `build_total` was proved in the tree and cut, not "proved in the workshop only"; the
   soundness theorems need no restatement.
5. **It does not cite the rulings that already decide parts of it:** DI-47, DI-69, DI-89, DI-22,
   DI-64, DI-39, DI-91, DB-15, DB-01's coherence clause, row 79's R79.1–R79.5, the owner's
   2026-09-07 ruling on derived forms, and the 2026-09-10 Config route.

**What changes.**
- **R1** names the open part of the signature, Σ_app = the row table and the service table, and
  defines "lawful" as one decidable check. Cells and records leave Σ: they are the type language's
  growth, owned by the core.
- **R2** becomes eight named conservativity conditions (C1–C8). Each is proved, tested or owed, and
  each failure above is one of them.
- **Four requirements are added:** R10 (library code inherits theorems), R11 (resources are
  released), R12 (frontiers name what they await; deadlock, liveness and divergence) and R13 (a run's
  load inputs). R8 becomes "runs and faces as named connections".
- **R6 drops "state the host premise now".** M6's premise is a predicate on tapes, landed as item B.
  The host lane brings its own conditions when it unparks.
- **The order holds** (§5). R1 for services comes before the M5–M7 proofs. Generic cells come before
  M6's store cases, as `decisions.md`'s order already rules. Nothing is owed for hosts now.

**H2, held for this synthesis** (row 107; addendum 4). The answer is **go**. No requirement here
changes the exit judgment's shape, on two conditions (§5.1):
- the service table enters the typed state as a static component of the world (shape A), not as a
  parameter of the value judgments;
- the shape-defect clause is stated over the core `Defect` alphabet and the frame's requirement row,
  with no signature parameter.

**What the owner decides.** Thirteen proposed rows in §6. The ones that gate the next brief:
- D1, Σ_app as R1's parameter;
- D2, shape A;
- D3, service keys by code;
- D4, the three admission rules for declared services;
- D6, the domain bit in the host-row protocol entry.

## 2. The revised requirements

### 2.1 What a full program is, corrected

The note's §2 says a full program is a closed term over `Σ = Σ_core ⊕ Σ_app`, run against a host
`H`. That stands, with four corrections.

- **Σ_core is closed inductives the language owns:** the `Eff` and `Ty` constructors, the built-in
  `NativeOp` rows, `SyncOp`, `FiberOp`, `NativeAtom`, `Err`, `Defect` and `HandleKind`. It grows by
  constructor appends under DI-47's compatibility gate over the retained baseline
  (`Test/fixtures/baseline/66ee4657/`) and the wildcard and inventory rules of rows 56 and 61. That
  is a finite gate and a discipline, not a theorem (pedigree verify §2 item 9; P16, confirmed).
- **Σ_app is data an application supplies:** today the row table and the service table. Later, and
  only if admitted, nominal data declarations and code entries (R3, R7).
- **Cells and structural records are not in Σ.** A cell at any type is typed by the world's `Ρ`/`Π`
  at allocation (row 44); the generic rows are core template rows (rows 42–43 plan §2b: "a row is a
  function of the operation's data"). Records and variants are growth of the type language
  (type algebra §1.3). Σ needs a declaration table only for nominal or recursive types
  (C-08, confirmed; pedigree §3.1).
- **`H` is the tree's own host specification:** `HostSpec`, five relations over an abstract host
  state (`Program/Profile.lean:178`), lawful by `LawfulHostSpec` (`:198`, DI-65), not a new notion.
  The empty relation is "no host" (C-11, confirmed).

A run of a full program also has **load inputs** (configuration, seed: R13), and a program may
have **several roots** (host-started work: §6, D12).

### 2.2 The requirements

Shapes are proposals; none is claimed. `Σ` is an admitted Σ_app, `p` an admitted program, `t` a
tape, `H` a lawful host specification.

#### R1. The signature is a parameter, and "lawful" is one decidable check (revised)

```lean
structure AdmittedSig (Σ : SigApp) where   -- runtime data, every law a Prop field (charter rule 7)
  lawful : LawfulSig Σ
def admitSig : (Σ : SigApp) → Except SigRefusal (AdmittedSig Σ)   -- refusal located at a row or key
theorem admitSig_ok_iff : (admitSig Σ).isOk = true ↔ LawfulSig Σ  -- decided by the kernel (rule 2)
-- and every milestone statement takes (hΣ : AdmittedSig Σ), for example
theorem typedState_load (hΣ : AdmittedSig Σ) (hp : AdmittedProgram Σ p) : TypedState Σ p (loadR p …)
```

**`LawfulSig`'s clauses** already exist as checks or rulings; the requirement is to gather them
behind one located refusal and prove it complete.
- Row names unique: `LawfulTable` (`Codegen/Read.lean:1943`).
- Rows registrable: `checkTable` (`Program/Native.lean:322-352`).
- No `int`: the admission scan (`Program/Admission.lean:100-106`; DI-67).
- No internal handle kind in a host row's answer or error: row 97, item A, in flight.
- No open template variable in a host row (pass synthesis K10).
- Templates admissible and well scoped (`templateAdmissible`, `Row.wellScoped`,
  `Laws/Program/Template.lean:268`, `:288`).
- Every key a row requires has a service type (author receipt C3).
- **New, for declared services** (D4): no name below `firstFreeName`
  (`Machine/ContextMap.lean:787`); no carrier that conflicts with the built-in table; flat carriers
  only (`unit`, `nat`, `bool`, `string`, a non-context handle) until structured carriers are ruled.
- The reader's `LawfulSpelling` (`Codegen/Read.lean:892`).

The start exists: `Table.checkLawful` and `LawfulRefusal` give a located refusal by key
(`Program/Table.lean:76-97`). But `admitProgram` has a fallback arm that invents a key when
`Table.lawful` fails and `checkLawful` finds nothing (`Program/Admission.lean:123`, read by this
seat), and no theorem ties the two checks. `admitSig_ok_iff` must close that first (completeness
verify §2 item 8).

**Status, by layer.**
- **Typing: proved over any signature.** `check_sound` and `check_complete`
  (`Laws/Program/Typing/CheckSound.lean:37`, `:361`); 188 explicit `(sig : Signature` binders
  (tested by three seats).
- **Admission: pinned.** `AdmittedProgram` at `nativeSignature table`
  (`Program/Admission.lean:89-90`, `:108`, `:191`).
- **Typed state: pinned in 13 places,** not ten, in four modules (tested, TREE verify). They come
  by two routes:
  - the source route: `ProgramSource` and its readers, plus `ForkSource` at the empty table;
  - the value route the note missed: `ServicesOk` reads `nativeServiceTy` itself
    (`Laws/Program/Typed/Admission.lean:32-34`, read by this seat). Item E renamed it
    `ServicesFit`, still on `nativeServiceTy`, typing flat carriers only (TREE-01 partly, TREE-02
    confirmed; completeness verify §2 item 3).
- **Meaning, loop and run soundness: no restatement needed.** Their fragments exclude every host
  row and every service form. `meaning_typed_any`, `run_typed_any`, `meaningB_typed_any`,
  `run_sound_any` and `run_soundB_any` carry them to any table and service list (proved, TREE
  `R2Probe.lean`; rerun by its verifier and by this seat). Row 21, receipt C2 and ledger 4B
  overstate the cost (TREE-06, confirmed).
- **Faces: pinned.** `Laws/Codegen/{Admit,Checked}.lean` and `Laws/Api/ModuleReadable.lean`
  take `nativeSignature table`: 22 lines (P6 confirmed; pedigree verify §2 item 10). Restating K2
  for services needs row 105 first (C7 below).
- **Agreement: unaffected by services.** `run_eq_ref` takes no signature and no premise
  (`Laws/Program/RuntimeR.lean:211`, read by this seat), so services do not touch it. Host rows
  need DI-57.

**Sources.** Author receipt C2 (`2026-09-17-seat-author-receipt.md` §6); ledger 4B; rows 21 and 90;
the rows 42–43 plan §2c, slice L7 ("the six type codes … become a service table beside the program,
as the row table is"), which is R1's earliest statement and which the note does not cite (TREE-11,
partly: the plan's dependency of L7 on L6 is for the printer half only); TREE §2;
completeness A1.

**Change from the note.** Σ is (rows, services). Lawfulness is defined. The two missed routes are
named. "`MeaningSound` and `LoopSound` follow" becomes "carry over by corollary".

#### R2. Extension is conservative under named conditions (revised)

An **extension** `ε : Σ ⊑ Σ′` is DI-47's relation applied to Σ_app: declared appends only; no
reorder, removal, reframing or tag reuse; positions in the link table (DI-22); receiver-qualified row
identity (DI-64); fresh names, meaning not reserved and not typed by Σ_core. Applying DI-47 to Σ is
the seats' extension of a ruling written for the world description and the wire (C-03, confirmed).
A **Σ-program** is one whose every operation is in `dom Σ` and whose every key at a position the
checker looks up is typed by Σ (pedigree verify P2).

| | Condition | Status |
| --- | --- | --- |
| C1 syntax | `ι*` is an injective monad morphism of free monads | proved: in the package for binary sums (`Program.inl_bind`, `inl_injective`, `Effects/Algebra/Sum.lean:72`, `:92`); for any signature morphism (`along_bind`, pedigree `Conservativity.lean`). In-tree witness: `denoteR_straight` uses `inl_bind` six times (`Laws/Program/DenoteR.lean:1422-1534`; P1 partly) |
| C2 meaning | `interpret h′ (ι* p) = interpret (h′ ∘ ι) p` | proved: `interpret_inl` (package), used by `meaning_via_rsig` (`Laws/Program/Sched.lean:237`); `interpret_along` (pedigree probe). **For host rows there is no free-monad instance until DI-69 lands** (`RowSig`, unimplemented), so the owed form is operational: an old program's run against an appended table is its run against its own table. Tested on one program; refuted for insertion (pedigree verify `VerifyRun.lean`) |
| C3 checker | for a Σ-program, `check Σ′ p = check Σ p` | monotone half proved: all six judgments and the checker at every path are preserved along `SigExtends` (`hasTy_ext` … `check_ext`, `rows_append`, `services_append` with freshness; TREE `R2Probe.lean`, 38 theorems, rerun by its verifier and by this seat). Red controls proved: `prepend_not_extends`, `shadow_not_extends`. Reflection owed: one more induction, the sibling of `hasTy_restrict_looped` (proved for looped programs) |
| C4 protocol typing | `Typed_Σ′ w′ Q′ (ι* p) ↔ Typed_Σ (π w′) Q p` | proved for the generic judgment, both directions and both injections (`inl_iff`, `inr_iff`, `typed_along`, `typed_pull_of_typed`, `typed_of_typed_pull`; composed as `c4_iff`, pedigree verify). **Owed for `TypedProg`**, its own inductive since the slice-5 ruling (P3, confirmed). For the row table it needs C3 in both directions (P17, partly) and the domain bit in the host-row entry: without it `TypedProg` is not monotone in the table (`typedProg_not_table_monotone`, proved, TREE verify; TREE-08) |
| C5 world | the new world projects onto the old by a monotone map with the back condition; new protocols refine the old ones (demand forward, promise backward); the old components' order is not widened | each premise has a proved red control: `reflection_needs_back`, `order_widening_loses_typing`, `post_refinement_needed` (pedigree), `mono_needed`, `pre_refinement_needed` (pedigree verify). `World.leHost` has admitted allocation growth since its first commit, `cd769650` (P9, confirmed) |
| C6 local lawfulness | `LawfulSig Σ′ ↔ LawfulSig Σ ∧ Fresh ε ∧ LocalLawful (new entries)` | shape only. For a row, local lawfulness is `LawfulTable` ∧ `checkTable` ∧ the `int` scan ∧ item A's scan: an append that `LawfulTable` accepts revokes admission of an old program (tested, pedigree verify `VerifyAdmission.lean`). For a service: not reserved ∧ no conflict ∧ flat (D4) |
| C7 representation | old bytes and text read back unchanged | **rows:** holds only if module assembly appends (`Package.install` prepends, `Program/Authoring/Services.lean:186-187`, tested) or a stored program travels with its link table (DI-01's recorded default; DI-05; DI-22). The same bytes under a reordered table call a different row and still check (tested, completeness verify §3). **services:** fails for a fresh key until row 105 lands: the key's printed spelling changes and the old text stops reading (tested, pedigree verify `VerifyServiceFace.lean`) |
| C8 forms (new) | a form's expansion lies in the readable image | a form adds nothing to Σ, so C1–C7 say nothing about it (PROG-1, partly). The seat's retry form types but cannot be printed and read back: its loop needs a cursor annotation, which DI-91 makes unreadable by design (tested, programs verify X3). The alternative is DI-91's fallback (a), which needs a written amendment to B19 |

**Status per extension point.**
- **Host rows, by append:** C1–C3 proved or tested. C4 is owed for `TypedProg` and needs D6. C7 is
  conditional on D5.
- **Services, by fresh, unreserved, flat codes:** C3 proved. C6's rule is to be written. C7 waits
  for row 105.
- **Core alphabets:** DI-47's finite gate, not a theorem. The bill for a new `Ty` constructor at
  HEAD: 63 matches read `Ty`, 25 with no catch-all (tested, programs verify `VerifyTyBill.lean`;
  PROG-15 partly: row 61's "22 of 51" is the 2026-09-19 figure and counts definitions, not proofs).
- **Structural records and generic cells:** not extensions of Σ (§2.1).
- **Forms:** C8, plus R10's obligations.
- **Equations,** the charter's third kind of extension: none is declared today. C1 and C2 are free
  only because `Eff` and the algebra carry no equations (coherence principle §1). If the fiber layer
  gains its deferred theory, conservativity of a sum of theories is the question of Hyland, Plotkin
  and Power 2006, which nobody in the tree has read (assumed; P14, confirmed).

**What the two parts buy.** R1 alone saves re-proving: a generic proof is reused. C1–C8 make the
statement stable: the Σ′ instance of a theorem says of an old program exactly what the Σ instance
said (pedigree §3.1).

**Sources.** End-state §8 and §10 (the charter's *Extensible*); DB-01's last paragraph ("Any
explicit signature map or universe lift requires its own contract and coherence laws"); DB-05 (a
separate summand); DI-47, DI-69, DI-22, DI-64; coherence principle, literature (Swierstra 2008;
Cartwright and Felleisen 1994: "rows as extension points … the shape the layers steer wants");
pedigree §3; pedigree verify §3; completeness A2.

**Change from the note.** Drops `interpret_pinned` (uniqueness) and `Ψ_S ⊕ Ψ_F` as the support.
Replaces "status per extension point" with C1–C8. Adds C8.

#### R3. Data: one amendment of DB-15 (revised)

**Shape.** The type language is closed under structural records and variants: a mutual
`Ty`/`Fields` spine, with `Ty.foreign id args` as the nominal form (type algebra §1.3). Each new
constructor brings:
- its `Fits` clause ("every `Ty` constructor has its clause", host-boundary §4.4);
- its exact embedding to Schema and JSON (K2);
- folds generated from the signature;
- assignability agreement with the target's compiler (row 68);
- inhabitance, DI-67 restated over `Fits`: `∀ admitted τ, τ.normalize = never ∨ ∃ w v, Fits w v τ`.

**Status: refused by a settled decision.** DB-15 refuses three things: a record type in `Ty`
("columns are pairs"), a `json` leaf, and any inhabitant of `int` (`docs/DESIGN-BASIS.md:664-666`).
DI-62 and DB-15 refuse `Err.value`, because a handle inside a cause would extend the minted-handle
invariant into causes. Row 2 is open, with a staged recommendation: annotation-carried names now
(c), and `Ty.record`/`Ty.variant` (b) before the first foreign consumer. The note's "the design is
ready" is a recommendation, not a decision (P12, confirmed; C-12, partly: "named" follows row 2's
title and implies nothing nominal).

**What real programs need** (tested by the programs seat, rerun by its verifier):
- records in all five programs;
- a structured error payload read by four of them (PROG-7, partly: p4 has no handler);
- signed numbers in p5: `sub 10 25` runs to 0 where rc.112 answers −15 (PROG-9, partly: this is
  DB-15's explicit `int` refusal, not a new extension point);
- a decode route for JSON answers in p1 and p2 (PROG-5, partly: DB-15 governs it; the other route,
  typed `Eff` holes, is already W9's next deliverable, post-Phase C §11.2).

**Also owed with records:**
- collections with a fixed key, duplicate and order policy (machine-state §5; DI-78);
- equality, `Val.eqAt` (DI-35);
- recursive types, which no register row covers (tested by grep, three seats). JSON bodies need
  them.

**Sources.** DB-15; DI-62; DI-67; row 2; type algebra §§0–1, §8; language cut §§2–3, §6 (a dated
snapshot); post-Phase C §11.2, W1 ("arbitrary error payloads need the existing basis ruling
amended, not silently enabled").

**Change from the note.** R3 is stated as the DB-15 amendment it is. Payloads, `int`, decoding,
collections and equality join it. Recursive types get a row (D10).

#### R4. State: generic cells, in the core (kept; status corrected)

**Shape.**
- The world types every cell at any type: `Ρ key = some A`, `Π key = some (A, E)`.
- The rows become templates (row 42).
- A row that takes a function takes a binder term, evaluated at `env ++ [current]` (row 43).

**Status.**
- **The world model: ruled and defined, not "proved".** Row 44 is a ruling. The world is defined
  at every type (`Laws/Program/Typed/World.lean:52-57`), and its order laws are proved
  (`:394-406`). M5 and M6 over it are `#proof_wanted` (TREE-12, confirmed).
- **Steps 1–2 landed; steps 3–5 open.**
- **Until then, row 96's sub-decision D2 reads the native spellings as cells declared at `nat`.**

**The cost of step 3 is wider than the TREE seat's "eight read-modify-write arms"** (TREE-10,
partly). The reference machine applies `syncOpOf`, whose `refMake` and deferred decodes take `nat`
only (`Laws/Program/DenoteR.lean:507`, `:599`, `:934`, `:947`, `:1203`). Rows as templates also
change the checker facts that every Ref and Deferred perform case of M5/M6 reads. `FnName` is in 51
tracked non-documentation files, most of them generated (tested, TREE verify).

**What real programs need** (tested by the programs seat):
- p3's `Deferred<void>` gate types the whole program at error `nat` where rc.112 says `never`
  (PROG-8, confirmed, with a red control);
- p4's atomic admit is unsayable, and its read-then-update spelling races, `[5, 0]` under a yield
  (PROG-12, confirmed).

**Sources.** Rows 42–45, 55; rows 42–43 plan §§1, 2a–2e; catalogue §3 items 1–2.

**Change from the note.** Cells leave Σ_app. "Proved (row 44)" becomes "ruled and defined".

#### R5. Services, joined to retained behaviour by a capture law (revised)

**Shape.**
- The service table is part of Σ_app (R1).
- In the typed state it is a static component of the world, fixed by the order; `ServicesFit`
  reads `w.serviceTy` (shape A, D2).
- Declared keys obey D4.
- A layer's value fits its key's type (row 105).
- Contexts typed per row 90; requirement rows grade programs.
- **The context satisfies every requirement row already discharged above a frame** (row 51,
  "`ServiceOk` context-wide"). This is the service-presence argument H2's part two needs. Its natural
  lemma is the provision algebra's adjunction, `satisfies_iff_subset_keysRow`
  (`2026-09-04-provision-algebra.md` §2; reading).

**Owed, from settled pieces.**
- **Build totality.** `build_total` and `buildAll_total` were proved in the tree at `f182d2b3`,
  over any signature, and cut at `b08f3b58` with "no consumer, 175 lines"
  (`docs/core/traversal-census.md:433-436`). The module docstring still advertises them
  (`Program/Provision.lean:35-41`). R5 is their consumer: restore them (tested by `git log -S`,
  three verifiers; C-14, P5 and TREE-13; X10).
- **`lower_refines_build`** (provision algebra §3, owed since 2026-09-04).
- **Reference keys and Config:** `KeyKind := service | reference`, provision algebra §6, and the
  2026-09-10 Config route (R13).
- **Minted keys that a term cannot spell** (`PROV-FB-KEY-FORGERY`; papers review G5).
- **Validation of contexts at any runtime-to-`Fits` bridge** (side audit, `ContextBridge.lean`).
- **Scope elimination is implemented, not pending:** the checker's `scoped` arm discharges the scope
  key through `bodyRequires` (`Program/Checker.lean:198-200`, read by this seat). The basis's proof
  graph still says "pending" (stale; §3.3).

**Code-valued services.** An ordinary rc.112 service is a record of operations built by a layer
(`Context.ts:177-180`). Three things follow:
- **R5 cannot stand without R7.** The coupling is already in post-Phase C §11.2 (W2: "W4 for retained
  behavior"; W4: "invocation/captured services, … Cache") and in row 82 (PROG-2, partly).
- **The capture law has a run-time half.** rc.112 uses two capture policies: a layer's closure keeps
  what it read at build time (`[1, 2]`), and `Cache.makeWith` runs `lookup` under the creation
  context merged under the caller's (`[2, 7]`). Both were tested on rc.112 by the programs seat and
  rerun by its verifier, with a red control.
- **It also has a typing half.** `Cache`'s `requireServicesAt` moves a lookup's requirement between
  construction and use, so R5's requirement rows must say where a code-valued service's requirements
  are paid (verifier, X8; reading of `Cache.ts:199-204`).

**Sources.** Rows 21, 51, 90, 104, 105; the provision algebra §§1–3, §6, §10; DB-12; DI-20, DI-28;
author receipt C2–C3; papers review A1, G5.

**Change from the note.** The threading moves to R1. Five owed pieces are named. R5 and R7 are
joined. Row 105 and D4 become preconditions.

#### R6. The host (revised: no premise now)

**Shape.** `H : HostSpec` with `LawfulHostSpec` (§2.1). When the lane unparks it brings:
- **receipt and application theorems** (host-boundary §4.5), with the converse it owes on the
  admitted profile: every semantically valid, representable reply is accepted;
- **the table-aware reference relation,** DI-57's `session_eq_ref`, of which `run_eq_ref` becomes
  the empty-table corollary;
- **the row table's algebraic meaning,** DI-69's `Sum StoreSig (RowSig table)`. This is C2's
  instance for rows; until it lands, C2 for rows is the operational clause;
- **a world extension that meets C5** (pedigree §3.5; P9, confirmed). C5 covers today's steps only.
  A host-answer step is new, and needs §4.5's application theorem however the world is extended
  (pedigree verify P9).
- **Retirement as an event of the protocol.** Retirement is not silent: `Run.Observation.retired`
  crosses the boundary (`Run.lean:215-232`), and at-most-once application is proved
  (`applied_reply_refused`, `Laws/Api/HostSession.lean:219-224`). What is missing is narrower
  (PROG-3, partly; verifier, X6):
  - a retirement edge in the protocol's labels (`Api/HostProtocol.lean:16-26`);
  - a lemma that a retired key is never applied;
  - a declaration per row of whether the row takes a cancellation. rc.112's notice is opt-in per
    call site: `tryPromise` makes the `AbortSignal` only when `try` takes it, and `callback` only
    when `register` takes two arguments (`internal/effect.ts:1088`, `:1169`, `:1131-1133`).
- **Inbound entries** (several roots): an owner choice, D12.

**Status.** Parked by the owner on 2026-09-30, except row 97's interim rule (item A, in flight). Of
the interim rule, neither the table scan nor the reply-value check is at HEAD (TREE-14, partly).

**Why no premise is stated now** (verifier, X7). M6's capstone counts reference-machine tapes in
which no decision is a host answer (row 95, landed as item B). It names no host relation, and its
extension hook is `decision_preserves`'s `AnswerOk`. The lane can define `H` with its whole event
alphabet (call, reply, retirement, the per-row cancellation option) when it lands, without restating
M6. The note's §5 item 3 ("state the host premise now") is therefore unnecessary.

**What real programs pay.** Three of the five programs call a host; by the programs seat's own
mapping p5's `Effect.callback` is a host row too, so four. They get:
- typing;
- the session's laws for the envelope, receipt, at-most-once application and protocol conformance
  (`Laws/Api/HostSession.lean`);
- the runner's K5 laws.

No agreement theorem reaches them. `run_eq_ref` covers their runs only at the empty table, where
they stop at the first host call (tested, programs verify §1b; PROG-6, partly).

**Sources.** host-boundary §§1–6; rows 95–101; DI-57, DI-58, DI-65, DI-69; DB-03, DB-09 (DI-65
amendment); lit-papers Q6–Q7 (Loring, Marron and Leijen, *Semantics of Asynchronous JavaScript*
§2.4, `E-Oracle`; Xia et al. §7, read there).

**Change from the note.** `H` is `HostSpec`. "State the premise now" is dropped. C5, the converse,
retirement and inbound entries are added.

#### R7. Retained behaviour, as a theorem shape (revised)

```lean
theorem resolve_typed (hΣ : AdmittedSig Σ) :
    resolve Σ ref = some (entry, caps) → HasTy Σ caps.types entry.body (τ ref)
-- plus: the typed state extended to stored behaviours, with their lifetime
```

- **Signature and capture layout are fixed at resolution:** "a digest alone does not"
  (machine-state §5).
- **Invocation context is chosen by the module's contract** (the two rc.112 policies of R5).
- **Code identity is either allocation or structure.** rc.112 removes a listener by object identity
  (`l !== listener`, p5), so either entries are allocated as handles or the profile states the
  difference.

**Status.** Open (row 82: "lifting the entire machine Capture record is not the design"). The
narrow form recommended by catalogue §5 Q4 is one value shape, one type former and one row that runs
it.

**Pedigree.**
- Lit-papers Q12: Danvy and Nielsen, *Defunctionalization at Work*, §1 and §3, read there. A
  `Capture` is closure conversion over a first-order code pointer; a callback is a term if it is pure
  and flows to the continuation, and a program at a `Point` if it can be deferred (van den Berg et
  al. §2.2).
- Lit-papers Q1: Xie and Leijen, *Generalized Evidence Passing* §2.12.1. Static dictionaries are
  unsound once a resumption can run under another handler context, so admitting code-valued services
  flips Q1 (C-10, confirmed; PROG-2, partly).

**Change from the note.** A representation choice becomes a theorem shape, with capture and
identity named.

#### R8. Runs and faces as named connections (revised; replaces the note's R8)

```lean
theorem face_F (hΣ : AdmittedSig Σ) (hp) (ht : t ∈ Profile_F.tapes) :
    (obs_F (run_F p t) = ρ • obs (replay Σ H p t))    -- inside the profile
  ∨ RefusedByProfile F p t                          -- outside it, intermediate values included
```

- **`ρ` is one partial bijection on identities,** extended by first appearance (DI-81). Equality
  relations between identities must agree (dogfood conclusions §8).
- **The profile is data, as R79.5 rules.** Its `direction` field (equal, included or both) is fixed
  per profile, not globally (`2026-09-20-open-design-issues-order-and-observation-packet.md` §2.5).
  The direction the programs seat proposes, every rc.112 observation being some model observation,
  is its reading, not row 79's text (PROG-13, partly).
- **The stages are lcnf-route §8's eight connections and seven rules,** and the numbers are DI-56
  with row 108's two side-audit additions (store functions; refusal outside the result).
- **K2 holds on the readable domain, and that domain must be stated.** A program with a retry loop is
  outside it today (C8).
- **Runs are the K5 action.** `journal_replays` is proved, but about `Run` (`Laws/Run.lean:184`).
  The note attributed it to row 98, whose typed replay route is still open (C-09, confirmed).

**A face difference no register row names.** A singleton `mergeAll` layer that compares fiber
identities answers `false` in Lean and `true` on rc.112. It is the dogfood conclusions' §2 finding
(D-E), still `false` at HEAD (tested, completeness verify `VerifyRun.lean` §4; rc.112's side is
reading of that note's evidence). It needs a register line.

**Status.** No face has a theorem beyond the printer and reader laws and the fragment simulations;
typed lowering is pending (DESIGN-BASIS proof graph). The duties are already owned by lcnf-route §8,
system map §5 and row 101, so R8 copies them into the requirement list (C-07, confirmed). It does not
redesign them.

**Change from the note.** The OCaml entry path is a feature that host-boundary §4.6 already owns, so
it leaves the list. The journal attribution is corrected.

#### R9. Never goes wrong (kept; stated so that no signature can reopen it)

```lean
-- the lane's `badDefect` (Test/Program/ExitTypeLane.lean:34-37), lifted into the proof graph:
-- it reads a reason's `Defect` (a closed core alphabet, Machine/Alphabets.lean:45-56) and
-- `ty.requires`, and nothing of Σ_app
def NoShapeDefect (ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure c => ∀ r ∈ c.reasons, badDefect ty r = false
def ExitOk (w : World) (ty : EffTy) (ex : ExitV) : Prop := FitsExit w ty ex ∧ NoShapeDefect ty ex
-- read at every typed position: TypedProg's pure arm and exit-carrying posts, saved stacks,
-- queued finish and observe commands, stored completions (addendum 3, item H2)
```

**Status.** Ruled (row 107), with its placement amended by the side audit (`E4-TYPED-CE-007`). H2
was held for this synthesis; §5.1 gives the answer.

**"Never halts" is not part of this clause.** That a typed run never halts on
`Stuck.unknownFiber`, `unknownScope` or `unknownRace` (row 52) is already M7's separate corollary,
beside "no wrong-shape internal decoder failure" (post-Phase C §I). The completeness seat's request
(C-15, confirmed) is met by naming it there.

**Change from the note.** The clause is written over Σ_core, so "for every Σ" holds by construction.
M7's progress corollary is cited.

#### R10. Library code inherits theorems (new)

**The rule.** A composed module (a DI-89 form, or a DI-11 composite such as a queue) is its
expansion. Its law is stated about the expansion, on a named profile:

```lean
-- R79.1, R79.5: a coarser or finer view is a projection that Factors to Obs; the profile is data
theorem M_agrees (hΣ : AdmittedSig Σ) (h : Σ_M ⊑ Σ) (hp : p uses M) :
    Agrees (profile M) (module M) (expand p)
-- a compiler c : Model → Eff, whose models are data (charter rule 6), returns a Verified bundle:
theorem c_bundle (hm : m.WellFormed) : typeOf Σ (c m) = some (τ m) ∧ Means Σ (c m) (spec m)
```

**Each form owes six things** (PROG-1 partly; programs verify X1–X3; dogfood conclusions §7):
1. a typing lemma over any argument typing;
2. one behaviour law on a named observation, against the rc.112 function it transcribes;
3. scope safety, which is free (`authoring_scoped`; `timeoutForm_scoped` and `retryForm_scoped`
   proved by the programs seat, with the red control `leaky_not_scoped`);
4. reader admission: the idiomatic spelling reads back only to an expansion that meets 2;
5. a readable expansion (C8);
6. a stable identity, under the owner's 2026-09-07 ruling (D9).

**A composed module also owes the six-piece contract of post-Phase C §11.4.** That includes a
satisfiability witness and one discriminating counterexample.

**The proof route is a stuttering relation.** It is not `Projects`/`Refines`, which relate one
concrete step to one model step (`Laws/Machine/Refinement.lean:20-37`). machine-state §7 says
stuttering simulation is "not provided automatically" (C-01, partly). lcnf-route §8's third rule
applies: a step that becomes several needs a bound or a progress measure.

**The fidelity a module owes is already ruled** (R79.5): "values relative to the decision tape; a
schedule deviation is a named refusal row". The completeness seat's question, from catalogue §5 Q1,
predates that ruling (C-01, partly).

**Status.**
- No form in the tree has a behaviour law (reading; PROG-1).
- The 19 forms of `Codegen/Forms.lean:89-124` include none of DI-89's named list.
- DI-39 ruled six forms rows on 2026-09-09: `catchTag`, `catchTags`, `catchIf`, `mapError`,
  `orElseSucceed`, `match`. None has landed, and the ingest engine refuses `catchTag` as `E-HANDLER`
  (`ts/eff/ingest/ck.ts:938`; X2).
- Every one of the five programs uses at least one DI-89 form. `timeout` is W6's, not on DI-89's
  list (programs verify, PROG-1).

**Sources.**
- DI-89, DI-11, DI-39; row 79 (R79.1–R79.5); post-Phase C §11.2–§11.4; machine-state §5
  ("typing is not enough"); catalogue §3, "the trade-off"; dogfood conclusions §7, D-G.
- The charter's *A base for higher-order APIs* (end-state §10).
- Bach Poulsen and van der Rest, *Hefty Algebras*, §1.2 and §3.4: inlined elaborations are not part
  of any effect interface (lit-papers Q2, read there).

**Why it is added.** "What a program does" had no requirement. Six of the thirteen module families
have none: transactions, time, streams, observability, collections and pure protocols (C-01,
partly: the duty itself is already ruled by DI-89 and row 79).

#### R11. Resources are released (new; the completeness seat's A4, corrected)

```lean
theorem release_atMostOnce (hΣ) (hp) : ∀ r, releaseRuns (replay Σ H p t) r ≤ 1
theorem closed_released (hΣ) (hp) (hs : closedIn (replay Σ H p t) s) :
    ∀ r ∈ registered s, releaseRuns (replay Σ H p t) r = 1 ∧ inCloseOrder s
theorem frontier_retains (hΣ) (hp) (h : (replay Σ H p t).outcome = .frontier) :
    ∀ s, openIn (replay Σ H p t) s → retained s   -- AGENTS.md: state kept for finalization
```

**Scope of the guarantee.** It is stated over closed scopes and structured regions: `scoped`, a
layer's scope, a race. It includes ownership of forked fibers and managed-runtime disposal. DB-07
lists these: "finalizer registration and order, exactly-once close, interruption masking, fiber
ownership, scheduler decisions, and managed-runtime disposal".

**Two corrections to the completeness seat's A4.**
- **"A finished run released every registered finalizer" is false.** A release registered in a
  `Scope.make` scope the program never closes does not run, and the run finishes (tested,
  completeness verify `VerifyRun.lean` §1). rc.112 behaves the same way: finalizers run only in
  `scopeCloseUnsafe`, and `scopeMake` links no parent (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3779-3797`,
  `:3915-3926`; reading by the verifier). So a scope a finished run leaves open is an observation,
  not a violation (D8).
- **Release must be counted, not written.** The seat's probe wrote `1`, which reads the same after
  two runs; a counting release shows exactly once (tested, completeness verify).

**Status.** Universal theorems exist for one close: `runState_complete`, `runState_restore` and
`runState_result` (`Laws/Machine/ScopeMachine.lean:191`, `:217`, `:233`). There is no whole-run
theorem (C-05, partly).

**Sources.** DB-07; the DESIGN-BASIS proof graph's "Scope and runtime" edge; DI-65 ("terminal
observation requires completed cleanup and ownership discharge"); host-boundary §4.2. The owner
ruled the frontier half on 2026-09-07 (grill agenda §3, call 9): open scopes are reported, not
closed, and an `abandon` operation runs the finalizers. That ruling is in an untracked note (§4.3).

**Why it is added.** No requirement covered release, and real programs rely on it: p3's three
workers close their connections on interruption (tested on rc.112 and on the Lean session by the
programs seat).

#### R12. Frontiers name what they await; deadlock, liveness, divergence (new; A5 corrected)

```lean
def Deadlocked (m : Machine) : Bool    -- every live fiber parked; nothing armed; no host call or timer
theorem deadlocked_fixed (h : Deadlocked m) (hd : ¬ d.isInterrupt) : stepDecision d m = m
theorem frontier_named (h : outcome = .frontier) : reasons ≠ [] ∨ Deadlocked m   -- INV-TAPE-2
theorem row_live (hfair : FairTape interp fuel m t) : Eventually P (replay … t)   -- per named row
```

**The completeness seat's `noReason_deadlocked` is false** (proved, completeness verify
`VerifyKernel.lean`). A root parked on its own `yieldNow` under the tape `[evaluate]` has no
frontier reason, `Api.Tape.Complete` holds for that tape, and one `flush` finishes the run. All
three theorems are `[propext, Quot.sound]` (reproduced by this seat, §7).

The cause is a proved law: `awaitDecision` appears exactly when some fiber is unparked
(`awaitDecision_iff`, `Laws/Api/Frontier.lean:13`). `frontierReasons` never reads `m.armed`
(`Api/Frontier.lean:47`, read by this seat). So armed dispatcher work is invisible to the frontier,
and a tape the API calls complete can still owe a decision.

**The research already defined deadlock with the dispatcher idle.** Papers review G6 has "dispatcher
idle", and core math §9 defines deadlock as "no fair tape advances it". So `Deadlocked` requires
`m.armed = []`, and the frontier alphabet needs a reason that names armed owners (D7).

**Liveness and divergence.**
- Liveness stays relative to a fairness hypothesis (DB-03), through `FairTape`
  (`Laws/Machine/Scheduling.lean:432`).
- Divergence adequacy is "pending" in the basis's proof graph. DB-03 rules that divergence is
  witnessed by an infinite run or by compatible finite prefixes, never by fuel. Servers and event
  loops are full programs, so telling "a frontier at every budget" from divergence is owed
  (completeness verify §2 item 9).

**Start from the existing laws:** `observe_of_reasons` (`Laws/Api/Frontier.lean:82`) and
`Sched.reasons_eq_ref` (`Laws/Program/ReasonsR.lean:223`).

**Sources.**
- Papers review G6–G7; core math §9 (Lee, Cho, Song, Hur et al., *Fair operational semantics*,
  PLDI 2023, as that note gives it).
- Lit-papers Q7: INV-TAPE-1 (no off-tape choice) and INV-TAPE-2 (a frontier records what it
  awaits), after Xia et al. §7, read there. Neither is in any tracked file yet (tested by grep,
  completeness verify), so both need a row before anything cites them as rules (D7).

#### R13. A run's inputs are data (new; the programs seat's P4, partly)

**Shape.** A run is identified by:
- the program;
- its profile and link table;
- its budgets;
- its tape;
- its load inputs: the environment snapshot and the seed. The clock is not one: it is already a
  tape decision (DB-14), and a custom clock is refused by name until row 83 rules otherwise
  (completeness verify, C-04).

Its meaning is a relation over the load inputs as over the tape.

**Status: designed, not implemented** (PROG-4, partly: the design exists in sources the seat did not
cite).
- The 2026-09-10 Config route B puts the environment snapshot "in the tape header beside the row
  table". That note's own decisions, its D1–D5, are pending (`2026-09-10-config-path.md` §3–§4,
  untracked).
- The header that would carry it exists (`Api/HostSession.lean:23-28`).
- `Program/Config.lean` §6 already gives a configuration's requirement row.
- Row 51 provides the root's requirement row at load. Row 83 and catalogue Q7 put the seed at load.
- The research's run identity already has profile and budget: a job is program, profile, fuel and
  tape (`2026-09-07-cas-design.md`); dogfood conclusions §7 says the same.

**What changes when Config lands: M5's `typedState_load`,** which loads with no inputs
(`Laws/Program/Typed/Assembly.lean:148-150`). It can ride the same `ProgramSource` restatement as R1,
as a defaulted field, when Config is first needed. Not M6 (verifier, X5).

**Real programs:** p2 reads `ADMIN_TOKEN` once per process. A run after the variable is deleted
still succeeds; a fresh process without it fails with `ConfigError` (tested on rc.112 by the programs
seat, with a red control, and rerun by its verifier).

### 2.3 Removals, merges and moves, with their reasons

| From the note | Now | Reason |
| --- | --- | --- |
| R1's Σ lists "data" and "cells" | removed from Σ | cells are core template rows typed by the world; structural records are `Ty` growth (C-08, confirmed) |
| R2 "rows: additive by construction … `interpret_pinned` and `Protocol.sum` are per operation" | replaced by C1–C8 | a host row is not an operation of `RSig`; it goes through `FiberOp.async` (`Laws/Program/Sched.lean:105`; TREE-04, confirmed). `interpret_pinned` is uniqueness (P1, partly). Insertion and override break it (proved and tested) |
| R2's per-point status list | replaced by C1–C8's status | it repeated §4's table and R1, R4, R5 (C-03, confirmed) |
| R5's threading | moved to R1 | one requirement owns the signature |
| R6 "parking is sound if the premise is stated now" | removed | M6's premise is a tape predicate; the lane's obligations are C5 and §4.5 (X7; P9, confirmed) |
| R7 "take typed first-order code references" | restated as a theorem | it was a representation choice (C-10, confirmed) |
| R8 "the OCaml engine needs a table-aware keyed entry path" | moved to host-boundary §4.6 | a feature; that document already owns it |
| R8 "numbers follow DI-56 (row 108)" | merged into R8's face clause | one face requirement |
| R8 "the run API is the K5 action … (row 98): `journal_replays` is proved" | corrected | `journal_replays` is about `Run`; row 98 is open (C-09, confirmed) |
| §5 item 1: "`MeaningSound` and `LoopSound` follow" (restated) | no restatement | proved corollaries (TREE-06, confirmed) |
| §5 item 3: the host premise | removed | as R6 |
| — | R10, R11, R12, R13 added | what a program does, its resources, its frontiers, its inputs (§2.2) |

### 2.4 The five real programs against the requirements

The programs seat wrote five rc.112 programs. All five type-check with the pinned `tsgo` and run on
rc.112 under bun 1.4.2, and the expressible parts run in Lean: tested by the seat, rerun identically
by its verifier, each with a red control. What each needs, by requirement:

| Program | Needs, in order of what stops it first |
| --- | --- |
| p1, HTTP call with `retry`, `timeout`, a typed error and a `Cache` | R10: the forms, and a readable retry; R3: a numeric payload (`status`) and JSON decoding; R5 + R7: `Cache` keeps code; R6: the call's retirement notice is opt-in |
| p2, request handler over layered services and `Config` | R5 + R7: `UserRepo` is a record of methods, with a capture policy; R13: `Config` read once per process; R1: a `string` carrier is refused today (`serviceCarrier … signature none`; PROG-11, confirmed); R3: records, payloads, decoding |
| p3, workers draining a queue, cleanup on interruption | R4: a list cell, and `Deferred<void>` typed at error `nat`; R10: `Queue` as DI-11's composite, with its law; `forEach`; R11: release on interruption |
| p4, dogfood 1's rate limiter | R4: a record cell and an atomic `Ref.modify` (binder terms); R10: `all`. Host-free, so `run_eq_ref` reaches it today and M5–M7 will |
| p5, a stateful service with callbacks | R3: records, variants, signed numbers; R7: listeners as values, removal by identity, `callback`'s cancel effect; R6, or the logical clock (X11) |

The note's §8 cites the dogfood notes as sources, but the dogfood briefs and batteries were never
committed, and two of the three idiomatic dogfood files are not rc.112 programs: they use
`Effect.forkDaemon`, `Context.Tag` and `Schedule.intersect` (PROG-10, confirmed). These five
programs, with their rc.112 runs, are the witness set R1–R13 can name, once they have one tracked
fixture owner, which the dogfood conclusions asked for (§7: "choose one fixture-definition owner").
Today they live only in this gitignored folder.

### 2.5 The counterexample register against the requirements

`Test/Counterexamples/REGISTER.md` has 153 live rows (tested by grep, this seat and the completeness
verifier). The 32 frozen packets in `Test/contracts/` are the other authority neither the note nor
the seats mapped (completeness verify §2 item 10). By id family (tested by grep, this seat; the
mapping is reading):

| Family (live rows) | Requirement |
| --- | --- |
| `SCHED` (14), `TYPED` (3), `RESID` (2), `DEN` (5), `SEM` (7), `PROGRESS` (2), `LIVE` (2), `BEH` (2), `APPROX` (4) | R1 and R9 (the milestone), R12 |
| `PROV` (4), `ENV` (6) | R5 |
| `HANDLE` (3), `STORES` (4), `D6` (1, the register's own family name) | R4 |
| `HOST` (5) | R6 |
| `SCHEMA` (28), `DATA` (9) | R3, and R8's K2 |
| `RUN` (31), `CAS` (8), `CONF` (6), `TARGET` (2) | R8 |
| `CHECK` (2), `CORE` (1), `RTERM` (2) | R1, typing |

Row by row, the mapping is owed with each requirement's contract. post-Phase C §11.4 asks each
contract for "the one discriminating counterexample", and these rows are where they come from.

## 3. The design basis, with its pedigree

### 3.1 Components and requirements, traced to the research

"At HEAD" uses three words: **holds**; **superseded** (a later ruling or landing replaced it, named);
**corrected** (the citation was wrong, and the right one is given). Literature carries the word its
citing note gives it: **read** (the section was read in this tree, by the note named) or **by name**
(cited without a section, not read here).

| Component or requirement | Established in | Literature | At HEAD |
| --- | --- | --- | --- |
| Level 0: the free monad, typed by a protocol per operation | M1 kickoff §3; the composed graph (`2026-09-18-typed-state-composed-graph.md`) §4; foundations review §4.3 | Xia et al., *Interaction Trees*, POPL 2020, §3.2, §7 (read, lit-papers Q7, Q10); de Vilhena, thesis 2022, Def. 2.2, 2.4–2.8 and rule Monotonicity (read, papers review §1.3 and the pedigree seat) | **holds** for the generic `Typed` (`Laws/Effects/Protocol.lean:45-120`). **Superseded** for the concrete judgment: `TypedProg` is its own inductive since the slice-5 contract ruling of 2026-09-23 (`Laws/Program/Typed/Residual.lean:186`; P3, confirmed). **Corrected:** the kickoff maps `Typed.mono` to Hazel's Monotonicity; Monotonicity is `Typed.widen` plus protocol refinement (`typed_along`), and `Typed.mono` is world-order weakening, the Kripke and Iris upward closure (by name) (pedigree verify §2 item 7) |
| Level 1: the world `⟨ids, state, Γ, Π, Ρ, Θ⟩` and its order | M1 kickoff §2.2, §3; slice 2 (Θ); rows 44–45; `heapNotMonotone` | de Vilhena §4.3; MCA §4.1.1; Jacobs Prop. 6.2.4 (read, papers review A3); Ahmed 2006 and Iris (by name, foundations review §4.1) | **holds** (`World.lean:52-57`; `World.le` `:131-136`; `leHost` with `Extends` since `cd769650`). The foundations review §2.4's strict-equality `leHost` was never in the tree (P9, confirmed) |
| Level 2: the typed stack, one delivery lemma | rows 48 and 86; slice-5 landing | Danvy and Nielsen, *Defunctionalization at Work*, 2001, §1, §3 (read, lit-papers Q12); Reynolds; Van Horn and Might (by name) | **holds** (`popR_typed`, `deliver_active`, `deliver_stale`) |
| Level 3: the store as comodel, the machine as runner | core math §7; M1 kickoff §3; row 41 | Plotkin and Power 2008; Ahman and Bauer, ESOP 2020 (by name) | **holds as a reading** (`storeHandler`, `Laws/Program/Denote.lean:124`) |
| Operations are algebraic; meaning is initial | end-state §8 | Plotkin and Power 2002/2003; Plotkin and Pretnar, *Handling Algebraic Effects* §1, §5 (read, lit-papers Q11); Goguen, Thatcher, Wagner and Wright 1977 (coherence principle, literature) | **holds** (`program_is_free`, `program_is_initial_in_models`, `interpret_pinned`, package `Universal.lean:98`, `:119`, `:243`). `interpret_pinned` is uniqueness: it is not R2's support (P1, partly) |
| Control is scoped syntax, elaborated | end-state §8; core math §§5–6; DB-05; DI-12 | Wu, Schrijvers and Hinze 2014; Piróg et al. 2018; Bach Poulsen and van der Rest 2023; van den Berg et al. 2021 (read, lit-papers Q2) | **holds** for "elaborated into `denoteR`". **Corrected** for "and a handler for fiber control": `fiberRefusal` is "Not a semantics" (`Laws/Program/Sched.lean:216-218`; `E4-SCHED-CE-001`). The error began in end-state §8; the tracked statement is `Sched.lean`'s header, `:33-39` (P4, partly) |
| Behaviour is a function of the tape | core math §2; DB-03; lit-papers Q7 | Jacobs ch. 2, Moore coalgebras (read, papers review §1.4); Xia et al. §7, Def. 1–2 (read, lit-papers Q7); Chappe et al., *Choice Trees*, §2.2 (read, lit-papers Q7) | **holds** (`Beh`, `Beh_fuel_irrelevant`, `Laws/Machine/Behaviour.lean:74`, `:92`). INV-TAPE-2 is broken at HEAD: armed work is invisible to the frontier (R12) |
| Partiality is a budget | core math §3; end-state §2.2, §8; row 41 | Capretta 2005; Chapman, Uustalu and Veltri; Hasuo, Jacobs and Sokolova 2007 (by name, core math); Jacobs Thm. 5.3.4, Prop. 5.3.3 (read, papers review §1.4); Elgot 1975; Adámek, Milius and Velebil 2006 (by name, coherence principle) | **holds, by another construction**: `iter` and `denoteB` beside `denote`, joined by `denoteB_straight`, with `denoteB_mono` and `meaningB_unique` (`Laws/Program/Iter.lean`, `DenoteB.lean:208`, `:285`, `:386`, `:496`). End-state §4.2's "a parameter of the one `denote`, changed in place" is **superseded** by the build-in-parallel rule (P15, confirmed) |
| Protocols compose by coproduct | composed graph §4; foundations review §4.3 | **corrected:** the review cites Plotkin and Pretnar 2009 and Bauer and Pretnar 2015 for "the coproduct of algebraic theories"; the sum of theories is Hyland, Plotkin and Power, TCS 357, 2006 (by name only, never read in the tree), and coproducts of signatures with injections are Swierstra, *Data Types à la Carte*, JFP 2008, §2, §6 (read by the pedigree seat) (P14, confirmed) | **superseded** for the concrete judgment (slice-5 ruling). The generic lemmas hold and now have both directions (`c4_iff`, proved). The review's claim that `Typed.inl` and `Typed.inr_inv` protect the complementary half does not reach `TypedProg` (P3) |
| Services and layers are one row calculus | provision algebra §§1–3, §6, §10 (landed `f182d2b3`); papers review A1; DB-12; DI-20, DI-28; rows 51, 90, 104, 105 | Burckhardt et al., *Durable Functions*, OOPSLA 2021, Thm. 5.3, 6.4; Lamport and Merz, *Prophecy Made Simple*; Kuessner et al., ECOOP 2023 (as provision §7 gives them); de Vilhena Tes §7.3 (read, papers review); Leijen on row polymorphism (read, lit-papers Q4); Wand, Rémy, Gaster and Jones, Morris and McKinna (assumed, type algebra §8) | **holds** for the row laws (`provide_closed`, `merge_rows_comm`, `Program/Provision.lean:98`, `:138`). **Corrected:** `build_total` was proved in the tree and cut (`b08f3b58`); the docstring at `:35-41` is stale |
| Faces: exact embeddings and simulations | coherence principle §§1–4; system map §5; `AGENTS.md` vocabulary (row 36); lcnf-route §8 | Goguen et al.; Rendel and Ostermann; Matsuda and Wang; Foster et al.; Pickering, Gibbons and Wu; Rutten; Lynch and Vaandrager; Leroy (by name, with their uses, coherence principle) | **holds** on the readable domain (`read_print`, `read_exact`); that domain excludes annotated loops (DI-91, B19) |
| A run is data (K5) | coherence principle §2; M1 kickoff §4 | free monoid action (standard); CompCert labels; CakeML's FFI oracle (by name) | **holds** (`replay_unique`, `Laws/Api/Runner.lean:157`; `journal_replays`, `Laws/Run.lean:184`) |
| R1 the signature as a parameter | author receipt C2; ledger 4B; rows 21, 90; rows 42–43 plan §2c, L7; DI-54, DI-61 | signatures as data: Benke, Dybjer and Jansson 2003; Chapman et al. 2010 (by name, coherence principle §1) | typing **holds** over any signature; the rest pinned (R1) |
| R2 conservative extension | end-state §10 (*Extensible*), §8; DB-01, DB-05, DB-10; DI-47, DI-69, DI-22, DI-64; the coherence principle's literature list (the layers steer's shape); REIFICATION-STRATEGY RS-4 | Swierstra 2008 §2 (read: the injections "may no longer be the right injection"); de Vilhena Def. 2.4, 2.8 and Monotonicity (read); Tes §7.3, distinct labels (read); modal p-morphisms (assumed) | **corrected**: not by construction; C1–C8 (R2). The layers steer's own sentence, that composition "needs a lawful `Signature.append`", is only in session memory; its shape is tracked (`docs/core/coherence-principle.md:552-553`; P13, partly) |
| R3 data | row 2; DB-15; DI-15, DI-62, DI-67; type algebra §§0–1 | Lean 4.33.1 deriving facts F1–F6 (read at the toolchain lines, type algebra §0); the record literature (assumed, type algebra §8) | refused by DB-15 (P12, confirmed) |
| R4 state | rows 42–45, 55; rows 42–43 plan; catalogue §3 | Hoare Type Theory, Nanevski et al. (by name, foundations review §2.1); declaration-site variance from rc.112's own declarations (row 60) | world **holds**; rows open |
| R6 host | host-boundary; rows 95–101; DI-57, DI-58, DI-65 | Loring, Marron and Leijen §2.4 (read, lit-papers Q6); Xia et al. §7 (read) | parked |
| R7 retained behaviour | row 82; catalogue §3 item 5, §5 Q4; machine-state §5 | Danvy and Nielsen §1 (read, Q12); van den Berg et al. §2.2; Bach Poulsen and van der Rest §2.6.4 (read, Q2); Xie and Leijen §2.12.1 (read, Q1) | open |
| R8 faces | lcnf-route §8; row 101; DI-49, DI-56, DI-81; row 108 | CompCert's contract shape; graded Freyd categories (Power and Robinson; Levy, Power and Thielecke; Katsumata; Orchard et al.; by name, coherence principle §4b) | partly |
| R9 never goes wrong | rows 52, 107; pass synthesis §2.4 part 6; side audit §2 | — | ruled; H2 |
| R10 library code | DI-89, DI-11, DI-39; row 79 (R79.1–R79.5, packet §2.5); post-Phase C §11.4; dogfood conclusions §7 | Plotkin and Pretnar §5: a law is an equation of the declared theory, discharged per clause (read, lit-papers Q11); Bach Poulsen and van der Rest §1.2, §3.4 (read, Q2) | ruled, undelivered. Lit-papers Q11's default, "laws only where an optimization relies on one", is **superseded** by DI-89's one behaviour law per form (PROG-14, partly) |
| R11 resources | DB-07; DI-65; the basis's "Scope and runtime" edge; grill agenda §3 call 9 (ruled 2026-09-07: "open scopes are *reported* in the receipt, not closed"; an `abandon` runs the finalizers) | `EStateM.run_throw` (DB-07); Sivaramakrishnan et al. §3.2 on what a stopped run leaves open (read, lit-papers Q3) | one close proved; whole run open |
| R12 frontiers, deadlock, liveness | papers review G6–G7; core math §9; lit-papers Q7 | Lee, Cho, Song, Hur et al., *Fair operational semantics*, PLDI 2023 (as core math §9 gives it); de Vilhena §4.1, "Deadlock"; Jacobs §6.9 (read, papers review) | open |
| R13 load inputs | config path (2026-09-10) §§3–4; provision algebra §6; rows 51, 83; catalogue §5 Q7; CAS design (2026-09-07) | — | designed |

### 3.2 Pedigree corrections, in one list

Each is a claim in a research note or a tracked file that a basis row must not inherit.

1. **M1 kickoff §3:** "`Typed.mono` is his Monotonicity rule". The right mapping is in §3.1, level 0
   (pedigree verify §2 item 7, reading of the thesis text).
2. **Foundations review §4.3** misattributes the sum of theories, and its claim that `Typed.inl` and
   `Typed.inr_inv` "guarantee that adding new store operations … never invalidates the complementary
   half" no longer reaches `TypedProg`. An inversion is not a lift (P3, P14, confirmed).
3. **Foundations review §2.4** quotes a strict-equality `leHost` that only a plan had
   (`2026-09-20-m1-evidence/phase-b/proof-plan/PhaseCWorldPlan.md:74`). §7.2 item 5 states
   `TypedProg` as `Typed (World.le) (Ψ_S + Ψ_F)`, which is superseded twice (pedigree verify §2
   item 12).
4. **End-state §8:** "a handler for the control signature (the scheduler)". Contradicted by
   `fiberRefusal` and `E4-SCHED-CE-001` (P4, partly). Its own "honest boundary" sentence is right:
   the fiber layer is algebraic in representation and operational in meaning.
5. **End-state §4.2 and §9 item 4:** the budget as "a parameter on the one `denote`, changed in
   place". Superseded by `denoteB` beside `denote` with a connector (P15, confirmed).
6. **End-state §10, the charter's *Extensible* status cell:** "true of the algebra by construction
   … `interpret_pinned` is stated per operation". This is where the mix-up starts (TREE-04,
   confirmed). The additivity lemmas are `interpret_inl`, `inl_injective` and `inl_bind`.
7. **`Program/Provision.lean:35-41`:** `build_total` "is proved once over the algebra". It was cut
   at `b08f3b58`. The note's "proved in the 2026-09-04 workshop spike only" is wrong too (C-14,
   partly; P5, TREE-13, confirmed; X10).
8. **Findings ledger 4B, author receipt C2 and decisions row 21:** threading the service table
   "changes … both soundness statements (stated at `nativeSignature table`)". They are stated at the
   empty table and need no restatement (TREE-06, confirmed, proved).
9. **The note's "ten places … mostly through `ProgramSource`".** There are 13, and five do not go
   through `ProgramSource` (TREE-03, confirmed).
10. **The note's §1:** the world as `⟨Γ, Π, Ρ, Θ, s⟩` cites the kickoff, which has `⟨Γ, Π, Ρ, s⟩`.
    Θ came with slice 2, and `ids` is a field too (pedigree §1.3).
11. **Catalogue §5 Q1** (the fidelity a module owes) predates R79.5, which rules its default (C-01,
    partly).
12. **Lit-papers Q2 and Q9** leave the identity of forms open. The owner ruled it on 2026-09-07:
    stored expanded (grill agenda §3, call 1; applied in `2026-09-07-join-dispatch.md`). It was
    challenged on 2026-09-08 ("store the term", `2026-09-08-effectful-repository-notes.md` §6). All
    three notes are untracked, so the ruling is unrecorded, not open (X1).
13. **Lit-papers Q11's** "laws only where an optimization relies on one" is superseded by DI-89
    (PROG-14, partly). Its Q3 supports reporting open scopes at a frontier, not notifying a host of a
    retired call (programs verify, PROG-3).
14. **`docs/core/language-cut.md`** is a dated snapshot by its own header. Its atoms are now 33, and
    Config has an algebra.
15. **The DESIGN-BASIS proof graph:**
    - `run_eq_ref`'s cell lacks "empty table only";
    - finite adequacy is called "single-fiber straight-line only", but `loopAgreement` covers
      `Looped`;
    - scope elimination is called "pending", but the checker discharges the scope key
      (`Checker.lean:198-200`, read by this seat) (P10, partly).
16. **The DESIGN-BASIS primary sources** list Xia et al. and Chappe et al. The pedigree seat's
    "none of these is listed" was wrong; the rest of its missing list stands (P10, partly).

### 3.3 The DESIGN-BASIS refresh

The basis was last changed on 2026-09-20 (DB-14's clock amendment). Nothing from the charter, rows
41–110, the typed state, the protocols, the budgeted meaning or `Fits` has reached it (P10, P11,
partly).

**The row shape** (pedigree §4.2), the same for every row:
- the decision, in today's names;
- its witnesses, as theorem and `file:line` at a stated commit, with tests named as tests;
- its refusals, with register ids;
- its sources, by path and section, marked tracked or untracked;
- its literature, marked read, by name or assumed;
- a status line, and the commit at which a coordinator last re-read the witnesses.

| Row | Verdict | Action |
| --- | --- | --- |
| DB-01 `Program` is the proof carrier | stands; stale wording (pins `v0.1.0`; the pin is `v0.8.0`, `a4ee7a14`, `lakefile.toml:126-131`) | **amend** with R2's C1–C8 and the Σ_core/Σ_app split. Its last paragraph already asks every signature map for "its own contract and coherence laws", so C1–C2 are those laws (pedigree verify §2 item 8). Add the caveat on sums of theories (HPP 2006, assumed). DI-90's in-tree move stays a pointer |
| DB-02 `Flow` | superseded, as marked | keep. Its rule that pure code is closed at the boundary lives in `AGENTS.md` and is R7's pedigree |
| DB-03 meaning is relational | stands; stale wording ("judgments over `Flow`") | amend: `Beh` and the tape. Host answers as decisions (row 95); a pointer to host-boundary; INV-TAPE-1 and INV-TAPE-2 once D7 rules them |
| DB-04 fuel is an approximation | stands; receipts archived | amend: the budgeted meaning (`iter`, `denoteB`, `denoteB_straight`, `meaningB_unique`, `soundB`, `loopAgreement`), with its Elgot, Capretta and Jacobs pedigree |
| DB-05 no `HHandler` for first-order children | stands; stale wording (`BlockId`) | amend: the honest boundary, operational fiber meaning (`E4-SCHED-CE-001`; `Sched.lean:33-39`) |
| DB-06 EffHOL is the logic layer | stands as a constraint | none; the logic edge is empty (DI-10) |
| DB-07 state survives failure | stands; stale wording (`EStateM`; the tree uses `ExitV` with `StateT`) | amend: point to R11 as the theorem its last paragraph asks for |
| DB-08 `Expr` is input only | stands | none |
| DB-09 Effect TypeScript is a profile | **conflicts** with system map §1: "OCaml native is a test bed" against "the model runs natively … through LCNF" | the system map owns the route; DB-09 keeps ProfileData, HostSpec, Binding and the evidence classes |
| DB-10 PolyFun is prior art | stands; stale wording | read `Eff` for `Flow` |
| DB-11 one value carrier | stale: "the executable admission is owed to X2" | amend: `admitProgram` (DI-61) and reply admission exist; value typing is rows 44 and 96 (`Fits`) |
| DB-12 one context, layers by path | stands | amend when items F and G land: rows 104, 105 |
| DB-13 one wake protocol | stands; wording ("Latch, Queue … as they land") reads as one store per family against DI-11 | amend the wording only (pedigree verify P10: weaker than first stated) |
| DB-14 one logical clock | stands | none |
| DB-15 strings are machine values | stands; **blocks R3** | the R3 amendment (D10) when it is ruled |
| new DB-16: typing as a protocol per operation over a world | settled by rows 44–45, 48, 86, 87, 96 and the slice-5 ruling | add: generic `Typed` and concrete `TypedProg` sharing certificates; the world order and antitone typing; coarse values with `Fits`. Literature as §3.1, levels 0–2, with item 1's correction |
| new DB-17: the requirement row calculus | settled by the provision laws (landed `f182d2b3`), DI-20, DI-28, rows 51, 90, 104, 105 | add, with `build_total`'s cut and its restoration under R5 |
| "Semantic decomposition" | superseded | retire to a dated history appendix |
| "Native library boundaries" | **conflicts** with DI-11 and DI-89 | retire; DI-89 owns how modules enter (restated in machine-state §5) |
| "Required proof graph" | stale, and a second owner of status (§3.2 item 15) | retire; the system map owns status |
| "Primary sources" | stale | one bibliography, built from §3.1's literature column with its read, by-name and assumed marks |

## 4. Consolidation: one owner per fact

### 4.1 Where each fact lives

The rule is to fold into the existing owners. No new document is needed.

| Fact | Owner | What moves there |
| --- | --- | --- |
| What a full program is: Σ_core, Σ_app, `H`, load inputs, roots | `docs/core/system-map.md` | a short §2.1-style paragraph beside §4's sorts |
| The requirement list R1–R13, with status | `docs/core/system-map.md`, one table under §5 (or a new §8) | one line per requirement: the shape's name, its status, the document that owns its detail, its workstream, its counterexample family. **Status lives here only** |
| Settled decisions, with their pedigree | `docs/DESIGN-BASIS.md` | DB-01's amendment (C1–C8, once D1 is ruled); DB-16; DB-17; the amendments to DB-03, DB-04, DB-05, DB-07, DB-11, DB-12, DB-13; DB-15's when D10 is ruled; one bibliography |
| Open questions | `docs/core/decisions.md` | the rows of §6. Row 21's consequence is corrected: threading does not change the soundness statements. Row 107: the H2 answer. Row 96's "structured carriers wait on the synthesis": D4 |
| Open design issues | `docs/DESIGN-ISSUES.md` | none new. The 2026-09-07 forms ruling is transcribed under DI-89 (D9) |
| The host lane's added obligations | `docs/core/host-boundary.md` §4.2, §4.5 | C5 for the world extension; the retirement edge and its lemma; the per-row cancellation declaration; inbound entries (D12). All parked, written down |
| Resources, frontiers, module contracts | `docs/core/machine-state.md` §5, §7 | R11's statements and D8; R12's armed-owner reason (D7); R10's stuttering route and the six obligations of a form |
| Faces and stages | `docs/core/lcnf-route.md` §8 | C8 (a readable expansion), as a rule for the printer stage |
| Data requirements | post-Phase C §11.2, W1 (already listed there) and DB-15 (the ruling) | nothing new. `language-cut.md` stays a dated snapshot and is not extended |
| Coverage planning | post-Phase C §11 | each workstream names its requirement in the system map's table; no second map |
| Counterexamples per requirement | `Test/Counterexamples/REGISTER.md` | the dogfood §2 merged-layer identity row (R8); the reserved-name, `FlatFits`, per-code and `asyncPre` fixtures from TREE verify, once landed as tests |
| Small fixes found on the way | the coordinator | the stale `build_total` docstring (`Program/Provision.lean:35-41`); the stale system-map line that still calls row 96 open (§4, "Value fits type"); the `daemon` keyword, which breaks `{ … daemon := … }` for `ForkOptions` in every module importing `Effect4.Api.Author` (`Program/Authoring/Services.lean:151`; tested, completeness verify §2 item 13) |

### 4.2 Research notes that become cited history

Cited by section from the basis rows and the system map's table, never copied:
- the note under review, this synthesis, and the four seat notes and verifications;
- end-state §8 and §10;
- the composed graph §4 and the slice-5 contract ruling;
- the M1 kickoff §§2–4, with §3.2 item 1's correction;
- the foundations review §4, with items 2–3;
- core math §§2–3 and §§7–9;
- the papers review §1.3, §1.4, G5–G7, A1 and A3;
- lit-papers Q1, Q2, Q3, Q7, Q11 and Q12;
- the provision algebra §§1–3, §6, §7 and §10;
- the type algebra §§0–1 and §8;
- the rows 42–43 plan §§1 and 2a–2e;
- the catalogue §§3 and 5;
- the grill agenda §3;
- the config path §§3–4;
- the dogfood conclusions §§2, 7 and 8;
- the observation packet §2.5 (R79).

### 4.3 The tracking problem

A ruling counts only once it is written into a tracked file (DESIGN-ISSUES' header), and
`docs/research/` is gitignored. These notes carry pedigree or rulings and are untracked (tested with
`git ls-files`, this seat):
- the end-state note (the charter);
- core math;
- the papers review;
- lit-papers;
- the provision algebra;
- the two dogfood notes;
- the grill agenda: the owner's fifteen rulings of 2026-09-07, including calls 1 and 9;
- the config path;
- the algebra-package review;
- the effectful repository notes;
- the CAS design;
- the join dispatch;
- REIFICATION-STRATEGY;
- brief addendum 4.

The tracked note under review cites five of them.

**Recommendation (D13):**
- force-add the eight that hold rulings or the literature reads: end-state, grill agenda,
  provision algebra, config path, core math, the papers review, lit-papers, dogfood conclusions;
- carry each cited claim into its basis row, with its literature line, so the basis stands without
  them.

Both follow `AGENTS.md`'s authority map ("the notes that matter are force-added"). They also follow
the way the 2026-09-19 design push landed: `docs/core/machine-state.md`, with its source notes
tracked (the stateful catalogue is). Force-add only the notes, never their evidence folders: the
directory is 2 GB.

## 5. Feasibility and order

### 5.1 Codex's queue now: H2 can go; nothing else changes

**The H2 question** (row 107; addendum 4) is whether the probe changes the exit judgment's shape. It
does not. The argument is reading, step by step:

1. **H2's judgment.** It is `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex`, read at
   every typed position (addendum 3, item H2, step 2). Its parameters are a world, an effect type
   and an exit.
2. **The shape-defect clause reads only the core.** It refuses `badName`, `notImplemented`, and
   `missingService` when the frame requires nothing (`badDefect`,
   `Test/Program/ExitTypeLane.lean:34-37`). These are constructors of `Defect`, a closed core
   alphabet (`Machine/Alphabets.lean:45-56`). `missingService` carries no key, so "requires nothing"
   reads only `ty.requires`. Nothing of Σ_app enters.
3. **`FitsExit` reads Σ_app in one place only:** the context arm, through `ServicesFit`, which reads
   `nativeServiceTy`. At HEAD that is `ServicesOk` (`Laws/Program/Typed/Admission.lean:32-34`,
   `:57`). In the design item E implemented it is `ServicesFit`, the only Σ_app read in
   `2026-09-30-pass/membership/Fits.lean` (`:90`; the other "tables" there are the world's
   declaration tables). Both read by this seat; Codex's landed module was not read.
   - Under shape A, R1 changes that body to read `w.serviceTy`, and the parameters of `FitsExit`
     and `ExitOk` stay as they are.
   - Under shape B, both gain a service-table parameter. H2's measured edits (eight existing
     bodies, seven from slice 5 and one E adapter) would then be redone, along with the B chain's
     59 statements and 15 bodies (tested count, TREE verify).
4. **No other requirement touches the exit judgment.**
   - R11 and R12 are statements about runs.
   - R6 does not touch M6 (X7).
   - "Never halts" is M7's separate corollary (R9).
5. **A future amendment to R3 would touch the cause clause, not the exit's shape.** Admitting
   `Err.value` (D10) would change `FitsCause`'s failure arm and item A's handle-freeness of
   failures. That is exactly why DI-62 refuses it today, and it is owed by that amendment.
6. **Part two of H2,** `missingService` moved outward across frames, needs a service-presence
   argument. That is row 51's context-wide `ServiceOk`, and its natural lemma is the provision
   algebra's adjunction `satisfies_iff_subset_keysRow` (§2, reading). Addendum 3's rule stands:
   land part one; if part two is not local, report it with its measured cost
   (`H2/diagnostics/MissingServiceTransport.lean`).

**For the next addendum:**
- H2 goes as addenda 3 and 4 state it;
- `NoShapeDefect` takes no signature parameter;
- `ExitOk`'s statement takes `w`, `ty` and `ex` only, so R1 cannot reopen it.

**The other items stay as addendum 4 orders them** (A, C with D's held users, F, G, H1).
- **G (row 105) is now also a precondition of R1 for services.** It adds service-table reads to
  `checkLayer`, so the typed state's `memoGet` case depends on the service table at every layer leaf
  (verifier, TREE verify §2 item 6). It also makes C7 hold for services (pedigree verify §2 item 1).
  R1 lands after G.
- **E's flat-only `ServicesFit` is right, and must become an admission rule the day the table
  opens** (D4). With an open table that types a key at `option nat`, the clause refuses honest
  states at every world (proved, TREE verify, `servicesFit_refuses_option`; TREE-02, confirmed).
- **A's table scan is one clause of `LawfulSig`.** The refusal of open template variables (pass K10)
  belongs in R1's slice, not in A: A's patch is written and checked, and widening it now costs a
  rebase.

### 5.2 R1 before the M5–M7 proofs: what it costs

This should be the first slice of the M5–M7 brief, after H and after G. The counts are declarations
whose statement changes, estimated by reading unless marked.

| Piece | Cost | Evidence |
| --- | --- | --- |
| **Source route.** `ProgramSource` gains the service table. The bodies of `PointTyped`, `CaptureTyped`, `storePre`'s `memoGet` arm and `asyncPre` read the source's signature. `ForkSource`'s two statements leave the empty table. The premises of `typedState_load` and `typedState_reachable` move to the source's signature | about 9 | the shapes elaborate (TREE `R1Probe.lean`, proved; rerun byte-identically by its verifier). The fork law holds over every signature with the tree's own proof (`fork_source_extension_sig`, proved, TREE verify) |
| **Value route, shape A.** `World` gains `serviceTy` with a default, and `World.le` one conjunct. `order_refl`, `order_trans` and the six extension proofs gain one `rfl` component each. `ServicesFit`'s body, `initialWorld` and one `TypedState` conjunct change, and one test projection gains a `.1` | 13–17 | TREE §2.2; TREE-09, partly: 17 if `initialWorld` takes an undefaulted parameter |
| **D4's three admission rules,** replacing `disagreeingService` (`Api/Author.lean:46-50`), which refuses every fresh key today | three checks | tested, pedigree verify `VerifyGuards.lean`; the red controls exist in TREE verify |
| **D6, the host-row entry's domain bit** | one conjunct, plus the slice-5 proofs that build the async case (not measured) | proved necessary (`typedProg_not_table_monotone`) |
| **C3's lemma family,** with its red controls as `Test` fixtures | about 30 new declarations; none restated | proved in the probe (TREE `R2Probe.lean`) |
| **Row 21's text** | documents only | the soundness statements need no restatement (proved corollaries) |
| **Not on the M5–M6 path:** the runtime threading of row 21's list (admission, `Built`, `HostSession.start`, `Run.open`, three `Laws/Run` theorems) | about 15–20, with the table a session field; about 45 if the session is indexed by it | TREE §2.2. M5 and M6 are stated over `ProgramSource` (`Assembly.lean:148-227`). Whether it reaches M7 is open: M7 is not declared yet (TREE verify §2 item 3) |
| **Not on the path:** the faces' 22 lines at `nativeSignature table` | restated after row 105 | P6, confirmed |

**Total before the proofs:** about 22–26 declarations restated, mechanically, plus three admission
rules, one protocol conjunct and about 30 new lemmas.

**If done after M5–M7 instead:**
- shape A adds one component to every hand-built world-order witness in M6, and to M5's initial
  world;
- shape B reopens every M6 proof that mentions `Fits` (TREE §5).

So "statement-level, because the checker already takes any signature" is right in direction, wider
than the note said (the value route; the admission rules), and cheapest now.

### 5.3 Generic cells before M6's store cases

The order is already ruled. `decisions.md`'s order says "generic language prerequisites already
authorized by rows 42–43 precede the proof arms that depend on them"; post-Phase C §11.2 says W1's
cell work comes before the corresponding W0 store proof arms. The note's §5 item 2 agrees.

The measured scope is wider than the TREE seat's eight read-modify-write arms of `Ψ_S` (TREE-10,
partly). Rows 42–43 step 3 also restates:
- the reference machine's `nat`-only `syncOpOf` decodes, at five sites;
- the checker facts every Ref and Deferred perform case reads.

`FnName` alone touches 51 tracked non-documentation files, most of them generated OCaml and
TypeScript.

**Recommendation:** keep the ruled order. Prove M5 and M6's other cases while rows 42–43 steps 3–5
land, and write M6's store-operation cases after step 3. If the owner instead wants M6 at `nat`
first, the restatement after step 3 covers the three sets of cases named above.

### 5.4 The host premise: nothing now

M6's premise is item B's tape predicate (landed; X7). When the host lane unparks, it brings:
- C5 for its world extension;
- host-boundary §4.5's receipt and application theorems, and the converse;
- DI-57's table-aware relation;
- DI-69's row meaning;
- the retirement edge.

None of this restates M6 (R6).

### 5.5 After the milestone, in the order real programs hit them

1. **R10's forms.** First DI-39's six rows, ruled in 2026-09 and never landed. Then DI-89's named
   list, each with its behaviour law and a readable expansion. Every one of the five programs needs
   at least one.
2. **R3,** as the DB-15 amendment (D10), when the first program that needs records is taken on. All
   five do.
3. **R12's and R11's statements.** These are cheap: `Deadlocked`, the armed-owner reason, and the
   release theorems over closed scopes. They come with D7 and D8.
4. **R13,** with Config route B.
5. **R5's restorations:** `build_total`, and `lower_refines_build`.
6. **The runtime threading and the faces for services.**

## 6. Open theory questions, each with a proposed decision row

The coordinator numbers the rows; `decisions.md` is not this seat's to edit. Each entry gives the
question, the options, a recommendation, and the row as it would read. D1–D6 gate the next brief.

**D1. R1's parameter, and R2's home.**
- *Options:* (a) Σ_app (the row and service tables; later nominal data and code entries), with Σ_core
  fixed and grown under DI-47's finite gate; (b) the whole alphabet as a parameter.
- *Recommendation:* (a). The machine is concrete over `NativeOp`, `SyncOp` and `FiberOp` (P16,
  confirmed). Write C1–C8 as an amendment of DB-01, which already owns signature sums and maps,
  citing DB-05, DI-47, DI-69, DI-22 and DI-64, rather than as a parallel row (pedigree verify §2
  item 8).
- *Row:* "The signature parameter is Σ_app; Σ_core grows under DI-47; extension is conservative
  under C1–C8, written into DB-01."

**D2. Where the typed state reads the service table.**
- *Options:* (A) a static component of the world, `w.serviceTy`, fixed by the order and tied to the
  source in `TypedState`; (B) a parameter of the value judgments.
- *Recommendation:* A.
  - It costs 13–17 declarations, against B's 59 statements and 15 bodies.
  - Item E's renames do not touch it.
  - It keeps `ExitOk`'s shape, which is why H2 can go.
  - It is not row 90's rejected alternative. That was a table grown at each `provide`, which would
    forbid re-providing a key at another type. A is the static table the checker already reads
    (TREE-01, partly; TREE verify §3).
- *Row:* "The typed state reads the service table as a static world component."

**D3. The open service table: by code or by key.**
- *Options:* (i) per code, as `Machine/Key.lean`'s frame (`carrier_def`: "selection is by the code,
  never by the nominal name", `:335-349`), `nativeServiceTy` for free names and the TypeScript
  profile already are; (ii) per key, as `nativeServiceTyWith` is today. Per key admits one code at
  two carriers (`one_code_two_carriers`, proved, TREE verify).
- *Recommendation:* (i). It extends the existing rule instead of adding a second one.
- *Row:* "Declared service carriers are per service code."

**D4. Which service declarations are lawful.**
- *Recommendation:* admission refuses three kinds of declaration, replacing `disagreeingService`,
  which refuses every fresh key today:
  - **names below `firstFreeName`.** A declaration at the reserved memo-map key ⟨3,3⟩ types
    `yield* ⟨3,3⟩` at `nat`, and both machines finish with a memo-map handle (proved and tested,
    TREE verify; TREE-07, partly). This rule is the provision algebra's own: "a name table must skip
    the machine's four reserved keys" (§10, finding 1; archived `E4-PROV-CE-007`);
  - **a carrier that conflicts with the built-in table** (`shadow_not_extends`, proved);
  - **a non-flat carrier.** Item E's `ServicesFit` refuses honest states at a structured carrier
    (`servicesFit_refuses_option`, proved).
- Open a separate row for structured carriers, beside R3.
- *Row:* "Declared services: reserved names, conflicting carriers and non-flat carriers are refused
  at admission; structured carriers wait on their own row."

**D5. How the row table grows.**
- *Options:* (a) module assembly appends: `Package.install` puts package rows after the module's
  (`Program/Authoring/Services.lean:186-187` puts them first; tested, pedigree verify); (b) a stored
  program is never re-linked, because it travels with its link table (DI-01's recorded default;
  DI-05; DI-22).
- *Recommendation:* both. (a) is cheap, and keeps a re-elaborated source stable. (b) is DI-01's
  default, to be decided at step 8, before the first published unit. The prepend is harmless today
  only because positions are resolved at elaboration (TREE §3.2, reading).
- *Row:* "Rows extend by append; a published program carries its link table."

**D6. The domain bit in the host-row protocol entry.**
- *Recommendation:* yes, before M6's proofs. `asyncPre`'s external arm reads `rowOf op` without
  `dom op` (`Laws/Program/Typed/Residual.lean:110-112`, read by this seat). Outside the table, the
  placeholder row's columns are `never`, so the entry holds at every certificate; a longer table then
  constrains it (`typedProg_not_table_monotone`, proved).
- *Row:* "The host-row protocol entry requires the row's domain bit."

**D7. What a frontier names; the two tape invariants.**
- *Options:* (a) a frontier reason that names armed owners, with `Api.Tape.Complete` requiring no
  armed work; (b) `awaitDecision` widened to cover armed owners.
- *Recommendation:*
  - rule INV-TAPE-1 (no off-tape choice) and INV-TAPE-2 (a frontier records what it awaits) as model
    invariants (lit-papers Q7);
  - take (a). It keeps `awaitDecision_iff`'s meaning, and names the owner, as INV-TAPE-2 asks. It
    changes the API and the host protocol's `observe`, so the decision is the owner's (completeness
    verify, open item 1).
- *Row:* "Frontiers name armed dispatcher owners; `Tape.Complete` excludes owed flushes; INV-TAPE-1
  and INV-TAPE-2 are model invariants."

**D8. A scope a finished run leaves open.**
- *Options:* an observation, or a refusal.
- *Recommendation:* an observation. rc.112 leaves it open too, and the 2026-09-07 ruling (grill
  agenda §3, call 9) already reports open scopes at a frontier. R11's theorems are stated over closed
  scopes and structured regions.
- *Row:* "Release is guaranteed over closed scopes and structured regions; a scope left open is
  reported."

**D9. Forms: identity, readability, order.**
- **Transcribe the 2026-09-07 ruling** into DI-89's row: forms are stored expanded (grill agenda §3,
  call 1). State its consequence: changing an expansion moves every digest and every byte of the
  programs that use the form.
- **The 2026-09-08 challenge,** "store the term, not the expansion", was made for a corpus with
  outside consumers. *Recommendation:* not now; revisit it at DI-01's step 8, when such consumers
  exist.
- **Forms owe a readable expansion (C8).** DI-91's fallback (a) is taken only by a written amendment
  of B19, and only for a form that cannot meet C8.
- **DI-39's six rows land first.**
- *Row:* "Forms are stored expanded (ruled 2026-09-07); each form owes a typing lemma, one behaviour
  law, a readable expansion and reader admission; DI-39 first."

**D10. R3 as one DB-15 amendment; a row for recursive types.**
- *Options:* rule the packet together: records and variants (row 2, stage b), error payloads (DI-62:
  `Err.value` at the error column's type, with the cause-side handle check it would need), `int`, and
  the decode route (typed host answers, or W9's typed `Eff` holes). Or keep the refusals until a
  program needs them.
- *Recommendation:*
  - keep the refusals now, under the owner's scope discipline;
  - rule row 2's stage (c), annotation-carried names, now: it changes no `Ty`;
  - rule the packet together when the first real program is taken on (all five need records);
  - open the recursive-types row now, so it is tracked.
- *Row:* "R3 lands as one amendment of DB-15 (records, payloads, `int`, decoding); recursive types are
  tracked."

**D11. Code-valued services (amend row 82).**
- *Recommendation:* row 82 gains three clauses:
  - **the typing half:** where a code-valued service's requirements are paid (`Cache`'s
    `requireServicesAt`);
  - **capture chosen per module contract:** a layer's closures capture at build time; `Cache` merges
    its creation context under the caller's;
  - **code identity by allocation:** entries are handles, because rc.112 removes listeners by object
    identity.
- *Row:* amend row 82 with these three clauses.

**D12. Inbound entries (several roots).**
- *Options:* (a) each host-started root is a recorded command typed at a declared entry type, so the
  typed state covers several roots (`runFork` and `runCallback` exist,
  `Machine/Fibers.lean:2181-2200`); (b) inbound events are only replies to outstanding pulls (DI-11's
  kernel), and host-started roots are refused by name.
- *Recommendation:* (b) now. `Api.load` makes one root and a session is indexed by one program. (a)
  is the route when a server-shaped program needs it; write it into host-boundary §4.6, parked.
- *Row:* "One root per run; host-started roots refused by name; the recorded-entry route written down
  and parked."

**D13. The untracked pedigree.**
- *Recommendation:* both force-add and carry over, as in §4.3.
- *Row:* "The pedigree notes that hold rulings or literature reads are force-added; each basis row
  carries its sources and literature lines."

**Recorded, with no row now** (theory questions that stay deferred):
- **An equational theory for the fiber layer.** End-state §8 defers it. With it, conservativity of a
  sum of theories becomes Hyland, Plotkin and Power's question (unread; assumed).
- **A program logic.** The basis's Logic edge is empty and DI-10 defers the bind law. Composed modules
  then have no proof technique for mutual exclusion beyond a law per module (catalogue §3, the
  trade-off).
- **Sharing.** There is no procedure form (dogfood 6, F21; end-state §8).
- **Durable journals and idempotency** for persistence, workflow, eventlog and cluster
  (host-boundary §4.2, last bullet).
- **Divergence adequacy** (R12).

**Register lines to propose** (the coordinator's file):
- the dogfood §2 merged-layer identity disagreement, against R8;
- when R1 lands, TREE verify's four red fixtures as `Test` controls: the reserved name, the non-flat
  carrier, one code at two carriers, and the host-row entry's domain bit;
- when D5 and C6 land, the pedigree verifier's install-order and admission-revocation controls.

## 7. Receipt

**Base and head.** `7cae243a` on `refactor/phase1-phase3`, unchanged from start to finish (checked
with `git log` at the end). The working tree carried the coordinator's uncommitted edits:
- `docs/STATE.md`, `docs/core/decisions.md` and `docs/core/system-map.md` (read here);
- later in the session, `docs/core/architecture-map.html` and `tools/Tools/Architecture*.lean`
  (not read).

None of them is this seat's. No commit, no `git add`, no checkout.

**Files written.** This file only. The rerun logs are in the session scratchpad
(`scratchpad/synthesis/rerun-*.log`).

**The worktree rule.** `/Users/pooks/Dev/lean4-effect4-slice6` was not read or touched. To place the
coordinator's "merged" status, this seat ran `git branch --contains` for `3c2609f4` and `eca77d6a`
and `git log --oneline -3 codex/slice6-fixes`. That read three commit titles and no file. Both
commits are on `codex/slice6-fixes` only and are not in HEAD. Codex's receipt is not in this
checkout and was not read; its content is cited from addendum 4 and the coordinator's edited rows.

**Reads.** `sed`, `grep`, `awk`, `git diff` (the coordinator's three documents), and
`git ls-files --error-unmatch` (the tracking check of §4.3).

**Reruns.** Each was run from the repository root, at HEAD, through the lock:

```sh
bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>
```

The first waited 7 min 27 s for the lock, held by the coordinator's `make gen-architecture`.

| File (in this folder) | Exit | Result |
| --- | --- | --- |
| `TREE/R2Probe.lean` | 0 | 29 axiom lines, identical to `TREE/R2Probe.log`: `[propext, Quot.sound]` or none |
| `TREE/verify-Probe.lean` | 0 | 15 axiom lines, identical to `TREE/verify-Probe.log`: `[propext, Quot.sound]`, `[propext]` or none |
| `completeness/VerifyKernel.lean` | 0 | `yielding_reasons`, `yielding_tape_complete`, `yielding_flush_finishes`: `[propext, Quot.sound]` |
| `completeness/VerifyRun.lean` | 0 | every `#guard` passes (no output) |
| `pedigree/Conservativity.lean` | 0 | 30 axiom lines, identical to `pedigree/conservativity.log`: none, `[Quot.sound]`, or `[propext, Quot.sound]` |
| `pedigree/VerifyConservativity.lean` | 0 | 11 theorems, no axioms, identical to `pedigree/verify-conservativity.log` |
| `pedigree/VerifyServiceFace.lean` | 0 | every `#guard` passes (no output) |

So the load-bearing facts this synthesis rests on are reproduced by this seat:
- C3's lemma family and the soundness corollaries;
- the non-monotone typed state, the reserved-name freshness, the per-code carriers, the flat-carrier
  refusal and the fork law over any signature;
- the frontier with no reason that one flush finishes;
- C4 with its five red controls;
- C7's failure for a fresh service key.

The failing red-control files (`*Red.lean`) were run by the verifiers, not again here; the red-control theorems inside the green files (`reflection_needs_back`, `mono_needed`, `prepend_not_extends`, …) were.

**Not run by this seat:** the programs seat's rc.112 host runs and `tsgo` checks (rerun by its
verifier); the other seat probes (rerun by their verifiers); any `lake build`, `make` or generator.
There is no `sorry`, `native_decide`, `axiom`, `partial` or `unsafe` in what was rerun (tested by `grep -c`, 0 in each of the seven files).

**Evidence classes.**
- Every verdict on cited text, every recommendation, and the H2 argument of §5.1 are reading.
- The register and tracking counts are tested by grep and `git ls-files`, bounded by their
  patterns.
- The rerun facts are proved or tested by the seats, reproduced here.
- Every probe is about particular programs, tables and tapes. None states anything about all
  programs, except the theorems quantified in their statements.

**Open obligations,** for whoever restates the requirements:
- the thirteen rows of §6;
- the row-by-row register mapping (§2.5);
- the measurement of the slice-5 proofs that D6's conjunct reaches;
- M7's statement (not declared yet);
- the Σ_app slice of §5.2, to be briefed after H and G.
