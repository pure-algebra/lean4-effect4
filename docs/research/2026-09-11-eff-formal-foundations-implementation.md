# Eff formal foundations — assessed plan and implementation packet (2026-09-11)

Source plan: `2026-09-11-eff-formal-foundations-resolution-plan.md` (nine items, four phases).
This note is the assessment of that plan against the tree at `af6c6cd` and the version to
implement. Where this note and the plan disagree, this note is the packet; the plan stays as
the proposal's history. Map ticket: `2026-09-10-fractal-cas-architecture.md` §9, T-13.
Evidence words per DI-32. **Ratified by the owner 2026-09-11, all eight decisions as
recommended, and written the same day**: rows DI-15, DI-17, DI-23, DI-39, DI-55, DI-57 and
DI-58 amended and DI-67 to DI-71 added in `docs/DESIGN-ISSUES.md`; the tracked text is
`Test/contracts/foundation-wave2.contract.md` §Formal foundations amendment. §12 below is
the list those rows implement.

## 0. Assessment in ten lines

1. Seven of the nine items are right in substance and are adopted with amendments (1, 2, 3,
   4, 6, 7, 9). Two are re-cut: item 8 rests on a premise that is false at HEAD and would
   diverge from rc.112; item 5 is under-scoped and one of its three parts contradicts the
   ratified keyed-session amendment.
2. **Item 8 is withdrawn as written.** rc.112 keys its memo map on the layer *object*
   (`Layer.ts` ~411, `memoMap.map.set(layer, entry)`), so two structurally identical layers
   built separately build twice. The tree already models object identity exactly:
   `LayerTerm.ref target` redirects two sites to one memo key and prints as one hoisted
   `const`, and `LayerTerm.fresh` exists (`Eff.lean:306-316`, `Refs.lean` header). Content
   identity would over-share relative to the runtime. My own line "memo hits unreachable"
   in the 2026-09-11 assessment predates the host-rows slice and is withdrawn with it. What
   remains is a proof slice: the sharing laws over the existing reference mechanism (§8).
3. **Item 5 keeps its direction and changes shape.** Deleting the unkeyed answer queue
   breaks the legacy truth lane (`Truth.lean:495-511` pass tape answers into `Api.run`) and
   the run entry points' signatures with their OCaml mirror; the legacy lane must move onto
   keyed version-2 tapes first. `Outcome.refused` is dropped: in the keyed session a refused
   reply is the verdict of `submit` and leaves execution unchanged (DI-58, the T-09/T-12
   amendment in `foundation-wave2.contract.md`); once the queue is gone there is no silent
   park left to name.
4. **Small misgroundings corrected.** `Ty.key` tags are `string ↦ 4`, `lit ↦ 15`
   (`Ty.lean:107,118`), not 14; `CTy` already exists (`Ty.lean:567`, `Canonical` = fixed by
   `normalize`); a `FrontierReason` already exists on the reference side
   (`Laws/Program/Sched.lean:60`: compileFuel, unansweredChoice, unsupported); the pinned
   algebra package already has `Family`, `Alphabet.toFamily` and `toSignature`
   (`.lake/packages/effects/Effects/Family.lean:22-71`), so item 6 reuses them instead of
   minting `RowSig`.
5. **Identity is subtyping-equivalence, not value-set equality.** `sub` is sound for
   membership (`hasTy_sub`, `Typed.lean:131`) and deliberately incomplete: it does not see
   that a pair over a union equals a union of pairs. TypeScript does not either. After item 1
   two types get one address iff each is a subtype of the other; the packet says so.
6. **The tag residual needs a datum, not a pattern.** There is no `catchTag` construct;
   `catchIf` takes an arbitrary test term. A residual is sound only when the typing rule knows
   the test's exact semantics, so the residual applies only to a recognized tag-test atom and
   ships with its soundness theorem (§2). The atom's shape is an owner ruling (DI-39).
7. **Sequence changes.** The generated fold (T-02) goes first, because every later item edits
   `Ty`/`Eff` case sites and the algebra is the lock. The compatibility-gate repair (v0 Wave A)
   precedes item 1, because item 1 changes type identity and the gate today cannot see it.
   Frontier reasons (item 7) come forward: small, independent, and the core of T-04. The
   denotation (item 6) stays last and is the long pole.
8. **Sizes, honestly.** Item 1: a week including goldens and the reproof of the normalization
   lemmas. Items 3, 4, 7, 8′, 9a: days each. Item 2: days plus one ruling. Item 5: days for the
   lane migration, weeks for the keyed agreement theorem. Item 6: weeks.
9. **Blast radius.** Item 1 moves every `.ty` golden and printed type whose union held an
   absorbable member, the way the literal type touched 320 files; it lands under the
   planted-test discipline with the receipt listing every moved golden.
10. **Nothing here changes a stored constructor or ordinal.** `Ty.int` stays at ordinal 3 and
    is refused at admission; `Outcome` gains a payload; `ExternalStore` loses two fields;
    no `Eff` constructor changes.

**Review round (2026-09-11, second reader).** Recommendations for the eight rulings were
checked against the tree. Adopted: the tag-test as a native atom with the residual under a
single-`Fail` premise (§2); the union-of-pairs canonical form for tagged columns (§1, which
changes this packet's earlier leaning toward the factored form); the frontier alphabet as
written with no `awaitFiber` (§7); P4 depending on P2b (§10). Amended against the tree: the
atom matches pairs only, never bare strings, so it coincides with `diffTag` (§2); the
inhabitation row carves out `never` and quantifies over an allocation (§3); the table-predicate
split cannot keep name safety in admission without keeping the reader import, so admission
drops that clause and the printer refuses (§9a); `submit` already returns the refusal as its
verdict (`HostSession.lean:180-186`), so no signature change is proposed (§5).

## 1. Type identity and the type algebra — adopted, amended

**Adopted.** Absorption in union normalization; `sub` as a proved preorder; antisymmetry on
canonical types; `join` as least upper bound; downstream laws restated over `CTy`.

**Amendments.**
- Absorption is a generic operation on the finite-row algebra, not a `Ty` special case:
  `Effect4.Row.antichain (le : α → α → Bool) : List α → List α` in `Data/Row.lean` beside
  `Row.normalize` and `normalize_idempotent`, keeping the maximal elements in sorted order.
  `Ty.normalize`'s union arm becomes `ofMembers (Row.antichain sub (Row.normalize members))`.
  `normalize` calls `sub` on already-normalized members and `sub` never calls `normalize`, so
  there is no cycle; `normalize` stays structural.
- Soundness of absorption for membership is `hasTy_sub`, already proved; `hasTy_normalize`
  (`TypeAlgebra.lean:62`) is re-proved through it.
- **One canonical shape for a tagged column: the union of per-tag pairs.** DI-15's text names
  both `prod (union of lit) string` and "a union of per-tag pairs"; they admit the same
  values (`Typed.lean:68-70` reads a pair as `.list [x, y]`, and `.union` is the disjunction)
  and `sub` relates them in one direction only (`2026-09-10-subtyping-errors-scout.md` §3.3).
  Without a choice, item 1's identity is broken again on exactly the columns that matter.
  `normalize` distributes `prod` over `union` on either side, so a normal form has no union
  under a `prod` head, the disjunctive normal form; `Normal` gains that clause. Distribution
  is **only** over `prod`: `list (A ∪ B)` is not `list A ∪ list B` (a list mixing both is in
  the first and not the second), and no other constructor needs it. With this, `diffTag` is
  a member filter, `sub` is complete on error columns, and the S4c join of two package error
  columns is a member merge. DI-55's printed face of a tag-set column moves from
  `readonly ["A" | "B", string]` to `readonly ["A", string] | readonly ["B", string]`, which
  is what the const-generic `pair` gives each member anyway; the two render to mutually
  assignable TypeScript (scout §3.3), and the moved goldens ride the same receipt as
  absorption.

**Obligations.**
```lean
-- Data/Row.lean
theorem antichain_subset  : x ∈ antichain le xs → x ∈ xs
theorem mem_antichain_iff : x ∈ antichain le xs ↔ x ∈ xs ∧ ∀ y ∈ xs, le x y → le y x
theorem antichain_idem    : antichain le (antichain le xs) = antichain le xs
-- Ty.lean / Laws/Program/TypeAlgebra.lean
theorem sub_trans (hab : sub a b = true) (hbc : sub b c = true) : sub a c = true
theorem sub_normalize : sub a b = sub a.normalize b.normalize
theorem sub_antisymm_canonical (ha : Canonical a) (hb : Canonical b)
    (hab : sub a b = true) (hba : sub b a = true) : a = b
theorem sub_prod_union_left  : sub (prod (union a1 a2) b) t = (sub (prod a1 b) t && sub (prod a2 b) t)
theorem sub_prod_union_right : sub (prod a (union b1 b2)) t = (sub (prod a b1) t && sub (prod a b2) t)
theorem normalize_prod_dnf   : Normal (normalize t) → no `union` under a `prod` head
theorem sub_join_left  : sub a (join a b) = true
theorem sub_join_right : sub b (join a b) = true
theorem join_least (hac : sub a c = true) (hbc : sub b c = true) : sub (join a b) c = true
theorem hasTy_normalize : Val.hasTy v t allocated = Val.hasTy v t.normalize allocated   -- re-proved
theorem normalize_idem  : normalize (normalize t) = normalize t                          -- re-proved
```
`CTy` (`Ty.lean:567`) is the carrier of every store key, schema document, codec law and
printed type from here on: `Ty.key` is taken of the canonical form, `Ty.schema`,
`Ty.encode`/`decode` and `render` take `CTy` or normalize at entry, and their laws are
stated on `CTy`. `key_injective` (`Ty.lean`) stays on raw `Ty`; the CAS uses
`key ∘ CTy.toRaw`.

**Tests.** Seat A's 37-type universe (`2026-09-10-schema-scout-a.md`) becomes a `#guard`
battery: zero antisymmetry failures, zero non-absorptions. Planted tests:
`join (lit "A") string = string`; `join (prod (lit "A") string) (prod string string) =
prod string string`; `normalize (prod (union (lit "A") (lit "B")) string) = union (prod (lit
"A") string) (prod (lit "B") string)`; and `normalize (list (union nat string))` is unchanged
(no distribution under `list`). The remaining incompleteness of `sub` against value
containment is recorded with rc.112's own behaviour beside it.

**Goldens.** Every `.ty` golden and printed type whose union held an absorbable member
moves; the receipt lists each by path. Run `scripts/check-compat.sh` (after §10's P0 repair)
before and after and quote both verdicts.

**Row.** DI-15 amendment: absorption and antisymmetry on canonical types are the acceptance
criterion of the subtyping slice; identity is subtyping-equivalence.

## 2. Typing subsumption and error residuals — adopted, amended

**Adopted.** Answer joining as the least upper bound (`joinAnswer a b := some (join a b)`),
which is rc.112's `A_then | A_else`; literal synthesis in discriminant positions;
subsumption at row requests and service provision.

**Amendments.**
- This is the ruled S4c step ("do not change answer joining until S4c", DI-15). Programs the
  corpus accepts today keep their types: `joinAnswer` already returned the normalized answer.
- **Literal synthesis mirrors TypeScript**, as the subtyping scout recommended
  (`2026-09-10-subtyping-errors-scout.md` §3.1): `termTy` keeps `.str s ↦ string`; `pair`'s
  literal arguments type at `lit s`. `succeed "x"` stays `string`; `pair("A", m)` types at
  `prod (lit "A") string`; the printed image agrees with the prelude's const-generic `pair`
  (DI-55). Obligation: `nativeAtom_typed` (`Laws/Program/Typed.lean`) re-proved; pin that
  `pair x y` with `x : string` a variable still types at `prod string string`.
- **The residual needs a datum.** `catchIf test body handler` takes an arbitrary term, typed
  with the caught error as the last variable (`Typing.lean:217`). The residual applies only
  when `test` is the native atom `tagIs` applied to a literal tag and that variable; every
  other test keeps today's `b.error.join h.error`. Recommended shape (DI-39, the owner's):
  a native atom in `NativeAtom.lean`, `tagIs (tag : Lit) (e : Term)`, typed `bool`; it
  evaluates to `true` **only** on a pair whose first component is `str tag`
  (`.list [str tag, _]`, the pair representation of `Typed.lean:68-70`), never on a bare
  string, so the atom and `diffTag` coincide exactly and bare-string errors stay with the
  ruled `eq`-at-string elimination. It prints as `tagIs("A", e)` through the atom printer
  (`Print.lean:58-61`) with `tagIs` added to the prelude; no inline lambda in the image.
  ```lean
  def diffTag (tag : String) : Ty → Ty   -- on canonical forms: drop the members `prod (lit tag) _`; a bare `lit tag` is kept
  theorem diffTag_sound (hv : Val.hasTy v e allocated = true)
      (hmiss : evalAtom (tagIs tag) v = some (.bool false)) : Val.hasTy v (diffTag tag e) allocated = true
  theorem diffTag_sub : sub (diffTag tag e) e = true
  ```
- **The residual against the first-`Fail` rule** (scout §3.2, a ruling). The elimination
  form selects the first `Fail` of a cause and re-raises the whole cause on a miss (DI-09,
  `Compile.lean:1205-1217`), so a cause `[Fail B, Fail A]` under a catch of `A` misses and `A`
  escapes at a type that excludes it. rc.112 has the same hole at the type level. Adopted:
  the scout's second way out. The residual is a **fidelity claim to rc.112's printed type**;
  the adequacy theorem (DI-17) carries the premise `SingleFail cause`, which holds on every
  cause the straight-line fragment can produce and is checkable on a tape; the two-`Fail` miss
  (`Test/Program/CatchIfContract.lean` `secondMiss`) becomes a counterexample row that names
  the premise. Not adopted: scanning every `Fail`, which would leave rc.112's `findError` and
  show on the truth lane for a mixed cause.
- **Subsumption sites**: row requests (`sub actual row.request`), service provision
  (`sub valueTy serviceTy`). Row answers are unchanged: the host's value is checked at the
  row's declared answer type and the continuation sees that type. Soundness is `hasTy_sub`.

**Row.** DI-15 amendment (S4c, the literal rule); DI-39 (the tag-test atom).

**Scout of 2026-09-12 (before dispatch; the dispatch file is
`docs/agents/dispatches/2026-09-12-part4-subsumption.md`, tracked).** Six facts that would have
stopped the lane: (1) atom argument typing is exact, so the literal rule needs subsumption at
fixed-signature atom arguments (DI-15 clause added); (2) the prelude `pair` is plain generic,
so DI-55's const-generic pair is unlanded and lands in commit 1, else the type oracle disagrees
on every tagged pair; (3) `pIllJoin` stops being ill under the least upper bound and is
re-purposed with the DI-60 report; (4) atoms are named on the wire, so `tagIs` changes no
ordinal; it must be total on values (false on non-pairs) or well-typed programs die; (5) the
printed image of a tag catch is `catchIf` with the prelude predicate, never `Effect.catchTag`,
which matches `_tag` objects and would not catch our tuples at runtime; (6) no
typing-preservation law exists for the catch miss path, so the single-`Fail` law is new, not a
changed statement; the two-`Fail` witness is filed as a counterexample row. Everything that
reads `joinAnswer` (declarative rules, five inversion lemmas, generated specs, soundness and
completeness) moves together in commit 2.

## 3. The uninhabited integer type — adopted, amended

**Adopted.** `Ty.int` leaves the admitted surface; the constructor stays at ordinal 3 so no
wire, key or mirror changes; `render` is unchanged.

**Amendments.**
- Refusal is at every entry: `admitProgram` refuses a program or table mentioning `int`
  (`AdmitRefusal.uninhabited (at : Path)`); `Ty.ofSchema` answers `none` for `number ∧ isInt`
  without the non-negative check (`Bridge.lean:68` today maps the pair to `nat`); the codec
  and schema entries take `CTy` and inherit the refusal.
- Not taken: appending a signed value tag to `Val`. Recorded reason: rc.112's `number` is a
  double; a faithful carrier needs a value type with decidable equality laws fit for the CAS,
  which `Float` does not give and `Int` only half gives. Restrict now, extend by one later,
  the DI-62 shape. Plain floats were never representable; this item does not change that.

**Tests.** Negative: a program at `int` refused with its path; a foreign schema `Schema.Int`
refused at the boundary by name. Positive: every `nat` program and golden unchanged.

**Row.** New row, the inhabitation invariant, stated with its two carve-outs: *every type
admitted at a program's answer, error, request or table column either normalizes to `never`
or has a value under some allocation table*, `t.normalize = .never ∨ ∃ allocated v,
Val.hasTy v t allocated = true`. `never` is the designed bottom and stays admitted; handle
and fiber types are inhabited only under an allocation, which is why the quantifier is there.
The reviewer's draft "every admitted type is inhabited at the empty allocation" is false at
`never` and at every handle type.

## 4. The error carrier as a sub-lattice — adopted

**Obligations** (`Laws/Program/TypeAlgebra.lean` or a new `Laws/Program/ErrTy.lean`):
```lean
theorem supportedErrTy_normalize : supportedErrTy t = supportedErrTy t.normalize
theorem supportedErrTy_join (ha : supportedErrTy a = true) (hb : supportedErrTy b = true) :
    supportedErrTy (join a b) = true
theorem supportedErrTy_diffTag (ha : supportedErrTy a = true) : supportedErrTy (diffTag tag a) = true
abbrev ErrTy := { t : CTy // supportedErrTy t.val = true }   -- bounded join-semilattice, bottom never
```
The lossless law exists in DI-62's shape (`errOf_valOfErr`, `valOfErr_errOf`,
`errAdmits_errOf`, `Program/ErrorImage.lean`); add only the `ErrTy`-quantified corollary.
`supportedErrTy_normalize` is needed because absorption (§1) may drop a member.

## 5. One run route and the keyed agreement — direction adopted, re-cut in three steps

**Facts.** `Api.run`, `runSync`, `replay` and `load` take an `answers` list
(`Api.lean:160,187,206,214`), consumed in scheduling order by the compile's external arm
(`Compile.lean:1430-1439`), a refusal parked into `externals.rejected`. The keyed session
(`Api/HostSession.lean`) is DI-58 in full. `run_eq_ref` (`RuntimeR.lean:209`) is over
`replay` at its defaults: empty table, no answers. The legacy truth lane passes tape answers
into `Api.run` and `Api.runSync` (`harness/truth/Truth.lean:495-511`) for 31 programs.

**5a. Move the legacy lane onto keyed tapes** (days). The recorder already emits fiber and
token (the keyed host gate). `Truth.lean`'s driver becomes a session driver: bind, submit
each tape reply by key, apply, compare. Every legacy tape gains `token` under DI-58's
migration provenance. The 31-program gate stays green through the move or the move stops.

**5b. Delete the queue** (a day). `ExternalStore.answers` and `rejected` go
(`Stores.lean:2049-2055`); `load`, `run`, `runSync`, `replay` lose `answers`; the compile's
external arm always parks at its key; the OCaml mirror (`ocaml/engine/api_engine.ml`) and the
generated TypeScript regenerate. `Outcome.refused` is **not** added: a refused reply is
already `submit`'s verdict, `⟨.refused why, s⟩` with the session unchanged
(`HostSession.lean:180-186`), and no signature changes. The frontier reason `awaitHost key`
(§7) is the complete diagnosis of a run waiting on the host.

**5c. The keyed agreement** (weeks; the proof lane). The reference machine gains the keyed
reply path, and the statement DI-57 deferred is:
```lean
theorem session_eq_ref (p : Program) (table : RowTable) (t : Tape) (h : t.WellFormed p table) :
    (HostSession.replay p table t).outcome = classify (replayR p table t) ∧
      obs (HostSession.replay p table t).machine = obsR (replayR p table t).machine
```
with `WellFormed` = DI-58's envelope per key. `run_eq_ref` becomes its empty-table corollary.

**Row.** DI-23/DI-57/DI-58 amendment: one route, the keyed session; refusal is a submit
verdict; the agreement statement above is the target.

## 6. The algebraic denotation with host rows — adopted, on the package's constructions

**Amendments.**
- No bespoke `RowSig`. The row table's meaning is the `Family` Q4 ruled:
  `RowFamily table := (Alphabet.ofTable table).toFamily` and
  `RowSig table := (RowFamily table).toSignature`, from `Effects/Family.lean:22-71`;
  the coproduct is `Effects.Algebra.Sum`, already imported. This also puts code behind Q4.
- The fragment is named honestly: **straight-line plus external rows on one fiber**
  (`StraightRows`), extending `Straight` (`Denote.lean:65`). Fork, scope and the internal
  async rows remain the reference machine's; their order of admission into the algebra
  (scope, then fork) is a later row.
- A tape is a **partial** handler: `Handler (RowSig table) (StateT Tape Option)`. Running
  out of tape is the handler's `none`, which is exactly the frontier reason `awaitHost` of §7.

**Obligation.**
```lean
def denoteRows (table : RowTable) : NativeEff → List Val → Effects.Program (Sum StoreSig (RowSig table)) ExitV
theorem denoteRows_eq_session (h : StraightRows table e = true) (ht : t.WellFormed …) :
    interpret (tapeHandler t) (denoteRows table e env) = classifyR (HostSession.replay … t)
```
Size: weeks. Last in the order; needs §5c's reference session.

## 7. Frontier reasons and the two laws — adopted, unified

**Amendments.**
- One alphabet, generated (Q7 ruled it a generated family), **observed into `Run.reasons`**,
  with `Outcome` and `run_eq_ref` unchanged (row amendment 2026-09-11, after the P2b probe):
  ```lean
  inductive Exhaustion | fuel | tape          -- on the driver's frontier result: not visible in the final machine
  inductive FrontierReason
    | commandFuel | compileFuel (fiber : FiberId)
    | awaitHost (key : HostProtocol.Key) | awaitTimer (fiber : FiberId) (wakeAt : Nat)
    | awaitDecision
  def frontierReasons (why : Exhaustion) (m : Machine) : List FrontierReason
  structure Run where outcome : Outcome; machine : Machine; reasons : List FrontierReason
  ```
  Why observed and not carried: `replayEval` yields the same `frontier` at its two exits
  (tape exhausted, fuel exhausted mid-decision) and is shared by both instances, so the tag
  is the driver's; a compile-fuel frontier is a fiber at `suspend (EffThunk.body p)` with
  `p.fuel = 0` (`Compile.lean:413,545`) and appears to the driver as fuel exhaustion, so the
  compile reason is a machine observation whose agreement with the reference needs the
  per-fiber book relation; putting reasons inside `Outcome` would drag that into `run_eq_ref`
  now. `commandFuel` has no fiber (a flush steps several). `awaitHost` carries the key only.
  No `awaitFiber`. The reference's `Sched.lean:60` inductive marks why a *denotation* is
  pending, not why a run stopped: renamed `PendingReason`, `unansweredChoice` dropped (no
  producer since the `choose` removal), `unsupported` kept and documented as unreachable at
  the empty table; the reference projects to the run-level alphabet (`reasonsR`,
  `reasons_eq_ref` separately named).
- Compile fuel split from command fuel (ruled, Q7) lands here, additive with a default
  (`compileFuel : Nat := fuel`) so the 185 call sites and every theorem statement stay
  textually unchanged; `HostSession.start` already takes `compileFuel`.

**Laws.**
```lean
theorem finished_mono_fuel (h : (replay p f tape choices answers table cf).outcome = .finished) (hf : f ≤ f') :
    replay p f' tape choices answers table cf = replay p f tape choices answers table cf
  -- compile fuel `cf` pinned; finished means the tape was exhausted with enough fuel at every
  -- decision, so Approximation's stable-of-done lemmas give whole-run equality
-- P2b preflight (Codex, 2026-09-12): three statements refuted and corrected, owner ruled.
def Interrupted (f) : Prop := interruptPending f = true ∨ f.exit.isSome
theorem guard_persists (h : requestOf m k = some r) (hd : ∀ c, d ≠ .answerAsync k.fiber k.token c) :
    requestOf (stepDecision interp fuel m d) k = some r ∨ Interrupted (fiber of k after the step)
  -- true only after the evaluate repair: a bare `evaluate` on a guarded fiber used to restart
  -- the frame and mint a new token (Codex's witness). Repair in Machine/Fibers.lean:1802: a fiber
  -- with `parked ≠ notParked` is a no-op for `Cmd.evaluate`; the arm's park-clearing goes.
  -- Safe because every legitimate resume unparks first (Cmd.resume for yields/deferreds/timers,
  -- interruptRecord for interrupts) and rc.112 has no bare evaluate on a suspended fiber.
  -- The earlier `awaitHost_stable` (whole reason lists equal across tapes) is FALSE.
theorem guard_persists_single : … equality for a one-fiber program with no cancel on the tape
-- observation laws, each against the predicate `HostProtocol.observe` reads (host-await priority):
theorem observe_awaiting : observe m = .awaitingAsync ↔ ∃ k, awaitHost k ∈ reasons
theorem observe_terminated : observe m = .terminated ↔ (∀ k, awaitHost k ∉ reasons) ∧ ∀ f, f.exit.isSome
theorem observe_idle : observe m = .idle ↔ (∀ k, awaitHost k ∉ reasons) ∧ ∃ f, runnable f
theorem awaitDecision_iff : awaitDecision ∈ reasons ↔ why = .tape ∧ ∃ f, runnable f
  -- never `terminated ↔ outcome = finished`: all fibers exited + driver out of fuel mid-flush
  -- is `frontier` with reasons [commandFuel] (Codex's witness at command fuel 3)
def Tape.Complete (p table t) : Prop := ∀ r ∈ reasons …, r ≠ awaitHost _ ∧ r ≠ awaitDecision
```
Size: days. Second lane in the sequential order.

## 8′. Layer sharing laws over the existing reference mechanism — replaces item 8

**Why item 8 is withdrawn.** See §0 line 2. Layer identity stays the path (DB-12), sharing
stays explicit through `LayerTerm.ref`, and `fresh` stays as it is. The fold keeps its
frontier parameter: it is about binding scope (`weaken` stops at closed layers), not
identity, and a "purely structural" fold cannot resolve a path-addressed reference.

**What is owed** (proof only, no source change):
```lean
theorem provide_ref_twice : provideLayer (.ref r) (provideLayer (.ref r) body) ≃ provideLayer (.ref r) body
theorem fresh_never_shares : the build of `fresh L` consults no entry of the enclosing memo map
theorem typeOf_expandRefs : typeOf (expandRefs p) table = typeOf p table    -- typing by expansion = compile by redirect
```
A truth fixture: one layer with a counted build effect, provided through two `ref` sites,
built once on rc.112 and once in Lean; the same layer written twice without `ref`, built
twice on both. Size: days. Any time; no shared files.

## 9. Structural recursion and the admission seam — adopted, sequenced first

**9a. The table predicate.** `LawfulTable` (`Codegen/Read.lean:2994`) is three table facts
(unique keys, no built-in collision, no trailing names on a value row) plus one print-face
fact (`rowNamesSafe`: the reader's reserved heads, `Read.lean:156`, and the printer's binder
byte, `Print.lean:45` `Var.name`). The face fact cannot move into `Program` without inverting
the dependency, and it cannot stay in admission without keeping the reader import. So the
cut is by meaning: **admission certifies that a program can run** and requires the three
table facts, moved to a new `Program/Table.lean`; **printing certifies that it can print**,
and `printModule` refuses an unsafe name itself through the printer's refusal (v0 Wave B
already returns it from the documented print entries). `admitProgram` imports
`Program.Table` and not `Codegen.Read`; the module-closure gate proves the cut. No admission
test exercises the name clause today: the one `unlawfulTable` fixture
(`Test/Program/InvocationContract.lean:282`, a row spelled `Ref.get`) is the built-in
collision clause and stays; the name clause gets its first negative in the print battery.

**9b. The generated fold** is T-02 as ruled: the Effect4Gen Fold group replaces the hand
`Fold.lean` (443 lines, no consumer but the root import; `Ty`/`Term`/`CauseTerm` algebras, a
seven-carrier `EffAlgebra`, a monoid fold and three unused helpers). Scout of 2026-09-12:

- **Seed exists.** Seat C's emitters survive in this session's scratchpad
  (`p03_emit_fold.lean` → `Gen_EffFold.lean`: the seven-family fold with a *family-indexed*
  carrier `R : EffFam → Type u`, `EffHom` and `hom_eq_cata_*` for all seven;
  `p06_emit_frontier.lean` → `Gen_Frontier.lean`: the frontier fold over five families with
  `weakenAlg` and `weaken_eq_cata_*`), both elaborating at `[propext]` in about two seconds.
  Scratch is ephemeral: they are copied into `tools/Effect4Gen/` as the Fold tool first.
- **Initiality is uniqueness, not `cata = rec`.** For a mutual block "`cata_eq_rec` by
  `induction <;> rfl`" would have to name Lean's seven-motive recursor; Seat C's emitted form
  is the initial-algebra property proper: `cata` exists, and every homomorphism equals it
  (`hom_eq_cata_*`). Adopt that for the Eff block and generate the same shape for `Ty`, the
  `Term` block and `CauseTerm`; keep the two hand `cata_eq_rec` only if the emitter reproduces
  them for free.
- **The driver has one hardcoded tool** (`tools/Effect4Gen/Main.lean`) and the manifest group
  has no tool column. The Fold group needs a `Tool` field (default Main.lean) read by
  `Driver.generateArgs`, so `scripts/generate.sh --commands` and `check_generated.py` keep
  working; the new output needs its producer mapping in `scripts/lib/check_generated.py` and a
  `docs/GENERATED.md` row; the header is `Tools.GeneratedStamp.line "<tool>" imports`.
- **Extras ride the guards file.** The hand file's monoid fold and helpers have no users; the
  established pattern is the group's `Guards` file appended verbatim, so they become
  executable acceptance guards (`tools/Effect4Gen/guards/fold.lean`) or go.
- **`foldMap` is mechanical** (constant carrier, explicit unit and op); `foldM` needs
  monadic sequencing of children and is emitted only if mechanical, else named in the receipt.
- **The case-site gate is staged, and the ruling already allows it.** The policy
  (`tools/Conform/Effect4/cases-policy.json`, 829 lines, `unlisted: refuse`, seeded by
  `--seed-policy`, hand notes on decision rows) pins each default arm by name with a `cover`
  list; the ruled acceptance is "no default arm over a generated family outside `Fold.lean`
  **except by name in the policy**". So P1 reseeds (after P2a's rename `rawSupportedErrTy`),
  adds `lit` covers and the unlisted `Ty.normalize`/`Ty.isMember`/`rawSupportedErrTy`, and
  moves `cases` into the routine sweep (it is an inspection profile today, not a green gate;
  it scans the build directory, so it builds first). Converting the 63 sites to exhaustive
  matches is later, area by area, not this lane.

**9a, corrected by the same scout.** Two facts change the cut:
- **The printer has no name refusal.** `PrintRefusal` is `internalAction | layerRef`
  (`Print.lean:38-41`); the printer relies on admission having refused unsafe names. Dropping
  the names clause from admission without a printer check would let an admitted program print
  a binder-colliding identifier. So `PrintRefusal.unsafeName (spelling)` is added and checked
  at the print entry over the table it prints against; `Api.printModule` keeps returning
  `Option` for now (Wave B's "return the refusal" is separate).
- **`Api.lean` imports the printer and reader for its print/read entries** (`Api.lean:4-7`),
  so "admission does not import the reader" cannot be a fact about `Api`. Admission moves
  below: `Program/Table.lean` (`rowKey` and the three table facts) and `Program/Admission.lean`
  (`AdmitRefusal`, `AdmittedProgram`, `admitProgram`; `checkTable` is already in
  `Program/Native.lean:346`), re-exported by `Api`; the module-closure claim is stated on
  `Program.Admission`'s import closure. `Codegen/Read.lean` keeps `LawfulTable table :=
  Table.lawful table && table.all rowNamesSafe` so `nativeLawful`, `read_print_native` and
  `read_exact_native` keep their statements. Moving `admitProgram` changes the OCaml mirror's
  LCNF names, so the engine regenerates.

**Why third.** Nothing in P2a/P2b added a constructor, so the lock was not needed before them;
it is needed before P3's `tagIs` atom and before anything appends to `Ty` or `Eff`.

## 10. Sequence (re-cut)

| step | items | why here | size | files |
| --- | --- | --- | --- | --- |
| P2a | 1 absorption + preorder + canonical laws; 3 `int` refusal; 4 error closure | first: it fixes the identity everything else keys on; the largest golden move | a week | `Data/Row.lean`, `Ty.lean`, `TypeAlgebra.lean`, `Bridge.lean`, goldens |
| P2b | 7 frontier reasons + fuel split; 8′ sharing laws | second: T-04's core; disjoint from P2a's files | days | `Api.lean`, `Sched.lean`, generated family; `Laws/Machine/StoresLaws.lean` |
| P1 | 9b generated fold (T-02), 9a table predicate | third: tool root ruled (DI-70); adds no constructor, so it need not precede the type lane | days | `tools/Effect4Gen`, `Program/Fold.lean`, `Program/Table.lean` |
| P3 | 2 answer LUB, literal rule, residual atom | needs P2a's `join` laws and the DI-39 ruling | days | `Typing.lean`, `NativeAtom.lean`, `Laws/Program/Typed.lean` |
| P4 | 5a lane migration → 5b delete queue → 5c keyed agreement | after P2b (the `awaitHost` reason is what replaces the silent park); 5a before 5b or the 31-program gate goes red; 5c is the proof lane's | days, a day, weeks | `harness/truth`, `Api.lean`, `Stores.lean`, `Compile.lean`, `RuntimeR.lean` |
| P5 | 6 denotation with rows as a Family | needs 5c's reference session; the long pole | weeks | `Laws/Program/Denote.lean`, new `DenoteRows.lean` |

All of it lands in the main checkout, one lane at a time, no new worktree (owner,
2026-09-11). Sequential order: P2a the type lane → P2b frontier reasons and sharing laws →
P1 the fold and the table predicate → P3 → P4 → P5. Every step is its own commit with a
receipt on the DI-32 words.

**Landed.** P2a (Codex, 2026-09-11/12): `5db3329` absorption and product distribution,
`73ae302` the canonical order and the canonical boundaries, `1774ecc` the integer refusal at
admission and the error carrier; receipt `2026-09-11-p2a-type-lane-receipt.md`. P2b (Codex,
2026-09-12): `f921bc7` the exhaustion tag, the compile-fuel split and the evaluate repair with
its negative fixture; `7804fdc` the observed reasons, the generated Api carriers, the
observation laws, `Tape.Complete`, `reasons_eq_ref` for non-compile reasons, the
`PendingReason` rename; `e94be3c` `finished_mono_fuel` and the **universal** `guard_persists`
over reachable machines with its two single-fiber corollaries (3,590 theorem declarations at
`[propext, Quot.sound]`, the key-ownership invariant proved, not assumed); `4e5fbfd`
`memoize_hit`, the map-scoped `fresh_never_shares`, `typeOfProgram_expandRefs`, the counted
`provide_ref_twice` instance certified by the kernel and extended to every larger budget by
the fuel law, and the two truth fixtures (`pDiamond` through two `ref` sites builds once,
`pProvideTwice` twice). All 18 sweep gates green at each commit; receipt
`2026-09-11-p2b-frontier-and-layers-receipt.md`. Three amendments ruled during the lane and
recorded in the rows and the contract: the unparked premise on the evaluate-entry helpers;
guard laws over machines reachable from a load (the injected-timer witness defeats the
arbitrary-machine law); `fresh_never_shares` scoped to operations routed through the fresh
map (rc.112's `fresh` calls the inner build directly without installing the map as the
current-memo-map service, `Layer.ts:3850-3851`, so a nested ambient `provideLayer` reads the
enclosing map in both the runtime and the model). **Open from P2b, separately named:** reasons
agreement for the compile-fuel reason needs the per-fiber `CompileBook` relation (the raw
book relates a zero-fuel suspend to any pending marker).

**Correction (2026-09-11, after the owner's question).** An earlier cut of this table put the
compatibility-gate repair (v0 Wave A) and the generated fold in front of the type lane. Both
were over-sequenced. The gate (`scripts/check-compatibility.py`, `tools/Compatibility/Extract.lean`)
compares the *constructor shapes* of the stored families against the baseline at `66ee4657`
and refuses a rename, reorder or payload change; its blind spots are the digest algorithm, the
value-encoding composition and the node header, and it is not in the sweep. Nothing in this
packet changes a constructor shape, a digest algorithm or a header: item 1 changes what
`normalize` returns, which the `.ty` goldens and the CAS goldens in the ordinary build already
see, and item 3 refuses `int` at admission precisely so that no constructor is removed. The
gate repair stays a v0 item where the v0 synthesis put it. Likewise the fold's exhaustive
algebra guards constructor *additions*, and this packet adds none, so P1 is a parallel lane,
not a gate.

## 11. Gates per step

Every step: full build, axiom gate at `[propext, Quot.sound]`, module closure, the sweep under
the declared-red policy. P0: the gate's self-test plus a planted digest change refused. P1: the
case-site audit lists no default arm over a generated family outside `Fold.lean`. P2a: the
37-type battery, the planted joins, the `.ty` goldens moved and listed, compat verdicts
before/after, the OCaml layout differential. P2b: the truth gate (31), the keyed host gate,
the stream gate. P3: the typing corpus and the T0 type oracle. P4: the truth gate through 5a
and after 5b, the keyed host gate, `ocaml/engine` regenerated and green. P5: the denotation
battery over `StraightRows`.

## 12. Rulings (ratified and written 2026-09-11; the row ids in brackets)

1. DI-15 amendment, in five clauses: `sub` a proved preorder on raw `Ty`; union normalization
   absorbs through `Row.antichain sub` and distributes `prod` over `union` (disjunctive normal
   form, never under `list`); on canonical types mutual subtyping is equality of the
   representatives (propositional, `a = b` for `a b : CTy`); S4c answer joining is the least
   upper bound; the literal rule mirrors TypeScript (`string` in general position, `lit` as an
   argument of `pair`). Identity is subtyping-equivalence, and the printed face of a tag-set
   column becomes a union of tuples (DI-55 amended accordingly).
2. New row: the inhabitation invariant as stated in §3 (`never` or inhabited under some
   allocation); `int` refused at admission and at the schema boundary; the value alphabet is
   not extended.
3. DI-39: the tag-test is the native atom `tagIs`, pairs only, printed through the prelude;
   the residual applies to it alone and is a fidelity claim under the `SingleFail` premise
   (DI-17 amended; DI-09 unchanged).
4. DI-23/DI-57/DI-58 amendment: one run route, the keyed session; refusal is a submit verdict;
   `session_eq_ref` is the agreement target.
5. Q7 written: the frontier reason alphabet as a generated family; compile fuel split.
6. DB-12 reaffirmed: layer identity is the path with explicit `ref` sharing; item 8 of the
   plan not adopted.
7. Q4 written with code: the row table's meaning is `(Alphabet.ofTable table).toFamily`.
8. R9 tool roots, needed by P1.
