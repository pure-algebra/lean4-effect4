# Seat "author" — receipt

Worktree `/Users/pooks/Dev/lean4-effect4-author`, branch `seat/author`, cut from
`refactor/phase1-phase3` at `1a8587f2`. Six commits, nothing pushed. The brief is scout B's
note (`docs/research/2026-09-17-language-constructs-api-scout-B.md`) with the owner's rulings:
everything recommended except the layer binder, which is another seat's and was not touched —
`LayerTerm.ref`, the hoisting, the placement protocol and the printed module shape are
unchanged.

**Evidence words.** *proved* = a theorem in the tree with its file and name, built here.
*tested* = a `#guard` in the tree that this session ran green. *stamped* = a `#print axioms`
this session printed. *reproduced* = a command re-run to the same result. *assumed* = my own
reasoning, marked at its site. Nothing below is claimed as green in a gate this seat was not
allowed to run; §7 says which those are.

---

## 1. Commits

| hash | what |
| --- | --- |
| `2312eb9f` | host rows by name (`RowDef`, `Row.host`, `Env.rows`, `Row.call`), `Module`'s four fields, `Author.build`, the reserved-name mechanism, the `Api.Built` repair |
| `7b0a3472` | services, packages and the layer/fiber words; `nativeSignatureWith`; the `Api` projections |
| `1a05c317` | `Laws/Program/Author.lean` — O-11, O-12, O-13, `carrier_unique`, B-9's capture-freedom, the conveniences' lemmas |
| `e941c847` | `Test/Program/AuthorContract.lean` — the three applications, B-9's red control and its fix |
| `7712951b` | the narrow `open` in `Api/Built.lean`, to match what landed on main as `3cf0d1e8` |
| `1da71e92` | `var` is `minted` with the reserved check in front; two unexercised entry points pinned |

`git diff --stat 1a8587f2..HEAD`: 10 files, +1264 −9.

---

## 2. What landed, with file and line

### 2.1 Host rows called by their spelling (deliverable 1)

* `src/Effect4/Program/Authoring.lean:214` `RowDef` — a host row declared once.
* `src/Effect4/Program/Authoring.lean:223` `Row.host spelling request answer (error := .never)
  (cite := "")` — `shape := .call`, `trailing := []`, `kind := .async`,
  `registration := .external`, `requires := []`. The last two are what `externalRow`
  (`src/Effect4/Program/Compile.lean:1346`) demands; `requires` stays empty on purpose (§6, C3).
* `src/Effect4/Program/Authoring.lean:104` `Env` gains `rows : RowNames`, the way `layers` was
  added. `Env.push` (`:125`) and `Env.closed` (`:129`) do not touch it, so **every generated
  lift and every existing `Src.Scoped` lemma is unchanged**: the generated modules under
  `src/Effect4/Program/Authoring/` and `src/Effect4/Laws/Program/Authoring/` were not edited
  and rebuilt untouched.
* `src/Effect4/Program/Authoring.lean:250` `Row.call r request` — resolves the spelling in
  `env.rows` and performs `.external i`; an undeclared spelling is
  `Reason.unboundRow` (`:60`) at the call's path.
* `src/Effect4/Program/Authoring.lean:231` `RowDef.table`, `:234` `RowDef.namesFrom`,
  `:239` `RowDef.names`, `:242` `RowDef.duplicate?`, `:376` `rowNamesOf`.

`rowKey` is the spelling and the trailing names (`src/Effect4/Program/Table.lean:19`); a host
row declares no trailing name, so the spelling alone is its key. `Table.lean` is not in
`Authoring.lean`'s import closure, so the key is not restated there — the laws use `rowKey`.

### 2.2 `Module` and one call (deliverable 2)

* `src/Effect4/Program/Authoring.lean:314` `Module` = `rows`, `services`, `layers`, `main`.
  `:322` `rowDefs` (own rows, then each service's operations, in order), `:326` `table`,
  `:329` `rowNames`, `:332` `serviceTypes`.
* `src/Effect4/Program/Authoring.lean:385` `elaborateModule` now binds the declared rows into
  the scope as it binds the declared layers; two rows under one spelling refuse
  (`Reason.duplicateRow`, `:65`).
* `src/Effect4/Program/Author.lean:55` `Api.Author.build : Module NativeOp → Except
  BuildRefusal Api.Built` — elaborate, assemble the table in declaration order, check the
  service declarations against the signature, admit. `:30` `BuildRefusal` is the sum of the
  three located refusals that already exist (`Authoring.Refusal`, `TypeRefusal`,
  `AdmitRefusal`) plus `serviceCarrier` (§5, D4). A module that fails to type is asked *where*
  by `Api.explain`, because `admitProgram` answers `illTyped` without a site.
* `src/Effect4/Program/Author.lean:73` `Author.program` (a module whose only field is its
  main), `:80`-`:105` `Built.ty/requires/closed/positionOf/run/runSync/print/bytes`.

### 2.3 Services, packages, layers, fibers (deliverable 3)

`src/Effect4/Program/Authoring.lean:269` `ServiceDef` (key, carrier, ops) and `:276` `Package`
(name, rows, services) are beside `Module`, which holds them; every operation over them is
`src/Effect4/Program/Authoring/Services.lean`:

* `:68` `receiver`, `:76` `Agrees` (decidable, one `#guard` at a declaration site), `:81`
  `use`, `:84` `give`, `:88` `layer`, `:111` `constant`.
* `:99` `Layer.value`, `:103` `Layer.empty`, `:108` `Layer.all`, `:115` `with_`, `:119`
  `provideAll`, `:123` `provideFresh`.
* `:133` `childOptions`, `:137` `daemonOptions`, `:141` `fork`, `:146` `daemonFork`, `:150`
  `daemonForkIn`, `:155` the `daemon body` / `daemon body in scope` notation (one module),
  `:162` `await`, `:165` `join`.
* `:172` `Package.ofRows`, `:178` `Package.op`, `:190` `Package.install`.
* `:42` `nativeServiceTyWith`, `:49` `nativeSignatureWith`, `:54` `nativeSignatureWith_nil`
  (*proved*, `rfl`): the empty service table is `nativeSignature table` itself.

`src/Effect4/Api.lean`, appended only: `:522` `requires`, `:525` `closed`, `:532` `TypedLayer`
(indexed by the signature, so one structure serves both `nativeSignature` and
`nativeSignatureWith`), `:540` `checkLayer` (total — the `none` branch is discharged by
`explainLayer_none_iff`, `src/Effect4/Program/Typing/Blame.lean:691`), `:559`-`:572`
`provides`/`requires`/`closed`/`print`, `:578` `printLayer`.

### 2.4 B-9, the binder-name bug (deliverable 4)

`src/Effect4/Program/Authoring.lean:86` `reservedPrefix := "_%"`, `:91` `Name.reserved` (read
off the UTF-8 bytes, as `LayerTerm.readRefName` does, because the string API's character
traversals reach `Classical.choice` — *stamped*: `Name.reserved` is `[propext]`), `:135`
`Env.mint` (prefix, stem, and the level the name will be bound at), `:178` `minted`, `:186`
`var` = `minted` with the refusal of a reserved name in front.

What that is worth, *proved* in `src/Effect4/Laws/Program/Author.lean`: `var_reserved` (`:93`)
an author who writes a reserved name is refused at the site, and `var_push_minted` (`:101`) a
binder the surface minted leaves every name an author wrote reading exactly what it read
before. Together: no name an author writes can be bound in a mint's place, and no name the
surface mints can be written by an author.

**Half of B-9 is owed, and its red control is pinned.** `Forms.tapContinuation "_answer1" …`
still binds the wrong variable, because `src/Effect4/Program/Authoring/Forms.lean` mints the
constant `"_answer1"`; `Sugar.bindWith` and `Loops.iterateWith` mint `"_<level>"`,
`"_c<level>"`, `"_a<level>"`, spellings an author can also write. Those three files are
generated from `tools/Effect4Gen/Forms.lean` or are outside this seat's files, so the fix is
named, not made — see §6, C1. `Test/Program/AuthorContract.lean` pins the bug as a red control
beside the expansion that fixes it (`tapMinted`, the same shape with `Env.mint` in place of
the constant), so the two `#guard`s differ in exactly one de Bruijn index (`.var 1` against
`.var 0`).

### 2.5 The laws (deliverable 5)

All in `src/Effect4/Laws/Program/Author.lean`, all *proved* and *stamped* at
`[propext, Quot.sound]` or below (§4).

| name | line | statement |
| --- | --- | --- |
| `Row.call_scoped` | `:53` | **O-13.** A declared row's call is scoped when its request is — the shape of the 48 generated lift lemmas |
| `build_table_lawful` | `:155` | **O-11.** Distinct spellings, none a built-in's, and the host shape give `Table.lawful`; all three decidable, one proof for every program |
| `build_rows_resolve` | `:175` | **O-12.** In the scope a module elaborates in, a declared row's call performs the external position its own table put the row at, and the table has that row there |
| `ServiceDef.carrier_unique` | `:211` | scout B's `carrier_unique`; it was not in the tree |
| `var_push_minted` | `:101` | B-9's capture freedom |
| `var_reserved` | `:93` | a reserved name refuses where an author writes it |
| `Names.resolve_append_ne` | `:80` | a binder of a different name changes no level |
| `RowDef.nodup_of_duplicate?` | `:110` / `nodup_keys` `:143` / `namesFrom_find?` `:120` | what O-11 and O-12 rest on |
| `build_table` `:194` / `build_lawful` `:201` / `build_runnable` `:205` | | what a build carries |
| `ServiceDef.agrees_serviceTy` | `:218` | a declaration that agrees is the signature's carrier |
| 15 `*_scoped` | `:228`-`:283` | one per new convenience, so `authoring_scoped` discharges the new surface as it does the old |
| 14 `*_eq` | `:292`-`:331` | the conveniences' unfolding equations, all `rfl` |

### 2.6 The battery (deliverable 6)

`Test/Program/AuthorContract.lean` (373 lines), rooted at `Test/All.lean:68`. All `#guard`s
*tested* green this session; every theorem *stamped*.

* **E1** — the counter service, the layer that builds it, the layer used twice.
  `#guard elaborateModule once = .ok Test.Program.LayerSharingContract.once` and the same for
  `twice`: the new surface elaborates to **exactly** the trees the layer-sharing battery
  certifies, reference target and all. `Author.build once` runs to `Exit.success (Val.nat 1)`.
  The layer is checked and printed on its own before any program provides it.
* **E2** — `Packages.keyValueStoreMemory` installed as a package; `readKey.table =
  Packages.keyValueStoreMemory` and `readKey.rowNames = [("Kv.make",0),("get",1),…]`. No table
  position is written anywhere. A spelling the package does not offer refuses at the call site
  under the name the author wrote.
* **E3** — the two-service deployment. `Api.checkLayer deployment` is closed; `Api.checkLayer
  siblingMistake` provides the same four keys and requires two of them, so `closed = false` —
  the sibling mistake is caught before a program exists. `Api.requires` on the handler answers
  `[Db, Rate]` as data.
* Beside them: the fiber words with `daemon` at the call site, the layer words, a service
  carrier the six type codes do not spell (through `nativeSignatureWith`), and B-9's red
  control and fix.

---

## 3. Aesop

Every proof in `src/Effect4/Laws/Program/Author.lean` is a search, an application of one
existing lemma, or `rfl`. No `simp_all`, no `first`, no `try`; hand `simp` appears once
(`simpa using hi`, an index shift) and `omega` once, as a `have`, never as an aesop rule.

**Aesop-closed (the search does the work).** `Row.call_scoped`, `Names.resolve_go_append_ne`
(per case, with the induction hypothesis handed to the call as the README asks),
`var_push_ne`, `var_reserved`, `var_push_minted`, `RowDef.nodup_of_duplicate?`,
`RowDef.nodup_keys`, `build_table_lawful`, `Row.host_shape`, `build_table`,
`ServiceDef.carrier_unique`, `ServiceDef.agrees_serviceTy`.

**Needed a fact stated first, and why.** Two proofs. Each `have` is a residual goal aesop
printed, not a tactic piled on:

* `RowDef.namesFrom_find?` (`:120`) — aesop's residuals were `False` (it had
  `∀ x ∈ rest, ¬ x.spelling = r.spelling` and `r ∈ rest` but does not instantiate a
  universally quantified hypothesis of the context) and `base + 1 + j = base + (j + 1)`. So:
  `hne` derived from `nodup_of_duplicate?`, and `harith` by one `omega`.
* `build_rows_resolve` (`:175`) — aesop's residuals were `i_1 = i` and a `False`, both naming
  the same missing fact: `env.rows.find? … = some (r.row.spelling, i)`. Stating `hsplit` (what
  `rowNamesOf … = .ok names` says) and `hfind` closes it.

**A trap worth recording.** `beq_decide` (`:45`), `(a == b) = decide (a = b)` at `String` by
`rfl`, registered `attribute [local aesop norm simp]`. Without it, `namesFrom_find?` and
`build_rows_resolve` came out at `[propext, Classical.choice, Quot.sound]`: the library's
lemmas about `==` at `String` (`beq_self_eq_true`, `beq_iff_eq`) reach `Classical.choice`
through the lawfulness instance, and the default simp set uses them. *Reproduced*:
`theorem tt (s : String) : (s == s) = true := by simp` stamps
`[propext, Classical.choice, Quot.sound]`, while `decide_eq_true rfl` stamps nothing. This
mentions no project type, so it is a candidate for `src/Effect4/Laws/Auto/Inversion.lean` —
not added there, because that file is not this seat's and touching it rebuilds the Laws graph
(§5, D1's reasoning). **Any aesop proof in this tree that normalises a `String` comparison
will leave the axiom ceiling unless this equation is registered.**

**Census.** `#auto_census Effect4.Laws.Program.Author using aesop` (run twice, before and
after the shortening): *16 of 47 theorems closed from their statements; 39 source lines they
now take.* Fourteen of the sixteen are the `*_eq` lemmas, already `rfl` at two lines; one is
`beq_decide`, already `rfl`. The one it found worth shortening was `Row.host_shape` — its
`aesop (add norm simp [Row.host])` is now plain `aesop`. Nothing else the census reports is
longer than its search.

---

## 4. Verification

Commands, all run in `/Users/pooks/Dev/lean4-effect4-author`.

```
lake build Effect4.Program.Authoring
lake build Effect4.Program.Authoring.Services
lake build Effect4.Program.Author
lake build Effect4.Api
lake build Effect4.Laws.Program.Authoring
lake build Effect4.Laws.Program.Author
lake build Test.Program.AuthorContract
lake env lean -M 6144 Test/Program/AuthorContract.lean         # every #guard, every stamp
```

Regression of what the change could break, all green:

```
lake build Effect4.Laws.Program.Authoring.Sugar Effect4.Laws.Program.Authoring.Forms \
           Effect4.Laws.Program.Authoring.Loops
lake build Effect4.Api.HostSession Effect4.Api.Runner Effect4.Api.RunnerBytes \
           Effect4.Api.HostProtocol
lake build Effect4.Laws.Api.Codegen Effect4.Laws.Api.Fuel Effect4.Laws.Program.Means
lake build Test.Program.AuthoringContract Test.Program.LoopSugarContract \
           Test.Program.BlameContract Test.Api.TestClockContract
```

Axioms, in `/tmp` scratches importing the built modules (`#print axioms`): **every one of the
47 theorems** of `Laws/Program/Author.lean`, the two changed theorems of
`Laws/Program/Authoring.lean`, the six battery theorems, and **all 50 new definitions**
(`Author.build`, `checkLayer`, `Row.call`, `Name.reserved`, `Env.mint`, `nativeSignatureWith`,
the `Built.*`, `Package.*`, `ServiceDef.*` and `Layer.*` families) stamp `[propext]`,
`[propext, Quot.sound]` or nothing. No `Classical.choice`, no `sorryAx`, no new axiom.

Citation gates (no Lean needed): `bash scripts/check-internal-citations.sh` PASS.
`python3 scripts/check-source-citations.py` reports three failures, all pre-existing and none
in a file this seat touched — `docs/UNIVERSAL-ALGEBRA-REFACTOR.md` (untracked in the
coordinator's tree), `ts/eff/node_modules/effect/package.json` and `workshop/Timer/Timer.lean`
(neither checked out here).

---

## 5. Decisions I made, with the reason

**D1. `nativeSignatureWith` lives in `Authoring/Services.lean`, not as a defaulted argument on
`nativeSignature` in `Native.lean`.** The brief allowed either. Any edit to `Native.lean`
invalidates roughly three hundred modules including the whole Laws graph, and this seat may
not build `Effect4`, `Effect4.Laws` or `Test.All` — so a change there could not be verified,
only hoped. What landed is additive and *proved* to change nothing:
`nativeSignatureWith table [] = nativeSignature table` by `rfl`
(`Authoring/Services.lean:54`). Moving it onto `nativeSignature` later is a one-line
follow-up whose only cost is a full rebuild. The coordinator's third note confirms it stays
out of `Author.build` and `Api.check` for now.

**D2. The record is `ServiceDef`, not `Service`.** `Effect4.Machine.Service` already exists
(`src/Effect4/Machine/ContextMap.lean:32`) and batteries `open Effect4.Machine`, so `Service`
would be ambiguous at every use site. `ServiceDef` is also the name scouts A and D use.

**D3. `src/Effect4/Program/Author.lean` declares into namespace `Effect4.Api`.** The name is
`Api.Author.build`, so the three modules of the dream API read as `Author` / `Run` / `Face`
(scout A §4.1). The file path is the brief's. It is the one place in the tree where a module
under `Program/` declares into `Effect4.Api`; say so if you would rather it moved to
`src/Effect4/Api/Author.lean`.

**D4. `build` refuses a service whose declared carrier disagrees with the signature**
(`BuildRefusal.serviceCarrier`, `Program/Author.lean:38`), rather than accepting the
declaration and ignoring it. A declaration that the checker does not believe is worse than no
declaration.

**D5. The three records are in `Authoring.lean`, their operations in `Services.lean`.**
`Module` holds `RowDef`, `ServiceDef` and `Package`, so their definitions must be below it;
every operation needs the generated lifts, which are above it. Two files, one owner each.

**D6. `Package.op` returns a `RowDef`, never an `Option`.** A spelling the package does not
offer answers a row carrying that spelling and nothing else, so `Row.call` refuses at the call
site with the name the author wrote — a located refusal instead of an `Option` an author must
unwrap at every call.

**D7. `daemon body` and `daemon body in scope` are notation in one module**
(`Services.lean:155`), over the plain functions `daemonFork` and `daemonForkIn`. The three
examples are written with it (`Test/Program/AuthorContract.lean`, the fiber section).

**D8. `Api.Built` was repaired.** As committed at `1a8587f2` it could not be constructed:
`RowTable` was not in scope in `src/Effect4/Api/Built.lean` (no `open`), so autoImplicit bound
the field as `table : {RowTable : Type} → RowTable`, a type with no closed inhabitant, and
`Built` sat at `Type 1`. `set_option autoImplicit false` plus the narrow
`open Effect4.Program (RowTable AdmittedProgram)` the coordinator asked for. Both seats that
share this file were blocked on it.

---

## 6. Owed, and why

**C1. B-9's second half: the minted spellings.** `Authoring/Sugar.lean:26` (`bindWith` mints
`"_" ++ level`), `:37` (`andThen` binds `"_"`), `Authoring/Loops.lean:34-35` (`iterateWith`
mints `"_c<n>"`, `"_a<n>"`) and the generated `Authoring/Forms.lean:28,48,56,88`
(`"_answer0"`, `"_answer1"`, `"_exit0"`, `"_exit1"`) still mint spellings an author can write.
The change is mechanical and identical in each: mint with `env.mint "<stem>"` and read with
`minted` instead of `var`. For the forms it is a change in `tools/Effect4Gen/Forms.lean` and a
regeneration of `src/Effect4/Program/Authoring/Forms.lean` and
`src/Effect4/Laws/Program/Authoring/Forms.lean`. None of those five files is in this seat's
list, so I named the change and pinned the bug as a red control rather than making it. With
it, `var_push_minted` (already *proved*) covers every convenience in the tree; without it,
it covers only the ones that mint through `Env.mint`.

*Assumed, not tested:* changing the forms' minted names cannot move a printed byte — a binder
name never reaches the printer, which names binders `a0`, `a1`, … . Worth one `make check-gen`
when it is done.

**C2. Supplied service carriers do not reach a certificate.** `Api.Built.admitted :
AdmittedProgram program table` is indexed by the table alone, and `AdmittedProgram` is stated
at `nativeSignature table` (`src/Effect4/Program/Admission.lean:88`). So a module may *declare*
a carrier the six type codes do not spell and check a layer against it
(`Api.checkLayer … (nativeSignatureWith table services)`, *tested* in the battery), but
`Author.build` still admits against `nativeSignature table` and refuses a declaration that
disagrees with it. Threading services further changes the certificate's signature and the
soundness statements, which the coordinator has raised as an owner decision.

**C3. `Row.requires` is untouched, deliberately.** D-B1(a) is the receiver-as-value
convention, so a service operation is a `method` row whose receiver is the first request
component and whose `requires` is empty. Setting it would put the key into the program's
requirement row (`src/Effect4/Program/Typing.lean:302`) and a layer's own build would then
require the key it provides. D-B2's shipped-row guard (every row's `requires` is empty or
every key in it is in the signature's service table) is not written.

**C4. No whole-tree gate was run**, as the brief requires: not `make check`, not
`make check-host`, not `make check-gen`, not the axiom gate's
`lake env lean Test/All.lean`. Per-module builds and `#print axioms` scratches stand in (§4).
Two things a whole-tree run would check that I could not: the module-closure gate (my four new
library modules are reachable from `Effect4.Laws` through `src/Effect4/Laws.lean:82`, which
also makes `Effect4.Api.Built` reachable for the first time — it was reachable from neither
root before), and the axiom gate over declarations I did not stamp by name.

**C5. Nothing is proved about `Author.build`'s agreement with `Api.author`.** They take
different inputs (a module against a source) and the composition is evident from the
definitions, but there is no theorem that `Author.build { main := s }` and
`Api.author s` agree on the program. One line to state, and it belongs with the Run seat's
`Built` consumer.

---

## 7. For the coordinator

1. `src/Effect4/Api/Built.lean` now matches main's narrow open (`7712951b`), so that file
   should merge clean.
2. `Built.run : Run` (`src/Effect4/Program/Author.lean:94`) is the declaration your `Api.Run` →
   `Api.Inspection` rename will touch.
3. `src/Effect4/Laws.lean:82` gains `import Effect4.Laws.Program.Author`; `Test/All.lean:68`
   gains `import Test.Program.AuthorContract`. If you would rather the two new library modules
   also hung from `src/Effect4.lean`, the imports are `Effect4.Program.Author` (which pulls
   `Effect4.Program.Authoring.Services` and `Effect4.Api.Built` with it) — I did not edit that
   root.
4. The `beq_decide` finding (§3) is a general trap for aesop in this tree and mentions no
   project type; it belongs in `src/Effect4/Laws/Auto/Inversion.lean` if you want every seat
   to inherit it.
5. C1 is the one piece of the brief I could not finish inside my files. It is three small edits
   and one generator change, and the red control that proves it is still needed is pinned at
   `Test/Program/AuthorContract.lean`.
