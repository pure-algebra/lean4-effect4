# 2026-10-17 D3 landed: named types in the typed state, at every declaration table

Status: research note (history, not authority). Base: `09638d1fc` on `wip/declared-ref` (the
coordinator's head after D2). Head: `ed11f238a` on branch `seat/d3`, not pushed. Role: the math
seat, the one Lean seat. The brief: land D3 of the audit by the math note
(`docs/research/2026-10-16-math-d3/README.md` §7), in slices that each build. The receipt is
`docs/research/2026-10-17-seat-d3-receipt.md`.

## The one thing to know first

The typed world carries the application's declaration table, and `Fits` reads a declared name at
the table's least fixed point. M5 to M7 now hold at every declaration table. The field
`ProgramSource.untyped` is gone. So are the premises `types = []` of the term laws and of the
library's operation laws.

Two facts take their place:

- **A world tied to its source** (`Typed.Tied`): the world's service table and declaration table are
  the source's. It replaces the service tie that the denotation threaded, and the world order keeps
  it (`Tied.mono`).
- **A table within the world's** (`TyDecls.Within`): each name the signature declares, the world
  declares at the same body. The term laws ask this of the signature's table. The empty table is
  within every table, so a native signature is read at every world. A source's table is within a
  world tied to it.

The second fact is more general than the tie `sig.types = w.types` that the math note planned. The
equality would lose the native signature at a world with a table. Three readers need that case:
`evalTerm_fits_native`, `TermFits` and the meaning layer's `sound`.

## 1. The slices

| Slice | Commit | What changed |
| --- | --- | --- |
| (a) | `9f03d2854` | an undeclared nominal reference has no member: the duplicate arm `app n _` as a host handle is removed from `Val.hasTy`, `Fits` and `FitsAt` (decisions row 406 (1)) |
| (b) | `703c41897` | `World.types`, fixed by the order and tied in `MachineTyped`; `Fits` as `FitsAt` at the least closed oracle; `ValueOk` and `CompletionOk` read `Val.memberIn` at the world's table; `FitsIn` retired into `Fits` |
| (d) | `9e5c9c577` | the term typer's readers under the table, at membership: `fits_liftIn_transfer`, `fits_fieldAdmitsIn`, `fits_listOfIn`, `fits_optionTyIn` |
| (c) | `ed11f238a` | the premises go: `Tied`, `TyDecls.Within`, the term laws, the library's operation laws, the meaning layer's exit judgment at a table, items 3 and 4, and the column checks of §6 |

Slice (d) landed before (c): the term laws can take the table only once the readers under the table
hold at membership.

## 2. The representation

| Declaration | Meaning |
| --- | --- |
| `World.types` | the world's declaration table; `World.le` keeps it (`le_types`) |
| `FitsAt decls w o v t` | one level of membership under the table `decls`, with the oracle `o` at a declared name |
| `NamesClosed`, `NameFits` | the readings of the declared names that one level closes, and the least one |
| `Fits w v t` | `FitsAt w.types w (NameFits w.types w) v t` |
| `Tied src w` | `w.serviceTy = src.sig.serviceTy` and `w.types = src.types` |
| `TyDecls.Within decls outer` | each `decls.body? n = some b` gives `outer.body? n = some b` |
| `Denote.ExitHasTy answer error s ex types` | the meaning layer's exit judgment, read by `Val.memberIn types`; the table is empty by default |

`FitsAt` has three fixed parameters, so `fold_of` (one fixed parameter) does not generate its
induction principle. The eleven inductions are written over `FitsAt` by hand.

## 3. The laws at every table

| Law | Statement | Requirement |
| --- | --- | --- |
| `fits_unfold` | a reference to a declared name has its body's members | R3 |
| `fits_map`, `fits_mono` | a later world keeps membership | R3 |
| `fits_live`, `fits_sub`, `fits_normalize` | liveness, the order and normalization, at every table | R3 |
| `fits_memberIn` | membership implies `MemberIn` at the world's table | R3 |
| `fits_iff_membersIn` | membership reads the union members under a table within the world's | R3 |
| `fits_hasTy_of_payloadFieldTy` | at a payload field type, membership is the shape check | R3 |
| `MemberIn.of_nil`, `Val.memberIn_never` | a member at the empty table is one at every table; `never` has none | R3 |
| `hasTy_of_memberIn_shapeDecides` | on the shape-decided fragment, membership under any table is the shape check | R3 |
| `evalTerm_progress`, `evalTerm_fitsAll` | term progress and term preservation, at a signature table within the world's | R9 |

The math note's five planned goals are closed. `fits_live`, `fits_sub` and `fits_normalize` hold
at every table as they stand, since the reference arm reads the oracle only. `fits_iff_membersIn`
is proved by an induction over the least fixed point and the shortening of a chain past a repeated
name, with no guardedness premise. `evalTerm_progressIn` is `evalTerm_progress` at
`TyDecls.within_of_eq`, so no second theorem states it.

## 4. Where the premises went

| Premise | Now |
| --- | --- |
| `ProgramSource.untyped` | removed; `AdmittedProgram.source`, `reachable_typed_admitted` and `m7_admitted` take none |
| `htie : w.serviceTy = root.sig.serviceTy` (about 50 sites) | `htie : Tied root w` |
| `sig.types = []` in the term laws | `TyDecls.Within sig.types w.types` |
| `types : sig.types = []` in the operation laws of Pool, Queue and Semaphore (29) | `TyDecls.Within sig.types w.types`, with the world bound before it |
| `htypes : w.types = []` in the exit connector | removed: `exitHasTy_of_fitsExit` concludes `ExitHasTy` at the world's table |
| `app.types = []` in the session's prepared successes (item 3) | removed |
| `s.built.app.types = []` in the call tree (item 4) | removed |

`fold_typed_atomic_update` keeps `sig.types = []`: its rules record (`ListFoldRules`) states each
field at every world, and a signature with no table is within every world's table.

## 5. Items 3 and 4

**Item 3, the session's prepared successes.** The session admits a success under the application's
table (`external_answer_typed`). The frame machine converts it at the row table, reading no
declaration table (`prepareExternalAnswer`, DI-57). Where the machine's conversion refuses a value
the session admitted, it passes the value unchanged. So the prepared success is the admitted value
in both cases (`externalValue_agree`), a member of the row's answer column under the table
(`external_prepared_answer_typedIn`). On the shape-decided fragment it fits at every world: such a
type names no reference (`hasTy_of_memberIn_shapeDecides`, then `fits_of_hasTy_shapeDecides`).

**Item 4, the call tree.** Two roads were open. One gives the tree's admission the application's
table. The other replaces the route by the simulation of the call-chains note, §3.4. The first is
the cheaper road, and it was taken. The table enters the tree only at its admission. So it threads
as one parameter through the reply host, the reached invariant and the decision lift, with no new
lemma. `admittedTapeHost table types` admits by `externalAdmits` at the application's table,
which is the session's own admission; `request_leads`, `request_in_tree` and `bound_in_tree` state the
tree at `s.built.app.types`.

## 6. A regression of slice (a), repaired in (c)

Slice (a) made a reference empty in the table-free inhabitance fold (`inhabitedAlg`), so that
inhabitance stays sound against membership (`inhabited_iff_fits`). The column checks read that
fold. So a row whose column names a declared type failed its local column check, before the table
was read. A program whose answer is a declared type failed admission the same way. The touched batteries of
slice (b) did not reach the two batteries that show it (`Test/Program/SignatureControls.lean`,
`Test/Program/DeclaredTypes.lean`); those of slice (c) did.

Slice (c) repairs both checks, and the fold keeps its law:

- A row is checked without the table, so its column check reads a reference as inhabited, as it
  reads a template parameter (`rowColumnInhabitedAlg`). The table answers for a declared name, and
  the signature refuses an undeclared one.
- Program admission reads the program's columns under the application's table
  (`admitColumnIn`, `TyDecls.inhabited`). At the empty table it is `admitColumn`.

## 7. What this does not establish

- That the frame machine converts an answer under the application's table (DI-57). It passes a
  value its row-table conversion refuses unchanged, so the typed state holds, but a host handle
  at a declared column is not minted.
- That the OCaml engines admit a reply at the application's table: the coordinator's slice.
- The induction principle of `FitsAt` by `fold_of`, whose single fixed parameter does not fit.
- `ListFoldRules` at a table: its fields quantify over every world.
- Anything of a host row (F1, R6) beyond the call tree's admission.

## 8. Placement

Every row has concept `store-typing` (concept 1 of `docs/core/semantics.md`), the claim
`fits-declared`.

| Obligation | Question: role, pointer | Reach | Does not establish | Unlocks |
| --- | --- | --- | --- | --- |
| The world's table | compatibility, `le_types`, `Tied.mono` | every run from a load | anything of a host's table | the tie along every run |
| The head members | inversion, `fits_iff_membersIn` | every table within the world's, guarded or not | the readers' own rules | the readers under the table |
| The readers | preservation, `fits_liftIn_transfer`, `fits_fieldAdmitsIn`, `fits_listOfIn`, `fits_optionTyIn` | every table within the world's | the checker's completeness | the term laws at a table |
| Term progress | progress, `evalTerm_progress` | native atoms, every signature table within the world's | the typed state itself | M5 to M7 at every table |
| The typed state | preservation, M5 to M7 with `Tied` | lawful sources, the empty row table | anything of a host row (R6) | the audit's F2 |
