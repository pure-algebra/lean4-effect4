# The algebraic reading, assessed against the tree, and the order ruling it supports

Written 2026-09-16 at `0c3f605b` (seat 1 landed 11:24 to 11:41; seat 2 drafted, not dispatched). This note checks the reviewer's assessment of the algebraic reading of the architecture (initial algebras, their unique homomorphisms, the graphs of those homomorphisms as certificates, intermediate algebras, and everything else as slack) against the code as it is, then answers the owner's question: does the consolidated plan's implementation order still stand? Every claim below was checked in the tree today; the assessed prompt itself is not in the repository, so its §4 slack rows are judged only where the assessment quotes them.

## 0. The answer

The assessment is right in substance and right in its three corrections (sixteen `Ty` constructors, a seven-sorted program family, `compileEff` as syntax rather than semantics). It is wrong on five facts and overstates two arguments (§2). None of that changes the plan's packet order. Seat 2, then the `select`/`iterate` packet, then S1, then S2 and onward, as the review log's standing ask 3 and plan §5 already say (§4).

One thing does change, inside the `select` packet: the three factoring refactors the register attached to that slice (B17 binder table, B5 `Plain` deletion, B6 `suspendDecided`) go first, as their own commits on the tree as it is, before the new constructor is added. The assessment argues this for the binder table and calls it forced; it is not forced, it is cheaper, and it applies to all three. The binder table, moreover, is not missing: it exists as `childLevel`, a private eleven-row definition over `Node` in `src/Effect4/Laws/Codegen/HoistingReadable.lean:45`, with one consumer. The refactor is a promotion, not an invention (§3).

## 1. What the assessment gets right, checked

**The objects.** `Ty` has sixteen constructors (`Program/Ty.lean:23-42`); `lit` came with `965eb07f`, which also added `Ty.sub`. The program is a seven-sorted mutual family, `Eff`, `Stmt`, `Stmts`, `Effs`, `ActionTerm`, `LayerTerm`, `LayerTerms` (`Program/Eff.lean:280-420`), over the two-sorted `Term`/`Terms` (`:250-260`); `Eff` itself has 27 constructors. `Refs.Node` has one constructor per sort (`Program/Refs.lean:39-48`). The typing, printing and reading families are indexed by sort exactly as the assessment says: `effTy` with `layerTy`, `layersTy`, `stmtsTy`, `effsTy`, `actionTy` (`Program/Typing.lean:282-557`); `print` with `printLayer`, `printLayers`, `printStmts`, `printEffs`, `printAction` (`Codegen/Print.lean:310-561`); `readEff`, `readHead`, `readStmts`, `readEffs`, `readLayer`, `readLayers` and the `readable` family (`Codegen/Read.lean:385-714`, `:792-881`).

**`compileEff` is syntax, the machine is the semantics.** The `bind` arm is `Prim.onSuccess (compileEff first (p.child 0)) (EffName.cont p)` (`Program/Compile.lean:585`): the rest is not compiled, it is addressed, and the machine reaches it through `resolve` (`:643`) and `contAOf` (`:1058`). So `compileEff` is a homomorphism into an algebra on `Point → NCode` that ignores the second argument of `bind`, which is a legitimate algebra and a useless one for meaning; the semantic object is the frame coalgebra over points into one root, which is the sentence the register already uses as its model (review log, register preamble). The assessment's refinement of the thesis's §2.5 is accepted as stated.

**The homomorphism and certificate rows.** All named and where the assessment says: `effTy_sound` (`Laws/Program/Typing/Sound.lean:45`), `effTy_complete` (`:385`), `replaceLayerAt_spec` (`Laws/Program/References.lean:63`), `Eff.restoreAll_hoistAll` (`Laws/Program/Hoisting.lean:134`), `read_print` (`Codegen/Read.lean:1768`), `read_exact` (`:2926`), `ofTy := ofNormalized ∘ normalize` and `ofTy_normalize` (`Codegen/Types.lean:311-315`), `Template.expand` (`Codegen/Forms.lean:61`) with the identical expansions of `andThenEffect` and `andThenThunk` (`:93-97`), `TypedProgram` and `checkTypedProgram` (`Program/CheckedTyping.lean:19-30`), `ModuleEmission` (`Codegen/Checked.lean:32`), `ModuleReading` with the fields `typing`, `bound`, `read` and the envelope (`Codegen/Admit.lean:100-108`, landed by `38ae77f9`). `readTy` is gone from `src` and `Test`.

**The slack rows it quotes.** `Plain` is at `Laws/Program/Agreement.lean:33` with `Plain_eq_Straight` at `:52` (59 mentions in that file, seven files in all); `Straight` is at `Program/Fragment.lean:20`, not `:13`. `OpRow` and `ServiceRow` appear in exactly three files, `Codegen/Profile.lean`, `Test/Codegen/ExprContract.lean` and `Test/Audit/AxiomGate.lean`: no producer, as B20 says.

## 2. Where the assessment is wrong, or claims more than it shows

1. **`optionCase` and `caseTag` are not in the tree.** Neither name occurs in `src` or `Test`. They are the constructs brief's proposals, and the `select` packet exists precisely so they are never added. So `select` replaces one constructor (`branch`) and pre-empts two; the count stays at 27 (28 during the S4 transition while both `branch` and `select` exist). "Eliminates 2 constructors from the 7-sorted family" is wrong.

2. **Seven exemptions, not four.** `Test/Audit/AxiomGate.lean:148-157` lists `ServiceRow.namespaces`, `ServiceRow.receiver`, `ServiceRow.sheet`, `ServiceRow.usesResult`, `mentions`, `namespacesOf`, `neededNamespaces`. The assessment repeats the register's stale count in B20; the seat 2 brief already says seven.

3. **`select` has two arms.** The packet's constructor is `select (scrutinee : Term) (decision : Decision) (arm0 arm1 : Eff Op)` (packet §1.2); the assessment writes `arms : Eff Op`.

4. **The cascade is over consumers, not sorts.** Adding an `Eff` constructor adds an arm only to functions that match on `Eff`; the arms of the other six sorts do not change. What sets the cost is the consumer count: `branch` costs 71 lines in 18 files (packet §0). The binder table removes the binder-offset part of that cost and nothing else; the typing arm, the compile arm, the meaning arm, the printer and both readers still each take one arm per constructor.

5. **The list of binder copies is not the register's list.** `Eff.weaken cut` passes `cut` unchanged through every binder (`Program/Eff.lean`, the `weaken` block): with de Bruijn levels an insertion below the scope needs no arithmetic at binders, so `weaken` is not a copy of the discipline. The reference denotation is one (`Laws/Program/Denote.lean`, fifteen `env ++ [` sites; `Handles.lean`, ten). The owners that actually encode which child binds how much: `effTy` (types, twelve sites in `Typing.lean`), `Point.child`/`childWith`/`childWith2` (values, `Compile.lean:79-98`, 46 uses), `readEff` and `readable` (`Read.lean`, 46 sites of `n + 1`/`n + 2`), `print` (eleven), `Test/Program/Gen.lean` (eight), `childLevel`, and the denotations. A count table serves the count-consumers directly (readers, printer, generator, hoisting, paths); `effTy` keeps the types and `Point` keeps the values, and each gets one lemma saying its length is the table's entry. So "seven manual lemmas become one" is the right shape, with two agreement lemmas that stay.

6. **`TypedProgram.mk` being public is harmless.** The field `typed : typeOfProgram sig program = some ty` is the checker's equation itself (`CheckedTyping.lean:19-21`). Any inhabitant, however built, witnesses that equation; proof irrelevance and `TypedProgram.unique` make every construction the same certificate. Making the constructor private would buy nothing; what stops a forged certificate is the axiom gate, not constructor visibility. No action.

7. **"Mathematically forced" is a cost argument.** Adding `select` with the table last proves the same theorems as adding it with the table first; the difference is that the table-first order verifies the refactor against the tree as it is (every proof green, no new constructor in play) and then pays one row for `select` instead of seven arms followed by a refactor of eight. That is the right order, for cost. It is not a necessity, and saying so keeps the packet honest about what it can and cannot reorder.

8. **The register is not a slack ledger.** B1 (elaboration's shape), B10 (an oracle row), B15 (requirement identity), B16 (the machine invariant) are design gaps, not redundancies, and B2, B3, B4, B11, B13, B14 are closed. A "1:1 map" from 21 slack rows to B1 to B21 cannot be exact; the thesis's §4 is not in the tree, so this note does not check it row by row.

9. **The table's domain.** The assessment writes `Node Op → Nat → Nat`; the register's B17 wrote `Eff Op → Nat → Nat`. The assessment is right: `Stmts` binds (`bindYield` extends the statements that follow it) and `LayerTerm.effect` resets the level to zero, both of which `childLevel`'s rows record. The table lives over `Node`.

## 3. The finding that changes the packet: the table exists

```lean
-- src/Effect4/Laws/Codegen/HoistingReadable.lean:45 (private today)
private def childLevel (n : Nat) : Node Op → Nat → Nat
  | .eff (.bind _ _), 1 => n + 1
  | .eff (.catchCause _ _), 1 => n + 1
  | .eff (.catchIf _ _ _), 1 => n + 1
  | .eff (.matchCause _ _ _), 1 => n + 1
  | .eff (.matchCause _ _ _), 2 => n + 1
  | .eff (.onExit _ _), 1 => n + 1
  | .eff (.whileLoop _ _ _ _), 0 => n + 1
  | .eff (.acquireRelease _ _), 1 => n + 2
  | .layer (.effect _ _), 0 => 0
  | .layer (.effectDiscard _), 0 => 0
  | .stmts (.cons (.bindYield _) _), 1 => n + 1
  | _, _ => n
```

This is the intermediate algebra B17 asked for, written on 2026-09-16 morning for one theorem (`readable_hoistAll`) and hidden as `private` in a proof file. The one test of the thesis's §6 flags it at once: it is a definition of the fourth kind (an algebra several homomorphisms should factor through) living where only proofs live, with one consumer where seven exist. The refactor:

- Move it to `Program/Refs.lean` beside `Node.child` as `Node.binders : Node Op → Nat → Nat` (values bound at child `i`; the level form `childLevel n node i = n + binders node i`, with the layer rows as the one reset, which is better stated as a separate `Node.resetsLevel` fact than folded into the arithmetic).
- Prove one agreement lemma per owner on the 27 constructors: the printer's and readers' offsets, the generator's, `Point.childWith`'s environment length, `effTy`'s environment growth, and the denotation's, each equal to the table's entry. These are `cases` proofs by `rfl` per arm.
- Then the owners read the table where they can (readers, printer, generator, hoisting) and cite the lemma where they cannot (`effTy`, `Point`, `denote`).

It is a pure refactor, zero behaviour change, one commit, and it is verified against today's proofs before `select` exists.

The same reading applies to the packet's other two register items. The packet was written before B5, B6 and B17 were raised, and it still adds a `Plain` arm for `select` (packet §1.6: "`Straight.select`, `Plain`, `Plain_eq_Straight` … the `branch` arms verbatim") and leaves `isBranch` for S4; the register says delete `Plain` and fold the five negative premises into `Eff.suspendDecided` in this slice. Both are cheaper before the constructor than after, for the same reason as the table.

## 4. The order ruling

**Packet level: unchanged.** Seat 2 (B20 deletion with B21's residue, then structural type arguments in the three TypeScript readers) → the `select`/`iterate` packet (the S4c freeze in the plan's words) → S1 (stable wire tags, then B18's deletion list) → S2 → the rest as plan §5 orders it. The reasons, one per candidate reordering the assessment raises:

- **Seat 2 before `select`.** Independent files, net deletion, drafted; and the packet's step 4 touches `read.ts`, which seat 2 also touches, so sequence keeps one seat per file.
- **`select` before S1.** `select` appends at tag 27 and moves no bytes; only `branch`'s retirement (packet step 5, in S4) needs S1's retirement rule, and the packet already says so (§1.9). The plan's sentence "stable tags must land before type-alphabet additions" is about `Ty` cases (S1's inventory of type reflections and S2's scope-exit type); `Decision` is a new stored family, which the positional codec appends safely. This is the one place the letter of plan §5 and the owner's redirect (standing ask 3) read differently; the redirect holds, and this note records why.
- **The invariant statements (D5 `TypedState`, D6 `ObsFull`) first.** The obligations note's §6 step 1 already allows them now, with no dependency; neither is in `src` yet. They are not a prerequisite for `select`: the packet's meaning theorems are arms of the existing straight-fragment fold (`meaning`, `denote`), not a second fragment theorem, so B16's freeze-before condition (before S8a-L) is not triggered. Write D5's statement before S8a-L, as B16 says; it can be drafted in parallel with the packet since it starts no build of its own.
- **Elaboration deferred.** Agreed and already the plan's stance (B1; obligations §6 step 4). Nothing to move.
- **S1's wire cleanup after `select`.** As the assessment orders it and as B18 schedules it. After seat 2 the TypeScript readers compare structure, so B18's change is a Lean-only change when S1 reaches it.

**Inside the `select` packet: a step 0.** Amend packet §4 to read:

0. Three refactors on the tree as it is, each its own commit, built and checked before the next: (a) promote `childLevel` to `Node.binders` in `Refs.lean` with the per-owner agreement lemmas (B17); (b) delete `Plain`, rewriting its 59 mentions in `Agreement.lean` and the six other files through `Plain_eq_Straight` (B5); (c) `Eff.suspendDecided` in `suspendBodyAt`'s match and as the single premise of `suspendBodyAt_of_at`, deleting `isBranch` (B6).
1. to 5. as written, with `select` adding one row to `Node.binders`, one arm to `Straight` and one to `suspendDecided`, and `childBind` defined over the table's entry rather than by hand.

That is the whole change. The packet's steps, its theorems, its controls and its S4 deletion list stand.

## 5. Housekeeping the check turned up

- The review log ends at entry 21 (Codex's lexical slice, `9c4dffc`); seat 1's four commits (`38ae77f9`, `5013db29`, `57fb8e6d`, `0c3f605b`) and the two refactors before them (`ecd44103`, `df2ab37b`) have no entry. The log's own rule is one entry per landing.
- Register B17 names `Eff.weaken` as a copy of the binder discipline; it is not (§2 item 5). B20 says four exemptions; there are seven. Both are one-line corrections in place.
- The architecture note's "27 constructors" is right; the assessment's "fifteen `Ty` constructors" came from the assessed prompt, not the note.

## 6. The one test, kept

The assessment endorses the thesis's §6 test (initial algebra, unique homomorphism, its graph, an intermediate algebra several homomorphisms factor through; anything else is slack; a homomorphism's stated domain must match its theorems; two maps of one type must be proved equal and one deleted). This note adds the corollary that found `childLevel`: a definition of the fourth kind belongs in `Program`, never `private` in `Laws`, because a private intermediate algebra is one nobody else can factor through.
