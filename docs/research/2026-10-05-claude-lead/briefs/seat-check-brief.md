# 2026-10-06 brief for seat CHECK: the checker's second test goes

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is decisions row 273, point 2: seat REFS's proposal P4, with Codex's limits.

## The slice

`typeOfProgram` (`src/Effect4/Program/Typing.lean`) tests two things before it types the
expanded program: the references are well formed, and the expansion has no reference site.
`expanded_refs_nil_of_wf` (`src/Effect4/Laws/Program/ReferenceExpansion.lean`) proves that
the first gives the second. So the second test is redundant, and one arm of `Api.explain`
(`src/Effect4/Api.lean`) is dead on every well-formed program: the arm that answers
`layerReference` for a site that survives the expansion.

**The goal.** `typeOfProgram` tests the references' formation only:

```lean
def typeOfProgram (sig : Signature Op) (program : Eff Op) : Option EffTy :=
  if program.layerRefsWF then typeOf sig program.expandRefs else none
```

`Api.explain` loses its dead arm in the same commit. No program's answer changes: the old
form and the new one are equal by `typeOfProgram_eq_if_refsWF`.

## Read first

1. `AGENTS.md`, in full.
2. `docs/research/2026-10-06-seat-REFS-receipt.md`: finding F4 and proposal P4. P4 lists
   the five proofs that unfold `typeOfProgram`: `typeOfProgram_ext`
   (`src/Effect4/Laws/Program/Signature.lean`); `TypedProgram.layerRefsWF`,
   `TypedProgram.expanded_refSites` and `TypedProgram.hasTy`
   (`src/Effect4/Laws/Program/CheckedTyping.lean`); `typeOfProgram_looped`
   (`src/Effect4/Laws/Program/TypedRun.lean`).
3. Codex's limits for this change:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-1136-pool-and-questions/refs/review.md`,
   the section "Remaining choices and recommendation", point 2.
4. `src/Effect4/Api.lean`: `explain`, `explain_none_iff`, `blame_none_iff`, and each use of
   `explain_none_iff` in that file.
5. `src/Effect4/Laws/Program/ReferenceTyping.lean`: `typeOfProgram_eq_if_refsWF` and
   `typeOfProgram_expandRefs`.

## The assignment

1. **Measure first.** `grep` every use of `typeOfProgram` and of `Api.explain` under `src`,
   `Test`, `tools` and `harness`. List each proof that unfolds either, in a short design note
   (`docs/research/2026-10-06-seat-CHECK-design.md`). Send its path, and go on.
2. **Change the two definitions in one commit**, with every proof that breaks:
   - `typeOfProgram`, as above;
   - `Api.explain`: on well-formed references it answers the structural `explain` of the
     expansion. The arm for a surviving site goes.
3. **Keep every statement.** `explain_none_iff`, `blame_none_iff`, the certificate laws of
   `CheckedTyping.lean`, the signature transport and the looped checker's connector keep
   their statements. `typeOfProgram_eq_if_refsWF` keeps its statement too: it becomes the
   definition's own equation. `TypedProgram.expanded_refSites` now takes the fact from
   `expanded_refs_nil_of_wf`, in the law graph.
4. **The runtime root imports no law.** `src/Effect4/Api.lean` and
   `src/Effect4/Program/Typing.lean` gain no import of `Effect4.Laws`. If a proof of the
   runtime root needs the expansion theorem, stop and report: that proof moves to the law
   graph, and the coordinator decides where.
5. **Remove no constructor.** `TypeRefusal.layerReference` stays, whether or not the arm was
   its last producer in `Api.lean`. A removed constructor changes the wire's tags.
6. **Controls.** The battery of the references (`Test/Program/ReferenceExpansion.lean`,
   `Test/Program/LayerRefs.lean`) keeps every answer: the nine programs type or refuse as
   before, and `Api.explain` gives each refused program the same refusal. Pin one program
   whose refusal came from the dead arm before, if one exists; the receipt says if none does.

## Placement

No new statement is asked. The slice serves `initial-algebras-folds`, R5, as a simplification
under `reference-expansion-complete`, and it keeps the located refusal's completeness
(`explain_none_iff`). It establishes nothing new, and it must lose nothing.

## The files, and the rules

- You may edit `src/Effect4/Program/Typing.lean`, `src/Effect4/Api.lean`, the law files that
  P4 names, `src/Effect4/Laws/Program/ReferenceTyping.lean`, the two batteries above, and
  any file whose proof breaks by the change. List each in the receipt.
- `Typing.lean` is low in the graph: the change rebuilds most of the tree. Make it once.
  Use narrow builds while you work, and the default build at the end.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. A proof
  that you touch loses its `simp_all`, `first` and `try`: the proof-style ratchet refuses a
  new use, and `make record-proof-style` is the coordinator's.

## Acceptance

1. The default `lake build` passes, with the gate lines of `Test/All.lean`. No statement of
   the list in point 3 changed: give the `#check` of each before and after.
2. `make gen-fixtures` and `make corpus`, then `git status`: no generated file moves. Then
   `dune build` and `dune test --force engine`, through `opam exec --switch=effect4`. Say
   which corpus folder the test read.
3. `make check-cases` and `make check-docs`.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-CHECK-receipt.md`, short, in the handoff form of `AGENTS.md`:
the one thing to know before merging; base, head and commits; changed files; commands with
results; each kept statement's `#check`; each proof that moved or changed; what the
proof-style baseline loses. Your last message gives the head, the receipt's path and its
first item.
