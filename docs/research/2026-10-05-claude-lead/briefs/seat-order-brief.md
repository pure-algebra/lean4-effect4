# 2026-10-06 brief for seat ORDER: the order of a lifted rule in Lean core's classes

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It holds seat PILOT's conversion. The owner asked for this slice on 2026-10-06, after a
second reader's report on what Lean already has for orders.

## The slice

The estate states an order three times. The canonical types and the error types use Lean
core's classes: `LE`, `Max`, `Std.IsPartialOrder`, `Std.LawfulOrderSup`
(`src/Effect4/Laws/Program/TypeAlgebra.lean`). The type slices use them too, as a preorder
(`src/Effect4/Laws/Slice/Lattice.lean`). The union combinator has a class of its own,
`AnswerOrder`, with seven fields (`src/Effect4/Laws/Program/UnionRule.lean`). **After this
slice there is one vocabulary.** The combinator still computes on raw types, and its laws are
read in the lattice of canonical types.

**What the coordinator compiled** (`docs/research/2026-10-06-order-classes-probe.lean.txt`,
with its output; tested, a scratch probe on `9d67ac14`):

1. From core's classes alone, a join is commutative, associative and idempotent in a partial
   order, with no axiom. Core has these equations for a linear order only.
2. The equations hold at `CTy` and at `ErrTy` by that one proof. A slice has the two bounds
   and no equation: it is a preorder.
3. `Ty.subN a b = true ↔ CTy.ofRaw a ≤ CTy.ofRaw b` holds by `Iff.rfl`. So the checker's order
   on raw types is the order of canonical types, read through `CTy.ofRaw`.
4. On raw types `≤` is the key order of sorting (`src/Effect4/Program/Ty.lean`). A raw type
   therefore cannot carry the subtyping order as an instance of `LE`.
5. A carrier with core's classes, a least element and `join = max` is an `AnswerOrder`: its
   seven fields follow, with no axiom.

## The assignment

1. **A design note first, one page**, with each statement compiled in scratch. Send its path
   and go on.
2. **One generic law module** for a join in core's classes: the two bounds and the least upper
   bound in a preorder; the three equations and the monotone law in a partial order. Use
   core's own lemma where one exists (`Std.left_le_max`, `Std.max_le_iff`), and add none twice.
   Say whether core's operation classes (`Std.Commutative`, `Std.Associative`,
   `Std.IdempotentOp`) get an instance, and what reads it.
3. **The equations of `CTy` and `ErrTy` from it**: `join_comm` and `join_assoc` at each become
   one application, or go where no caller names them.
4. **`AnswerOrder` says what it is.** Choose the smallest change that gives one vocabulary, and
   compile it before the note:
   - the class keeps its fields, and gains the standard instance of item 5 above and the
     bridge at raw types (`le a b ↔ CTy.ofRaw a ≤ CTy.ofRaw b`); or
   - the class is replaced by core's classes on the carrier of the laws, with raw answers
     read through a map into it.
   The first changes no statement. Take the second only if it removes more than it adds: count
   the statements and the lines that each form costs.
5. **The join law as an equation at every carrier.** In the canonical lattice the order is
   antisymmetric. State `lift_union` and `lift_unique` there for a pair of types: today each
   is an equation at `Ty` only (decisions row 293, point 4).
6. **The adjoint form in `≤`**: for an eliminator into types, the lifted answer `a` and each
   `b` satisfy `CTy.ofRaw a ≤ CTy.ofRaw b ↔ CTy.ofRaw t ≤ CTy.ofRaw (C b)`. It is
   `Eliminator.adjoint`, read in the lattice.
7. **One sentence for a slice view**: say which statement of the combinator is the `mono`
   premise of a slice view of a lifted rule's answer, with the types lined up and not built.

**Not in this slice:** a change of `UnionRule.lift`, of `Answer`, of a rule of the checker or
of an existing statement; a new dependency; an instance of `LE` on raw types; an order
instance on `Prod` (core's `<` on a pair is lexicographic).

## Placement of the obligations

- Concept `subtyping-algebra`; the required properties are the type order's laws and "a rule
  that reads a union member by member" (`docs/core/semantics.md`, section 2.6). Tag each
  theorem `@[semantics "subtyping-algebra" (requirement := R14)]`.
- The questions: the claims `union-rule-lift` and `sub-antisymm-canonical`, as steps; the
  equation of the join law at a pair is the open item of row 293, point 4. Propose a registry
  text only if a statement is a new question.
- Reach: carriers with core's classes; raw types through `CTy.ofRaw`. Decisions rows 137, 293.
- It does not establish: anything of a rule under the guard at a proper union;
  `checker-monotone`; a slice view of a real program.
- Its consumers: the conversions that answer a pair; the first slice view of an answer column;
  every later carrier of answers.

## The rules

- Root anchors. In `src/Effect4/Laws.lean`: directly before
  `import Effect4.Laws.Program.UnionRule`. In `Test/All.lean`: directly after
  `import Test.Program.UnionRule`.
- A new folder under `src/Effect4/Laws` needs an area row, which is the coordinator's: name
  the folder in the design note.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md`, `docs/core/controlled-english.md` or
  `tools/Tools/SemanticsRegistry.lean`. Propose their text in the receipt.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
  State each theorem as a planned goal, placed, and prove it in place.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]` or below. No existing statement
changes: show it with the two statement lists, as seat UNION's receipt does. Run narrow builds
after each step, and the default `lake build` once before the hand-back, with the gate lines,
then `make gen-fixtures`, `make check-cases` and `make check-docs`.

The receipt is `docs/research/2026-10-06-seat-ORDER-receipt.md`, in the handoff form of
`AGENTS.md`. It gives the count of lines and of statements before and after, and what each
later carrier of answers now owes. Your last message gives the head, the receipt's path and
its first item.
