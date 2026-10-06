# 2026-10-06 brief for seat BRACKET: a region ends with its entry flag

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is the next proof slice of R11 (decisions row 278, point 3), after seats MASKPOP
and LIFT. It is part of the close-out set that the owner named on 2026-10-06 (row 277).

## The slice

R11 keeps one open part of the mask: **the bracket of a region**. A region that changes no
flag ends with its entry flag, for an arbitrary body. It is the run-level half of the claim
`saved-mask-restoration`.

Seat LIFT proved the half that reads a run: along a run, a live fiber's flag is a function of
its stack (`MaskRuns.flag_eq`, `src/Effect4/Laws/Machine/MaskRuns.lean`). Two facts stay
open, and no theorem states either at a cut:

1. the stack at the region's end is the entry's stack;
2. the fiber is live at both cuts.

**The goal.** Define the two cuts of a region, prove the two facts for them, and state the
bracket as one placed theorem. The registry's open part then becomes a claim.

## Read first

1. `AGENTS.md`, in full.
2. `docs/research/2026-10-06-seat-LIFT-receipt.md`, item 8, whole: the statements that this
   slice starts from, two compositions that compile in scratch, each open premise, and the
   trap of `src/Effect4/Laws/Machine/LiveStack.lean` (a passing `asyncFinalizer` frame grows
   the stack during a pop, so the fact is about two cuts and not about each pop). Item 7
   gives the invariant's range: live fibers only.
3. `docs/research/2026-10-06-seat-MASKPOP-receipt.md`, item 8, line 7.
4. `src/Effect4/Laws/Machine/MaskDiscipline.lean` and `MaskRuns.lean`;
   `src/Effect4/Laws/Program/MaskRuns.lean` and `src/Effect4/Laws/Api/MaskRuns.lean`.
5. `src/Effect4/Laws/Program/Typed/Mask.lean`: `saved_mask_restoration`, the law at a
   region's boundaries, and its docstring's sentence on what it does not state.
6. Decisions rows 227 and 244 to 246 (the mask's forms and the client premise), and row 278.
7. The registry's open part "the bracket of a region" (`tools/Tools/SemanticsRegistry.lean`,
   R11), and the required property `saved-mask-chain-runs` in `docs/core/semantics.md`.

## The assignment

1. **A design note first** (`docs/research/2026-10-06-seat-BRACKET-design.md`): what a
   region's entry and its end are, as cuts of a run; the bracket's statement as Lean
   elaborates it; which landed statement gives each step; and what is not provable as
   stated, with a counterexample. Say whether the cuts are best defined on the frame machine,
   at the compiled program's interpreter, or on a journaled run. Send its path, and go on.
2. **State the bracket as a planned goal, placed, and prove it in place.** Its two facts are
   its steps. Prefer the most general home that the proof reaches: the frame machine first,
   then the compiled program's interpreter as the claim's pointer, as seat LIFT did.
3. **Keep the client premise visible**: nothing is acquired or registered before the body
   begins (rows 227, 244 to 246). Do not prove it away, and do not widen it.
4. **Controls** in a battery (`Test/Machine/MaskBracket.lean`): a real compiled program with
   a region whose body changes the flag and returns; a nested region; a region whose body is
   interrupted; and red controls. One red control for each fact: a pair of cuts with two
   stacks, and a fiber that has exited at the second cut.
5. **Stop rule.** The two facts and the definitions are the floor. If the bracket does not
   close in its step, leave it a planned goal with the exact missing fact, and hand back.

**Not in this slice:** the waiting wrapper under a masked caller, Semaphore's protected
permit, Pool's `use`, any cleanup's count, any delivery or budget law. `Program.MaskInv`
stays as it is. Do not change the machine: no file under `src/Effect4/Machine/` is edited.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The two facts | `scope-lifetime-finalization`; R11, steps of the open part "the bracket of a region" | the cuts that the design note defines | nothing of a region whose body never ends | the bracket |
| The bracket | the same; the open part itself, then a registry claim | a region of a compiled program, an arbitrary body, under the client premise | cleanup, release counts, delivery, budget, liveness; a region whose fiber exits inside it | the waiting wrapper under a masked caller, then the protected permit and Pool's `use` |

## The files, and the rules

- New files: one law module under `src/Effect4/Laws/` (the design note names its folder by
  the import graph) and `Test/Machine/MaskBracket.lean`. Root anchors: after the last import
  of a `MaskRuns` module in `src/Effect4/Laws.lean`, and after `import Test.Machine.MaskRuns`
  in `Test/All.lean`.
- You may add a statement to a `MaskRuns` law module when it is a step of that module's law.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
  Propose their text in the receipt, and read back what the coordinator enters.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.

## Acceptance

1. Each landed statement is a theorem at `[propext, Quot.sound]`, or the receipt lists the
   planned goal first, with its missing fact.
2. The controls pass, with each red one red for its stated reason.
3. Narrow builds after each step; the default `lake build` once at the end, with the gate
   lines; `make check-docs`.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-BRACKET-receipt.md`, in the handoff form of `AGENTS.md`: the
one thing to know before merging; base, head and commits; changed files; commands with
results; the statements as compiled, with axioms and `#plan_status`; what the waiting wrapper
under a masked caller still owes; the proposed registry text. One paragraph accounts for R1
to R13. Your last message gives the head, the receipt's path and its first item.
