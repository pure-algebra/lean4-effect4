# S1 Sketch review receipt

No confirmed defect has been found in the reviewed Sketch or Parts implementation.
The module check, the part readers, and the edit laws keep their stated boundaries.
The coordinator separately reviews the query tool's law attribution.

Reviewed base: `8785c6f9`. Reviewed head: `979be0ad`.
S1 commits: `351fb3f9` and `991d57da`.
Review branch: `codex/s1-sketch-review`.
The review adds research files only.
The branch preserves `codex/partitioned-authoring-probe` and changes no production file.

## Source reasoning

`Sketch.check` (`src/Effect4/Program/Sketch.lean`) calls `Checker.checkModule` with the appended hole rows.
The structural checker still refuses a definition block.
The typing signature holds the application rows followed by the hole rows.
Program admission, signature admission, and reference expansion remain separate.

`Eff.partAt` (`src/Effect4/Program/Typing/Parts.lean`) splits a root block into its bodies and main program.
Each body receives its own normalized request as its only starting variable.
The main program starts in the empty environment.
Each part receives `Signature.withDefs` from `src/Effect4/Program/Definitions.lean`.
The signature changes invocation rows and their domain bits.
Host rows and hole rows retain their positions.

`Sketch.sigAt` answers the containing part's signature.
`Sketch.check_fill_focusAt` checks its filling there, under the longer hole table, with the original focus's exact type.
`BodiesHasTy.replace` (`src/Effect4/Laws/Program/Typing/Parts.lean`) retains each body's type and its declaration check.
The main replacement retains the bodies under signature extension.

`Sketch.check_omit_focusAt` needs closed and formed columns, plus an answer and error already in normal form.
It appends the new hole and uses the original hole-table length for its position.
Those premises remain necessary when the checker reads a hole row in normal form.

`Sketch.tableEntry` checks inside the containing part and locates refusals at the whole-program address.
The root entry holds the module check's answer.
The bodies' spine has no environment or result.
`Sketch.refusals_nil_iff` (`src/Effect4/Laws/Program/Sketch.lean`) holds over every sketch and application.
Its forward direction follows the root entry.
Its reverse direction uses the typing of every part and the structural focus law inside each part.

## Reproduced checks

The exact commands, exits, toolchain, and measured control counts are in `results.json` beside this receipt.
The narrow build checks the Sketch and Parts laws, plus the existing Parts, Sketch, and Replace batteries.
`Controls.lean` contains finite evaluations and readers of existing laws.
Its placement precedes the controls in `scope.md`.
It states no new general theorem or planned goal.

The controls distinguish two definition request types and one host row.
They check body and main fillings that invoke installed definitions.
They check omission after one existing hole, filling while declaring another hole, and retained hole rows after filling.
They refuse a wrong body type, an unavailable variable, an unknown invocation, a nested block, and mismatched body counts.
They also check malformed declaration refusals and whole-program refusal paths.
The accepted and refused controls read `Sketch.refusals_nil_iff` directly.

The focused transitive axiom output is in `axioms-output.txt`.
`Trust.lean` prints the reviewed law dependencies outside the finite battery.
Every printed declaration reports `[propext, Quot.sound]`.
`ScopedAudit.lean` uses `ProofGraph.Audit.auditedFacts` from `tools/ProofGraph/Audit.lean`.
It uses `ProofGraph.reachedAxiomsMany` from `tools/ProofGraph/Axioms.lean` for transitive dependencies.
The exact scope selects both reviewed law modules, including their imported generated declarations.
The audit refuses missing declarations, empty module sets, forbidden declaration forms, exhausted searches, and axioms outside the permitted set.
The measured module counts and axiom union appear in `scoped-audit-output.txt`.
The compiler-generated safe recursors receive the same declaration-form exception as the existing gate.
Their transitive axioms remain checked.
This receipt does not claim the whole-tree axiom gate ran.

## Open limits

`Sketch.check_filled` now requires the program to hold no root block.
Its docstring leaves the block conservativity law open.
`holes_conservative` and `sketch_weakening` still state structural-check results.
`Sketch.check_more_holes` supplies module-check weakening, including blocks.
The old semantics registry pointers do not themselves state filled-block conservativity.

The root focus holds the whole block at its module type.
`Sketch.check_fill_focusAt` accepts a root filling only when the structural checker accepts that filling.
A block-to-block root replacement is valid data and can check, but that theorem does not cover it.
`Sketch.check_fill` and `Sketch.check_omit` explicitly exclude the root of a block.
The focus-based omission law does cover replacing that root with a hole.

`focusAt_typed` (`src/Effect4/Laws/Program/Typing/Focus.lean`) cannot justify the root focus of an admitted block.
It concludes `HasTy`, whose rules exclude a block.
`Sketch.focusAt_nil` and `checkModule_sound` justify that root through the module judgment instead.
The coordinator owns the query integration finding and its controls.

The finite controls do not establish a general off-block table agreement law.
They do not order refusals after the head.
They do not establish signature admission, sketch storage admission, a wire format, reference expansion, or host execution.
No full sweep, merge, push, or owner ruling occurs in this review.
