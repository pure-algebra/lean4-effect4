# 2026-10-10 Design: layers by lexical scope (decisions row 341, steps 2 and 3)

## 1. The one thing to know first

A layer outside every definition body belongs to the module. A layer in a body belongs to one
call of that body. rc.112 behaves this way because its memo map is keyed by the layer object. The
machine keys a build by the layer's path alone (DB-12), so today a body's layer is shared across
every call. Step 1 of row 341 landed the scope rule. Two steps remain:

- **Step 2**: a body names a module-level layer, and module-level layers get a home in the
  block.
- **Step 3**: a body's layer is keyed by its path and the call that runs it.

The language gains no other construct. A program written today keeps its meaning, except one
case: a body's layer reached by two calls. Step 3 changes that case to rc.112's meaning.

## 2. What rc.112 does

| Fact | Source |
| --- | --- |
| The memo map is a `Map` keyed by the layer object | `vendor/effect-4.0.0-rc.112/src/Layer.ts` (`MemoMapImpl`, `readonly map = new Map<Layer<any, any, any>, MemoMapEntry>()`) |
| A memoized layer looks itself up by identity, and builds on a miss | `Layer.ts` (`fromBuildMemo`: `memoMap.getOrElseMemoize(self, scope, build)`) |
| A build stores its entry under the layer object | `Layer.ts` (`memoMapBuild`: `memoMap.map.set(layer, entry)`) |
| A lookup that misses the local map asks the parent map | `Layer.ts` (`MemoMapImpl.get`: `this.parent?.get(layer, scope)`) |

Three consequences follow for printed code:

- A module-level `const DbLive = Layer.effect(…)` is one object. Every use shares one build per
  memo map, in every function.
- `Layer.effect(…)` evaluated inside a function body is a new object at each evaluation, so each
  call builds its own.
- A closure sees the object of the call that made it.

## 3. What the tree does now

| Fact | Where |
| --- | --- |
| A build is keyed by the layer's path (`LayerId := List Nat`) | DB-12; `src/Effect4/Machine/Stores.lean` (`MemoMap.entries`) |
| A reference names its target by path, and the target precedes it in program order | `Eff.layerRefsWF` (`src/Effect4/Program/Refs.lean`) |
| A block's bodies are child `0`, and its main program is child `1` | `Node.child` (`src/Effect4/Program/NodeLenses.lean`) |
| A reference and its target stand in one scope (step 1) | `Eff.scopeOf`, `Eff.layerRefsWF`; row 341 |
| The printer refuses any layer term inside a body | `printDef` (`src/Effect4/Codegen/Print.lean`, reason `defs:layer`) |
| The authoring surface places a shared layer at its first use in program order | `elaborateModule` (`src/Effect4/Program/Authoring.lean`) |

Program order puts every body before the main program. So a body never names a layer of the main
program, and the authoring surface places a layer used by a body and by the main program inside
the body. Step 1 now refuses the result: the main program's use names a layer in a body. No
module in the tree does this today (survey of 2026-10-10: no authored module declares both shared
layers and definitions).

## 4. Step 2: module-level layers

### 4.1 The rule

A reference sees its own body's layers and the module's layers: lexical visibility. A body's
reference may name a module-level target in any program order. Within one scope the target still
precedes the site.

```mermaid
flowchart LR
  B[a site in body k] -->|precedes it| BK[a target in body k]
  B -->|any order| M[a module-level target]
  MS[a module-level site] -->|precedes it| M
```

The references stay acyclic. A module-level target holds only module-level sites, so every chain
of hops goes down within one body, jumps at most once to the module, and goes down there. The
expansion bound (`expanded_refs_nil_of_wf`, `Laws/Program/ReferenceExpansion.lean`) ranks sites
by program order. It ranks module-level sites first instead, and the existing measure argument
carries over: a target's inner sites rank below every site that names the target.

### 4.2 A home for module-level layers

The main program cannot hold every module-level layer. A layer that only bodies use, such as the
one that `const withTx = (p) => Effect.provide(p, TxLayer)` reads, has no use in the main program
to stand at. Two representations:

| Option | Shape | Cost |
| --- | --- | --- |
| (a) a block child: `.defs decls bodies layers main`, the module's layers as a `LayerTerms` spine | the printer's hoisted `const L_<path>` becomes the block's own declaration list; the authoring `Module.layers` maps onto it one to one | one constructor field: the new-field checklist (wire, LCNF roots, goldens, reader, OCaml bridge, case policy) |
| (b) the main program only | a module-level layer stands at a use in the main program | no syntax change; a layer that only bodies use cannot be written |

Ruled (a), by the owner, 2026-10-10. It is the representation the printer already prints: one
declaration per module-level layer, before the main program. The authoring surface already keeps
`Module.layers` as that list. (b) refuses an ordinary Effect program.

The field comes last: `.defs decls bodies main layers`, the module's layers at child `2`. Every
existing path keeps its meaning: the bodies stay child `0`, the main program child `1`, and no
printed `L_<path>` name or golden byte moves. Three scopes follow, by the path's first index:

| Path | Scope | Visible to |
| --- | --- | --- |
| `0 :: …` in body `k` | body `k`, with its parameters | body `k` |
| `1 :: …` | the main program | the main program |
| `2 :: …` | the module | every scope |

A module-level layer names only module-level layers. So a reference never leaves the module once
it enters it, and the order below is acyclic.

The reference order ranks module-level sites before every other site, and program order within
each class (`Path.refBefore`). Within one scope a target still precedes its site in program
order. The expansion bound's rank argument (`target_refs_prior`) reads that order in place of
`Path.lt`.

The field reaches what a new constructor field reaches (the new-field checklist): the generated
folds and lenses, the OCaml emitter and its goldens (`src/OCaml5/Eff/Goldens.lean`), the LCNF
roots, the engine bridge (`ocaml/engine/e4_program.ml`), the TypeScript generator and reader
switches (`tools/Drivers/TsGen.lean`, `ts/eff`), the foreign corpus driver, the compatibility
policy and the case policy.

### 4.3 The typing

The target's scope has no parameter, so every stack is typed there (`stackTyped_nil`). Its
expansion must check at the body's signature to the same columns as at the module's. A typed
module-level layer reads only the source signature, so no parameter. The proof:

1. The module's part is typed at the source signature (the module check).
2. Every node of a typed program is typed in its environment, layers included
   (`NodeHasTy.replace_envAt`, `Laws/Program/Typing/Replace.lean`).
3. A typed program reads only its signature (`hasTy_sigProgram`, `Laws/Program/Typing/Restrict.lean`).
4. On such a program the checker answers the same at every extension (`check_restrict`,
   `Laws/Program/Signature.lean`), at the layer sort through `cata_layer_congr_on`.

One new lemma connects the expansion to the address: the node of the expanded program at a
target's path is the target's expansion (`LayerTerm.expandIn`), since no ancestor of a layer is a
reference. The memo cell at the target is typed at the module's signature, which every reader
then agrees with, so a shared entry has one set of columns.

### 4.4 Print, read and author

- `printDef` admits a reference to a module-level target, printed as the hoisted identifier. A
  body's own layers stay refused until step 3.
- The reader reads the identifier in a body back as the reference.
- `elaborateModule` places each shared layer at module level and turns every use into a reference.

### 4.5 As landed: step 2a

Step 2 lands in two parts. Part 2a is the syntax, the rule, the expansion bound, the typing and
the run. Part 2b is the print, the read and the authoring placement of 4.4 (§4.6).

Three points differ from 4.1 to 4.3:

- **A reference into the module names a whole module layer.** The target is the head of the
  spine's element, `2 :: 1 … 1 0` (`Path.spineHead`). A piece inside a module layer has no
  name, as a sub-expression of a module-level `const` has none. The refusal is `otherScope`.
- **The order is `Eff.refBefore`** (`Program/Refs.lean`), with the module test `Eff.inModule`.
  It is a strict order (`Eff.refBefore_irrefl`, `Eff.refBefore_trans`,
  `Laws/Program/PathOrder.lean`). The expansion's budget ranks by it (`Path.rankBy`).
- **The typing needs no address lemma.** The load discharges a third formation fact,
  `ModuleLayersTyped` (`Typed/Admission.lean`), from the module check
  (`moduleLayersTyped_of_typeOf`). The hop's point is typed by the extension lemma
  `checkLayer_ext`: the module's check at the source signature, extended to the site's, answers
  the site's type (`layerPointTyped_redirect_module`, `Typed/LayerArm.lean`).

The scope rule as a table:

| Site | Target | Rule |
| --- | --- | --- |
| any | a whole module layer | admitted; within the module, the target comes first |
| any | a piece inside a module layer | `otherScope` |
| body `k` or the main program | a layer of the same scope | admitted when it comes first |
| a module layer | a layer of a body or the main program | `notBefore`: the module's layers come first |
| body `k` or the main program | a layer of another body, or of the main program | `notBefore` when it comes after the site in program order, else `otherScope` |

### 4.6 As landed: step 2b

- **Print** (`printModuleLayers`, `Codegen/Print.lean`): each module layer is a constant named by
  its path, `const L_2_0 = …` for `Path.layerPath 0`, after the definitions and the services
  (a layer's body may invoke them) and before the hoisted layers (which may name it). Hoisting
  leaves the module's layers out (`Eff.refTargets`), so a reference to one prints as its name. A
  body may hold references into the module (`Eff.layersAreModuleRefs`); its own layer stays
  refused until step 3.
- **Read** (`readModule`, `moduleLayersOf`, `Codegen/Read.lean`): the declarations whose paths
  stand in the module rebuild the layers child, and they must be `Path.layerPath 0`, `1`, … in
  order; the others are put back at their paths.
- **The round trip** (`readModule_printModule_defs`, `Laws/Codegen/Module.lean`, claim
  `module-defs-round-trip`): restated for any module layers, with two premises more (each module
  layer reads back, and its name decodes). No hoisted layer stands in the module
  (`Eff.hoistAll_outside`, `Laws/Program/Hoisting.lean`). `blockReadable` checks both premises.
- **Author** (`elaborateModule`, `Program/Authoring.lean`): in a module with definitions, every
  declared layer is the block's module layer of its position, and every use, in a body, the main
  program or a later layer, is a reference to it. A declared layer nobody uses stays, as a
  module-level `const` does. A module with no definition places its layers at first use, as before.
- **Evidence.** The truth lane runs `pDefsModuleLayer` (`Test/Program/DefinitionsControls.lean`,
  `moduleLayerProg`) on rc.112 and agrees: success 7 (`make check-truth`). tsgo 7 admits its
  print (`make check-target`). Codex's review (`2026-10-10-module-layer-step2b-review/`) found a
  filter lemma reaching `Classical.choice` in `moduleLayersOf_split`; its proof-only repair is
  taken, and `#axiom_audit` over the slice's modules is within `[propext, Quot.sound]`.
- **Not established.**
  - The round trip is through `Api.readModule`, not `Api.admitModule`. `SourceBindings`
    (`Codegen/SourceBindings.lean`) refuses a forward reference inside a deferred closure, and a
    definition printed before the module constant it names meets that refusal. Admitting such a
    reference to a top-level constant needs its own design and refusal controls.
  - A module layer whose build invokes a definition that names the same module layer waits on its
    own build (Codex's observation). The checker does not refuse it, and no run here checks it.

## 5. Step 3: a body's layers, one build per call

### 5.1 The key

A build in a body is keyed by its path and the call that runs it. The owner ruled this form,
option B, on 2026-10-10; sharing by argument values (Effect's `LayerMap`) is a later opt-in
construct, scouted separately.

The call is named by the program, not minted by the store. An invocation at path `s`, run under
call `c`, runs its body under the call `s :: c` (`CallId := List (List Nat)`). A parameter's run
resumes its site under the caller's call, the tail. A site belongs to the call that made it, so
the tail is the site's call. The main program and the module run under no call, `[]`. A
module-level layer keys on its path alone (`Point.layerCall`: the call only for a path in the
root block's bodies, child `0`).

| Layer | Key | rc.112 |
| --- | --- | --- |
| module-level | its path | one object per module |
| in body `k` | its path and the running call of `k` | one object per evaluation of the body |
| reached by a reference in its own body | the reference's call | the same object within one call |

Two calls that one caller makes at one site share a name: a loop's iterations, or two fibers that
fork one program. Their builds never meet. An entry is visible only from a memo map below the
provide that built it (`MemoWorld.get` walks parents only). Below that provide, the code that
runs under the caller's call `c` is the programs passed at `s`, which are children of `s`, and
the code they reach through `c`'s own parameters runs under `c`'s caller. None of it is `s`
itself, so no call named `s :: c` starts there. A store counter would name every call apart, but
it costs a store step at each invocation, and its names depend on the schedule. The program's
names do not, so the key adds no fresh name to the schedule-independence argument (DET-1 to
DET-5).

### 5.2 What changes (step 3a, the machine)

- `LayerId := List Nat × CallId` (`src/Effect4/Machine/Alphabets.lean`). The memo operations
  keep their shape; the compile keys its five memo sites by `Point.layerKey`
  (`src/Effect4/Program/Compile.lean`), and the reference denotation mirrors it
  (`src/Effect4/Laws/Program/DenoteR.lean`).
- A point carries its call (`Point.call`), and so does a release's capture (`Capture.call`). The
  frames of `Point.params` are unchanged.
- The memo invariant types a cell by its key's path (`LayerCellTyped`,
  `src/Effect4/Laws/Program/Typed/Adequacy.lean`): every call of one body checks the layer at one
  signature, so the columns do not depend on the call.
- The OCaml route keys its memo table by the pair (`E4_memo.key`, `compare_key`,
  `ocaml/engine/e4_memo.mli`).

Step 3b, the printer, prints a body's layers inside the definition's suspension, so rc.112
creates one object per run of the body: `(a0) => Effect.suspend(() => { const L = …; return
body })`.

### 5.3 What it does not establish

- No closure: a nested definition stays outside the admitted fragment. An authoring helper that
  needs its parent's parameters takes them as parameters (lambda lifting at the surface). A layer
  in one body stays invisible to another body.
- No change to `fresh`: `LayerTerm.fresh` keeps its private memo map (DI-71's amendment).
- A call identity is never a value, so no observation reads it (unlike DI-73's fiber ids).

## 6. Order of work (ruled by the owner, 2026-10-10)

1. **Located reference refusals**: `Api.explain` names the bad reference's site and its reason
   (after its target, encloses it, no layer, a reference, another scope) in place of the
   root-level `referencesIllFormed`. An agent author then fixes the right site. The refusal codec
   is regenerated.
2. **Step 2**: the home of 4.2, then the rule, the expansion bound, the typing of 4.3, the print,
   the read and the authoring placement.
3. **HO-3**: the printer prints an invocation with programs, so a helper that takes a program
   (a retry, a timeout, a transaction wrapper) reaches TypeScript.
4. **Step 3**: the call identity in the machine, the memo key, the compile, the denotation and the
   OCaml route; then the printer admits a body's layers; then the typed chain's memo invariant.
   It lands before the printer admits a layer inside a body.

After step 3, a definition that returns a layer (`makeDbLive(url)`) builds on its call identity:
a later design question.

## 7. Placement

| Obligation | Concept | Claim, consumer | Requirement |
| --- | --- | --- | --- |
| the expansion bound under lexical order | `initial-algebras-folds` | `expanded_refs_nil_of_wf`; the checker's admission | R4 |
| a module-level target checks alike in every scope | `residual-program-typing` | `denote-typed`; `ref_builds` | R4; M7 |
| the memo key with the call | `store-typing` | `denote-typed`; `memoGet_implements`, `memoize_typed` | R4, R5; M7 |
| per-call print agrees with the machine | `translation-simulation` | the truth lane's counted builds (DI-71's fixtures) | R2, R3 |
