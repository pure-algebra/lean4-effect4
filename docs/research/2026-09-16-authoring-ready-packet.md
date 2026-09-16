# Ready packet: the authoring surface (plan S9a, the agent unlock)

Written 2026-09-16 at `0c3f605b`, while seat 2 runs. This is the packet the plan asked to prepare early (§5, S9a: "prepare these interfaces and their negative controls during S0/S1; they do not wait for loop implementation or P5"). It reuses the reader's name discipline and the hoisting functions that exist, and it needs no substitution in the core.

## 0. What the agents hit

From the dogfood findings (`2026-09-16-dogfood-findings-applied.md` §2): one index slip in a positional binder made a silent wrong program, and each brief spent four to six probes on indices; derived forms (retry, tagged catch, an option lookup, a row plus adapter) were rebuilt from primitives every time; a hand-written layer path that is wrong is a silently different program; the import header for a package handle had to be written by hand. The IR is right as an IR. What is missing is the surface that resolves names, expands forms, and refuses at a source position.

Today a program is authored as the IR itself (`Test/Api/ApiContract.lean:27`):

```lean
def pBind : Program :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))
```

`Var := Nat` (`Eff.lean:248`) is a de Bruijn level; `.var 0` is the first binder in scope, and the author counts.

## 1. The cleaner shape: the authoring surface is a reader

The plan's §3.6 considers construction callbacks (Lean functions receiving scoped symbolic terms) and then lists what they cost: elaboration at a declared scope, escaped-variable rejection, capture-avoiding renaming, an instantiation operation that removes a bound slot, a substitution evaluation law with a scoped-source premise, and a typing law that must not assume exact inferred-type equality. None of that machinery exists in the tree (no `subst`, no `instantiate`, no `shift`; only `Eff.weaken`, `effTy_weaken` at `Typing.lean:688` and `hasTy_weaken` at `Sound.lean:711`).

All of it disappears if the authoring surface is a **named source tree elaborated once**, the way the TypeScript reader already works. `readEff` recovers binders by comparing a source name with the positional name it expects (`Var.read`, `Read.lean:102`); an authoring reader does the same with names the author chose. Concretely:

- `Author.Src`: a first-order tree with the constructors of `Eff` and `Term`, where every binder carries a name and every variable is a name. It is never stored and never runs; it is the transient view the plan allows ("stored content contains existing `Term`/`Eff` data"), the same status the TypeScript text has.
- `Author.elaborate : Scope → Src → Except Refusal (Eff NativeOp)`, with `Scope := List String` in level order. A variable resolves to the nearest binding of its name (shadowing is allowed, since elaboration resolves it; the lexical check's refusal of shadowing exists to protect `Var.read` on foreign text and does not apply here). A free name refuses with the path to its use. Layer references are names too: an authored module is `(layers : List (String × LayerSrc), main : Src)`, each layer body elaborated in the empty scope, and the program is `Eff.restoreAll main' decls` (`Refs.lean:471`), which computes the paths that `LayerTerm.ref` stores. Nobody writes a path.
- Composition happens on `Src`, before elaboration. A fragment reused at two depths is the same `Src` elaborated twice, which is exactly the plan's "instantiate that syntax, not call it again" without an instantiation operation. A Lean function that builds `Src` from names (`fun x => …`) is ordinary programming over data, and nothing about its purity is assumed.
- Located refusals. Scope refusals carry the source path by construction. Typing refusals come from the one checker: `typeOfProgram` answers `none`, and a diagnostic projection `Typing.blame : Eff → Option (List Nat)` finds the deepest child whose `effTy` is `none` by the same function. It adds no second typing algorithm; it is a search over the checker's answers, and its law is `blame e = some p → effTy at p = none ∧ every proper child at p types`.

The theorems, all cheap because the elaborator is a fold that only resolves names:

1. `elaborate_rename`: renaming binders and their uses consistently leaves the elaborated program unchanged (the plan's "changing names alone leaves canonical core content unchanged").
2. `elaborate_scope`: an elaborated program has no free level beyond the scope's length (the premise `readable` and `effTy` already want).
3. `elaborate_print`: printing an elaborated program and reading it back is the identity on the readable fragment. This is free: it is `read_print` applied to the elaborated program.
4. Proof-carrying admission: `Author.check : Src → Except Refusal (Σ e, TypedProgram sig e)` is `elaborate` then `checkTypedProgram`; the certificate is the existing one, and the refusal names the path through `blame`.

## 2. Derived forms (S9b) on the same surface

`Forms.all` already holds nineteen templates with one expansion (`Template.expand`, typed by `Template.{argument,bind,onExit}_typed`). The combinators the plan lists are `Src → Src` functions whose elaborated image is a template expansion, so each carries its typing from the template's lemma and adds a law only where it claims a new behaviour:

| Combinator | Expands to | New law needed |
| --- | --- | --- |
| `seq`, `map` | `bind` + `succeed (app atom …)` | none |
| `when`, `select` | `branch` today, `select` after the constructs packet | none |
| `catchTag` | `catchIf` with a tag test; `Decision.tag` after the packet | inherits §3.1's bound |
| `retry n` | `iterate` (needs the packet); until then refused, not unrolled | attempts, error, cleanup |
| `use` | `acquireRelease` (release column `never`, D-I) | none |
| `forkScoped`, `join`, `race` | `withFiber` actions and `awaitFiber` | winner selection, loser interruption (the core's decisions) |
| `call row args` | `perform` through the row table; the import header derived from the `Ty.handle` targets the printer emits | none |

The unrolled loop is refused rather than emitted (the dogfood's finding on size), so `retry` and any fold wait for `iterate`. Everything else is available on the tree as it is.

## 3. Files

New, disjoint from every existing owner: `src/Effect4/Author/{Src,Elaborate,Blame}.lean`, `src/Effect4/Laws/Author/*.lean`, `Test/Author/AuthorContract.lean` rooted in `Test/All.lean`, and one facade line per function in `Api.lean` (`Api.author`, `Api.authorModule`). No change to `Eff`, `Typing`, `Print`, `Read`, `Refs` or the machine.

Because the owner set is disjoint, this packet can run as its own seat in a per-seat worktree while the constructs packet holds the main checkout, or after it; the only shared surface is `Api.lean`'s two new lines.

## 4. Controls

- Positive: the three API battery programs (`p42`, `pBind`, `pStrBind`) authored by name elaborate to the same trees; a two-layer module with a shared layer elaborates to the tree `hoistAll` recovers.
- Negative, one fact each: a free name at depth two refuses with its path; a shadowed name resolves to the nearest binder (and a control shows the outer one is not reached); a layer name with no declaration refuses; a typing refusal names the deepest failing child; a reused fragment at two depths elaborates to two different binder levels and the same shape.
- The rename theorem checked on the generated corpus: rename every binder of a readable program's named image and elaborate; the tree is unchanged (400 programs, no expected file, the theorem is the oracle).

## 5. Order and dependencies

1. `Src`, `elaborate`, `elaborate_rename`, `elaborate_scope`, the positive and scope controls. Nothing to wait for.
2. `blame` and `Author.check` with the typing controls. Nothing to wait for.
3. Named layers through `restoreAll`; `authorModule` through `emitModule`. Nothing to wait for.
4. The combinators of §2 that expand to existing forms; `select`, `catchTag` on `Decision` and `retry` follow the constructs packet.

What this packet does not do: it stores no `Src`, adds no evaluator, keeps one first-order `Eff` and one checker (DI-78), and does not promise that a combinator's Lean function is pure; only the elaborated syntax is checked.
