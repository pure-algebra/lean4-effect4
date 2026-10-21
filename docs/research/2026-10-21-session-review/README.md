# 2026-10-21 The service session, reviewed after Codex's landing

Status: a review of `docs/research/2026-10-21-session-landing/README.md` (`88d69b401`), with three refinements landed (decisions row 441).
It rules nothing beyond that row. The evidence words are those of `docs/core/controlled-english.md` §3.8.

## 1. The one thing to know

The landing is right. The lifetime is one ordinary program, built from the admitted block, invoked by position and admitted once. The host's replies keep call-instance admission.
Three things were simpler than written, and they are landed here.
The construction is a function of the object, not of the admitted program.
The lifetime provides nothing: the services of the typing signature are the host's at every target, and the requirement row names them.
A method is paired with its reply row once, instead of counted twice.

## 2. What was landed

| Change | Before | After | Evidence |
| --- | --- | --- | --- |
| The construction's domain | `ServiceSession.candidate : Built → String → Except _ Object`, reading only the object's fields | `Object.session : Object → String → Except _ Object`; `Built.session b s = Object.session (ofBuilt b) s >>= finish` | `Built.session_ok_iff`, `Built.session_retains`, reproved |
| The provision | the initializer's `requires`, each provided with the unit | none; `finish` requires every key left to be one the signature types (`ServiceSession.foreign` empty) | the session's TypeScript type is `Effect<void, never, "TodoRepo">` with no `provideService`; the `nonunit` and `remaining` fixtures admit with their key left to the host; an untyped key refuses at source admission (`foreignRemaining`) |
| The reply row's position | a counter `reply + 1` threaded through `dispatch`, parallel to `rows`' order | each method paired with `next + 1 + k` once (`zipIdx`) | the to-do's rows and replies unchanged (the session battery) |

The narrow build and the touched batteries pass. The axiom gate reports 185 declarations at `[propext, Quot.sound]` and no planned goal. The service-identity gate reruns the session's TypeScript print on Effect rc.112 under tsgo 7.

## 3. Where the review agrees

| Point | Evidence |
| --- | --- |
| The lifetime is one `Eff` program over the object's own block; no second representation | `Built.session_retains` |
| Calls are positional: `perform (.call k)`, `perform (.external i)`; no name is resolved after the view | `invokeAt`, `dispatch` |
| Construct, then admit once; the refusals keep their owners' locations | `Built.session_ok_iff`, `finish_admission_error_iff` |
| No raw-row guard; a bad reply is a refused verdict at the call instance | the withdrawn improvement of the host review; the `bogus` control of the design's probe |
| The protocol rows are the service's dual: `Session.next : unit → option (Σ tag, args)`, `Session.reply_m : Exit B E → unit` | `rows`, tested on the to-do |
| The printer's target-name repair (`serviceNamesFault` against `rowNameUses`) | `Test/Codegen/ServicesPrint.lean` |

## 4. What stays open

1. **The typed service view.** `serviceFaultOfIn` computes each method's argument types and discards them. Then five consumers recompute `methodArgs` with a refusal arm that formation already excluded: `Codegen.Print.methodField`, `methodClosure`, `Codegen.Surface.serviceSurface`, `Compiler.Inspect` and `ServiceSession.methodPort`. A `Service` whose methods carry their types makes formation "the view exists" and those five consumers total. Its own slice: it touches `Program/Services.lean`, the printer and `Laws/Codegen/Services.lean`.
2. **`SessionRefusal.scope` is unreachable.** The lifetime's source is written at the empty scope with minted names and positional operations. No name can be unbound, and no fixture reaches the case. A totality theorem of `ServiceSession.main` would remove it.
3. **`SessionRefusal.requirements` is unreachable.** Source admission refuses a read of a key the signature does not type, so `foreign` is empty on every admitted lifetime. The check stays as the witness until the checker's requirement calculus states it.
5. **The provision was wrong at the target.** The landing provided the initializer's keys with the unit. On the machine that is harmless, since the rows are answered by the host. On Effect it printed as a void `TodoRepo` service handed `undefined`, which the first repository call would have thrown on. The signature's services are the host's at every target: the program provides nothing, and the host's layer or the host's answers supply them. Landed the same day as the amendment of row 441 (2).
4. **The previous implementation.** It is the per-request model: one program a request, the layer rebuilt each time (the design's hole A). What it is, and when each part retires:

| Part | Where | Size | Retires with |
| --- | --- | --- | --- |
| the `run` command's per-request runner | `tools/Compiler/Run.lean` (`serve`, `runFrom`, `modulesOf`, `Request.moduleOf?`), `Main.lean` 306–326, `Groups.lean` (`todoHosted`, `todoScript`) | 1 module, 3 call sites | the driver slice: `run` drives the session object under the script and the host |
| the per-request consumer | `Test/Dogfood/Scenario/Todo/CachedProgram.lean` (`buildConsumer`, `consumerBuiltAt`), `Application.entry?`/`moduleOf` | 2 definitions, 9 battery lines | the driver slice |
| the OCaml to-do lane | `HostRun.serveBuilt*`, `HostLane.lean`, `ocaml/engine/test/todo/` (test 455, hosts 345, fixture 122, bench 247, `todo-host.txt` 93 lines), `todoLowered` roots | 1,267 OCaml lines, 5 roots | the engine slice: the engine runs a saved session object against a native host and the journals compare |

Nothing is deleted before its replacement runs (`AGENTS.md`, "Build in parallel, slot in, and delete at a good place").

## 5. What this review does not establish

No OCaml was run and the TypeScript gate reruns only the service-identity lane. The finite evaluations run on the to-do, the cached to-do and the landing's small fixtures. Host progress stays assumed, and the stage law stays outside Lean.
