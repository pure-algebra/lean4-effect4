# 2026-10-21 The host and runtime design, rederived

Status: a review of `docs/research/2026-10-21-host-runtime-design/README.md` (`9061ff5d7`), with two probes.
It rules nothing. The evidence words are those of `docs/core/controlled-english.md` §3.8.

Amended 2026-10-21 after Codex's refinement (`docs/research/2026-10-21-host-runtime-refinement/README.md`, `22bfa7473`).
Improvement 1 is withdrawn. The raw-row guard refuses a valid reply at a generic row, and it hides a bad reply as a wait (its `probe-guard.lean`).
Reply admission stays at the call instance, where the session applies it, and a refused verdict stays visible.
Improvements 2 and 3 stand; §2.4's reader must read `Run.rows` and keep the `bound` verdicts (its finding 2.4).

Both probes run clean against the design's compiled probes with `lake env lean -DwarningAsError=true`.
`audit.sh` reruns the design's audit, then runs and audits the review's two modules (`audit.out`).
The design's closure measurements (`closure.sh`) were not rerun here; the review takes them as reported.

## 1. The one thing to know

The design is right, and it is right by the method the owner asked for: every datum is what a law quantifies over.
The host is a comodel of the object's typing signature, read at its rows, with its initial state. The run's data is its record.
The lifetime is one run of the session program, and the per-run check of a journal is the evidence across the language boundary.

One thing should change before it lands. Assembly must apply reply admission.
The deployment's host is the assembled reactor behind the loaded object's named types (`Reactor.guardRows`).
Then every deployment is inside the envelope by construction, and the driver laws read it with no premise on its host (`probe-guard.lean`, proved).
That removes a proposed planned goal and a stored interface, and it fixes the shape of two carriers.

## 2. The rederivation

### 2.1 The host, from the free monad

A program over the object's signature is a term of the free monad over the stores' operations and the rows' operations.
The denotation reads it so (`denoteRows`, `src/Effect4/Laws/Program/DenoteRows.lean`).
A host is the other side of the row signature: a comodel, which answers each operation from a state and moves the state.
The tree's executable comodel is `Run.Reactor σ` (`src/Effect4/Run/Basic.lean`): the row, the request and the state in; an answer and the next state out, or none.
`reactorHost` (`src/Effect4/Laws/Api/SessionMeaning.lean`) reads it as the comodel the laws quantify over.

So the minimal host is a reactor, its state type and its initial state. The design's `Host` is that, and the census confirms nothing else is read.
The review agrees. Two remarks sharpen it:

- The envelope is reply admission. `Reactor.Envelops` says every answer the host gives is one the machine admits at the call it holds.
  `Reactor.guardRows` restricts any reactor to that, and `guardRows_envelops` proves it (`src/Effect4/Laws/Api/HostDrive.lean`).
  So "a lawful host" is "any host, behind reply admission", and the guard is where the seventh judgment enters a deployment.
- The three spellings are one comodel, as the design proves (`treeHost_eq_reactorHost`). The review adds nothing there.

### 2.2 The run, from the journal

The journal is the free monoid on run commands, and replay is its action (`replay_unique`, `src/Effect4/Laws/Api/Runner.lean`).
A run is an open and a journal; the session and the verdicts are folds (`journal_replays`, `src/Effect4/Laws/Run.lean`).
So the run's data is the open's arguments and the journal, which is `LiveRecord` (`src/Effect4/Run/LiveRecord.lean`).
The design pares it correctly: the binding is provenance (tested there), and the version field should be the store's spec, as for the object.

### 2.3 The lifetime, from the layer

The design derives "one run" from the decision alphabet.
No decision brings a new program into a machine, so a request can only arrive as a host answer.
The review agrees, and names the semantic reason beside the operational one.
A service block means a layer. In the emitted module `TodoAppLayer` is `Layer.effect`, built once.
Its methods close over the state it made. A per-request run rebuilds the layer each time, which is the plan's first hole, its hole A of §4.
The lifetime of a service is its layer's scope, and the session program is that scope as one program.
The operational step, that host-started roots are refused, is a ruling of `docs/core/system-map.md` §1.1, not a theorem of the algebra. The design says so, and the review keeps the distinction.

### 2.4 The session rows are the dual service

The design appends a request row and one reply row a method. The review names what that is.
A service is a coalgebra over its method signature: from a state and a method's arguments to the method's exit and a new state.
The session rows are that signature with its direction reversed.
Each method `m : A → Exit B E` becomes a reply row `Session.reply_m : Exit B E → unit`, and the request row's answer is the sum of the methods' arguments, or none at the end.
`Session` is to the service what `TodoRepo` is to the repository: a host namespace whose methods are the service's, inside out.
`probe-transcript.lean` tests the shape on the to-do: the reply rows are the methods, in order, each at its method's exit type.

The consequence matters for the evidence. Because a reply is a call, every output of a deployment is a bound call in its journal.
On the to-do's lifetime the 22 bound calls are 8 at `Session.next`, 7 at the reply rows and 7 at the repository (tested).
The seven requests at the reply rows are the seven replies the driver recorded (tested).
So `journal_bound_call` reads each reply as the Lean machine's own request at that point, and `replay_at_call_instance` reads each input as admitted.
The per-run check validates the whole interaction: inputs, outputs and the host's calls. The design states the calls' half; the review states that the outputs are inside it.

## 3. Where the review agrees

| Point | Evidence |
| --- | --- |
| The census method, and its result: one run, a reactor or a comodel, nothing else | `probe-census.lean` of the design |
| `Host` is the reactor, its state and its initial state | §2.1; the driver laws' binders |
| The interface is `o.app.rows`; no new carrier | `probe-host.lean` of the design, two `rfl` examples |
| The run's data is `LiveRecord` less its version; the binding is provenance | `probe-run.lean` of the design, tested |
| The lifetime is one run of the session program; `Object.session : Object → String → Except _ Object` | §2.3; `probe-session.lean` of the design, tested on two applications |
| `emit` is host-free by type; a deployment's run is the driver's run of the object's admission | `run_assemble_emit`, proved there |
| `journal_bound_call`, and the per-run check as the evidence across the language boundary | `probe-run.lean` of the design, proved; §2.4 here |
| The plan's hole D is refuted; the engine's roots lie under `Effect4` | the design's reading and `closure.out`, taken as reported |

## 4. The probes

| Probe | States | Result |
| --- | --- | --- |
| `probe-guard.lean` | artifacts are the bytes; the run's name is assembly's; `Deployable.reactor` is the host behind the loaded object's types; `reactor_envelops`, `reactor_exitsOnly`, `run_eq`, `run_denotes` | proved |
| `probe-guard.lean` | on the to-do's lifetime the guarded run has the unguarded run's observation, journal and host state; every call claim carries the assembled name; a host that answers outside the column waits with no refused verdict | tested |
| `probe-transcript.lean` | the reply rows are the service's methods at their exit types; the 22 bound calls are 8, 7 and 7; the replies are the bound requests at the reply rows | tested |

The probes import the design's compiled probes (`Probe.Deploy`, `Probe.Session`, `Probe.Run`) and the driver laws. They add no axiom and no planned goal.

## 5. Improvements, in order of value

1. **Assembly applies reply admission.** `Deployable.run` loads the object and drives under `d.host.reactor.guardRows b.app.types`.
   `run_denotes` then has four premises, the fragment, funding, rest and the exit, and none on the host.
   The reference host is unchanged by it on the whole lifetime (tested), and a bad host waits instead of reaching a refusal (tested).
   Cost: `answerAdmits` and `Reactor.guardRows` move from `src/Effect4/Laws/Api/HostDrive.lean` to the core run module, since the engine lowers the guard; the laws stay.
   Gain: the proposed planned goal `typed-host-envelops` is cut, since safety no longer needs it; the typed host's agreement stays a finite control.
2. **The artifacts are the bytes.** The design's `Artifacts.interface : RowTable` is a projection of the object, and it cannot carry the guard, which needs `app.types`.
   Read the interface off the loaded object; `Host.comodel` is named at the loaded program's table.
3. **The run's name is the deployment's identity, given at assembly.** The design writes the constant `"deployment"`. Every call claim carries the name (tested), so two deployments of one object must differ there.
   This also settles open point 5: the name is the identity, and the header's binding goes with the next wire slice, as recommended.
4. **The call claim names the object, not the table.** Open point 4 recommends a digest of the rows. The run's name and its object determine the table, and `staleCall` still checks each request against the machine.
   Carry `Object.ref` in the claim, or nothing beside the name; the digest of the rows alone names less than the object.
5. **The guard in the engine.** With point 1 the OCaml engine must apply the same guard, so `Reactor.guardRows` joins the engine's roots (`recipe-engine.json`). It is a filter over `answerAdmits`, which the kit's reply checks already lower.
6. **Names.** `Host` collides with `Run.Tree.Host` (`src/Effect4/Run/Tree.lean`) and the to-do's `Typed.Host`. Place it as `Run.Host` beside `Reactor`.
7. **The record's version.** `LiveRecord.version` is the spec's job, as point 4 of the program-domain review says. The design agrees; the slice should do it.
8. **The session refusal alphabet.** The probe's strings become a sum in the slice, as the design plans. One case a probe did not test: a block with no definition block at all.

Points 1 to 3 have probes. Points 4 to 8 are placements and names.

## 6. What this review does not establish

The probes restate the design's laws through a guarded driver; they add no reach beyond `runWith_guarded_denotes`.
Every finite evaluation runs on the to-do's lifetime alone. The closure counts are the design's, not rerun.
No OCaml was compiled or run, and no TypeScript was checked. Host progress stays assumed, and the stage law stays outside Lean, where `docs/core/host-boundary.md` puts it.
