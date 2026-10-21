(* E4_engine -- the drive loop over an instance of the generated engine.

   What it is: docs/research/2026-09-08-engine-a1-state.md §5.  Load a program, apply
   decisions, replay a tape, take a snapshot, and answer in the four-letter alphabet of
   proposal 16, or explicitly refuse the host numeric profile. Every accepted transition
   is the generated
   `stepDecisionState` (api_engine.ml:11424) and the answer is a projection of what that
   function and the generated `settled` (ocaml/engine/api_engine.ml) already say.

   The four letters, and where each comes from:
     Finished   every fiber has exited (`RunMachine.finished`, RunMachine.finished (src/Effect4/Machine/Fibers.lean)), the
                tape is spent, and the last step settled.
     Suspended  the TAPE ran out with the machine live and settled: a frontier whose
                command residue is empty.
     Delay      the FUEL ran out: `driveState` returned a NON-EMPTY command residue
                (replayEval (src/Effect4/Machine/Fibers.lean)), which is exactly `settled = false`.  `Api.Outcome`
                conflates this with Suspended (Outcome (src/Effect4/Api.lean)); the engine does not,
                because a caller that can give more fuel must be able to tell them apart.
     Refused    `ReplayResult.stuck` -- `Stuck.unknownFiber/unknownScope/unknownRace`.

   Outside_profile is separate from those four semantic answers. If a generated decision
   computes a value a crossing of the runtime library refuses (`Lcnf_crossing`: an exponent, a
   shift or an index past the target's int), step retains its INPUT machine and records this
   host refusal. Intermediate pure values from that decision are discarded; no claim of a
   simulated transition is made. The refused decision remains in replay_to's residue. The
   run's naturals are exact (Zarith's `Z.t`, M4); the engine's host face keeps ints for ids,
   tokens and counts, each a machine natural narrowed once (`Lcnf_nat.to_index_exn`).

   ONE loop over any instance.  {!Fast} is {!Make} of `Api_engine_inst`, which applies
   `E4_instance.Make` to the substituted carriers; the test tree applies {!Make} to the
   generated machine (`test/api_gen_inst.ml`, ocaml/gen/api_gen.ml over Lean's lists), the
   oracle.  The loop, the answer alphabet and every renderer exist once.  The declarations are
   e4_engine_intf.ml's, which this file includes.  A differential calls both engines through
   {!ENGINE} with one signature -- which is what `test/test_diff.ml` does over every corpus.

   Depends on: E4_engine_intf, Api_engine_inst, effect4_eff (Eff_types, Eff_val, Eff_codec),
   effect4_lcnf (Lcnf_crossing, Lcnf_nat), Zarith, stdlib.

   Behaviours:
   EN8 A program's literals are profile support's, Lean's: `literal_refusal` is
       `ProfileData.literalRefusal` at the selected profile (`rc112`, the profile as data;
       src/Effect4/Program/ProfileSupport.lean), lowered, and names the first literal above the
       bound at its node's address. A host driver asks it before `load` (E4_host H8). The
       engine requires a 63-bit integer host. The decision constructors check nothing: a raw
       decision is a trusted input.                       tested (numeric_ingress_check)
   EN9 A host's answer is host ingress (decisions row 394 (1)): `ingress` reads its value tree
       (Lean's `answerTree`, lowered), refuses it as `Not_a_value` when it is no Lean value
       (`Eff_val.valid`), and as `Unsupported` where Lean's profile support refuses it
       (`ProfileData.valueRefusal` at the selected profile, lowered). The refusal is a value
       at the answer's path, never an exception and never a defect. A driver asks it before
       the machine reads the answer (E4_host H6), as the kit does before either runner.
                                                          tested (answer_ingress_check)
   EN1 `run p ~fuel` is `Api.run p fuel []`: same outcome, same fiber table, same trace
       rows, same exits.  The check is against the instance's OWN `api_run` (the generated
       `Effect4.Api.run`, untouched) on every program of the corpus.
                                                          tested (test_engine, check 1/2)
   EN2 the alphabet REFINES Lean's and never contradicts it: Finished iff
       `Outcome.finished`, Refused iff `Outcome.stuck`, and Suspended-or-Delay iff
       `Outcome.frontier`.                                 tested (test_engine)
   EN3 `step` is total: it answers a machine for every decision and never raises -- the two
       `failwith` rows of the generated prelude (`sh_dispatcher_mk`, `sh_memo_map_mk`) are
       the only exception, and they fire on a construction the closure does not contain.
       test_engine counts them over the whole corpus and expects 0. A crossing's refusal
       (`Lcnf_crossing.Refused`) is caught and returned as Outside_profile with the input
       machine retained.
                                                          by construction; counted
   EN4 THE TAPE AXIS.  `replay_steps m tape` yields `List.length tape + 1` machines, the
       initial one first, position i equal to `replay m (the first i decisions)`, and the
       last equal to `replay m tape`.  It is TOTAL, and it is total because a viewer and a
       differential index by tape position and must have a machine at every one.
                                    tested (test_engine check 4, test_diff, test_replay_steps)
   EN4b THE RUN AXIS, and lane P6's finding F1.  Lean's `replayEval` (replayEval (src/Effect4/Machine/Fibers.lean))
       STOPS: at a stuck machine it answers `stuck why m` WITHOUT applying the decision, and
       after a step that left a non-empty command residue — the fuel ran out — it answers
       `frontier r.1` and reads no further.  Past that point Lean defines no machine, and
       `replay_steps` fills the gap by repeating the halted one, so a 64-decision tape at low
       fuel has 65 TAPE positions and 2 RUN positions.  P6 met this as one machine
       checkpointed 64 times.  The run axis is `replay_positions`, which ENDS at the stop and
       repeats nothing, and `replay_to`, which hands back the unread suffix — whose head is
       the REFUSED decision when the machine is stuck, at position
       `|tape| - |residue|`.  On the three corpora of `test_diff` 414 of 3 376 tapes stop
       early, so this is the common case and not a corner.
                                                        tested (test_replay_steps, 41 checks)
   EN5 a snapshot is the machine VALUE: {!snapshot} is the identity, and the value holds no
       mutable structure anywhere (brief §2.3).            by construction
   EN6 fuel is explicit and never implicit: no function of this module invents fuel.
                                                          by construction
   EN7 free rows cost no fuel and never reach the tape: every projection below is a pure
       function of a machine value (INV-TAPE-1, brief §2.4).  by construction

   The projection, stated so its limits are loud (deviation D-D3 of the lane receipt).
   `Api_engine_inst.event` and the generated machine's `run_event` are two OCaml types -- the
   generated type group lives inside each generated file, and inside the functor of the seam's
   -- and a differential must therefore compare RENDERINGS, not values.  {!ENGINE.trace_rows}
   renders every constructor of `RunEvent`, `Task`, `Prim`, `FrameEvent`, `Exit`, `Cause`,
   `Val`, `Ctx` and `Observer` in full.  Two payloads are NOT descended into and print as
   `<name>` and `<thunk>`: `Effect4.Program.EffName` and `Effect4.Program.EffThunk`.  They
   are program-shaped, not carrier-shaped -- no carrier can reach them -- but the claim
   "the trace rows are equal" is exactly this projection and nothing wider. *)

include E4_engine_intf.E4_engine
