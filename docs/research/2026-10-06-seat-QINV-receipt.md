# 2026-10-06 seat QINV receipt: the Queue model's run invariant on the first profile

**The one thing to know before merging:** the three laws are proved with Codex's statement
unchanged, and no planned goal is open. The semantics report is stale after the merge: three
statements are new nodes of R12, and proposal P1 gives the registry's lines.

Brief: `docs/research/2026-10-05-claude-lead/briefs/seat-qinv-brief.md`. Design note:
`docs/research/2026-10-06-seat-QINV-design.md`, with an addendum for the landed names.

## 1. Base, head and commits

Branch `seat/qinv`, in the worktree `/Users/pooks/Dev/lean4-effect4-qsteps`. Base `4bd063a2`.
The last commit that changes a Lean file is `5dd784bd`. The commits after it hold the design
note's addendum and this receipt, and the last message names the head.

| Commit | Step | Content |
| --- | --- | --- |
| `1f6277a6` | the design note | the statements, the eleven arms, the invariant's parts, the proof's order |
| `83ff0a8c` | 1 | `FirstRunInv`, and `first_step_inv` as a placed planned goal; the law root's import |
| `678e643c` | 2 | `first_step_inv` proved in place |
| `4122fbbb` | 3 | `FirstOps`, `first_run_inv`, `empty_inv` and `first_run_flags` |
| `e6aa9993` | 4 | the battery, and its import in `Test/All.lean` |
| `5dd784bd` | 5 | doc comments inside the sentence limit, and three plain names; no statement changes |

## 2. Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Modules/Queue/Invariant.lean` | new: 2 structures, 1 abbreviation, 1 definition, 3 instances and 32 theorems |
| `src/Effect4/Laws.lean` | one import, after `import Effect4.Laws.Modules.Queue.Ops` |
| `Test/Program/QueueInvariant.lean` | new: 4 pinned outputs, 41 guards, 2 examples and 24 definitions |
| `Test/All.lean` | one import, after `import Test.Program.QueueTraces` |
| `docs/research/2026-10-06-seat-QINV-design.md`, and this receipt | new |

The new module imports `Profile.lean`, `Capacity.lean` and `Effect4.Laws.Auto.Semantics`. It
imports no module of a term, of a cell or of the machine. No existing file of the Queue changes,
and no definition of the model changes.

## 3. Commands, results and evidence

Each Lean, Lake and `make` command ran through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, named `SLOT`. `LEAN` stands for
`SLOT lake env lean -M6144 -DwarningAsError=true`, and `PROBE` for the same without the last
flag. `FLAGS` stands for `-o build -o ts/eff/node_modules -o harness/truth/node_modules`. The
scratch folder holds each log:
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/acf2315e-02ac-4acd-9ef9-b0734bd686a7/scratchpad/qinv/`,
named `SCRATCH`.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build`, on `4bd063a2` | `Build completed successfully (996 jobs).` Lake restored each module, so the run gave no gate line | tested |
| `LEAN Test/All.lean`, on `4bd063a2` | exit 0; the base's three gate lines, in the table below | tested: a fresh run of the gates |
| `PROBE SCRATCH/probe1.lean` | exit 0; Codex's definition and statement elaborate as written; the projection equation is proved | tested |
| `PROBE SCRATCH/probe2.lean` | exit 0; the counts of section 5 and of findings F3 to F5 | tested: a finite probe |
| `PROBE SCRATCH/probe3.lean`, then `LEAN SCRATCH/probe5.lean` | exit 0; the whole development as a scratch file, each statement at `[propext, Quot.sound]` | tested: before the first file of the slice |
| `PROBE SCRATCH/probe4.lean` | exit 0; the value of each planned control | tested |
| `SLOT lake build Effect4.Laws.Modules.Queue.Invariant Effect4.Laws`, at steps 1, 2 and 3 | `Build completed successfully (673 jobs).`, each time; the module takes under three seconds | proved, from step 2: the kernel accepts each theorem |
| `LEAN SCRATCH/step1-goal.lean` | exit 0; the plan status "goal", with the statement as its one next goal; axioms `[propext, sorryAx]` | tested: the goal of step 1 |
| `LEAN SCRATCH/step2-check.lean`, `LEAN SCRATCH/step3-check.lean` | exit 0; the axioms and the plan status of section 4 | tested |
| `LEAN Test/Audit/ProofStyle.lean`, at step 2 | exit 0; `proof style: 1914 recorded uses and 52 recorded unread commands in 1163 entries`, and no finding | tested: the ratchet refuses nothing |
| `LEAN Test/Program/QueueInvariant.lean`, at step 4 | exit 0 and no message, in 2.4 seconds | tested: the battery |
| `SLOT lake build Effect4.Laws.Modules.Queue.Invariant Test.Program.QueueInvariant`, at step 4 | `Build completed successfully (16 jobs).` | tested |
| `python3 SCRATCH/falsify.py`, then `LEAN SCRATCH/battery-red.lean`, at steps 4 and 5 | exit 1 from Lean: 45 errors, one at each of the 41 negated guards and of the 4 spoiled pins | tested: each check of the battery can fail |
| `LEAN SCRATCH/examples-red.lean` | exit 1: the fault equation without its premise fails at `close` and at `shutdown`; `decide` refuses the premise of the clashing list | tested: the red side of the two examples |
| `LEAN SCRATCH/battery-axioms.lean`, at steps 4 and 5 | 150 declarations of the two modules, none above `[propext, Quot.sound]` | tested |
| `PROBE SCRATCH/census.lean` | `#auto_census … using aesop`: 0 of 41 theorems closed from their statements. `#semantics_census`: 3 tagged, 38 untagged | tested |
| `SLOT make FLAGS check-docs`, at step 4 and again with this receipt | `PASS check-docs: every path, link, citation and make target in 76 documents resolves`, each time | tested |
| `SLOT lake build Effect4.Laws.Modules.Queue.Invariant Effect4.Laws Test.Program.QueueInvariant`, at step 5 | `Build completed successfully (675 jobs).` | proved, for the laws; tested, for the battery |
| `SLOT lake build`, on `5dd784bd` | `Build completed successfully (998 jobs).` in 29 seconds; the gate lines below | proved, for the laws; tested, for the batteries |
| `python3 scripts/check-language.py --strict` on the design note, on this receipt, and on the doc comments of the two Lean files (`python3 SCRATCH/docstrings.py` extracts them) | `PASS check-language: no finding`, for each | tested |

The gate lines of `Test/All.lean`, and the proof-style line of `Test/Audit/ProofStyle.lean`:

| Tree | Jobs | API and Laws-only modules | Modules, declarations | Planned goals, declarations on goals | Proof style: uses, unread, entries |
| --- | --- | --- | --- | --- | --- |
| `4bd063a2`, the base | 996 | 173, 305 | 746, 88410 | 24, 11 | no line: the run was `Test/All.lean` alone |
| `5dd784bd` | 998 | 173, 306 | 748, 88560 | 24, 11 | 1914, 52, 1163 |

The head's lines, from the default build:

```text
Effect4 library-root gate: 173 API/utility modules, 306 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 748 modules and 88560 declarations; [...] semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 24 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 11 declaration(s) rest on goals; no other declaration reaches sorryAx
```

The slice adds two modules and 150 declarations. The default build ran once at the end, as the
brief asks. The commits after `5dd784bd` change no Lean file.

Not run: `make check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script and `make gen-semantics`. Not run either: `make check-semantics`, which
needs the coordinator's report, and the large exploration of
`docs/research/2026-10-05-claude-lead/queue-contract/QueueLargeControls.lean`. No definition of
the model changed, so its two mutations stand as they stood. No TypeScript and no OCaml ran.
No evidence of the slice is host-only. The probes and the battery are bounded; the three laws
are not.

## 4. The statements as compiled

```lean
structure FirstRunInv (r : Run) : Prop where
  profile : FirstProfile r.s
  within : within r.s = true
  tidy : tidy r.s = true
  quiet : quiet r.s r.signalled = true
  ok : r.ok = true
  named : r.named = true

@[semantics "reactive-scheduling" (requirement := R12)]
theorem first_step_inv (r : Run) (op : Op) (h : FirstRunInv r)
    (first : firstOp op = true) (requested : Requested r.s op) :
    FirstRunInv (step .none r op)

def FirstOps (r : Run) : List Op → Prop
  | [] => True
  | op :: ops => firstOp op = true ∧ Requested r.s op ∧ FirstOps (step .none r op) ops

@[semantics "reactive-scheduling" (requirement := R12)]
theorem first_run_inv (r : Run) (ops : List Op) (h : FirstRunInv r) (first : FirstOps r ops) :
    FirstRunInv (ops.foldl (step .none) r)

theorem empty_inv (c : Nat) : FirstRunInv { s := { capacity := some (c + 1) } }

@[semantics "reactive-scheduling" (requirement := R12)]
theorem first_run_flags (c : Nat) (ops : List Op)
    (first : FirstOps { s := { capacity := some (c + 1) } } ops) :
    (ops.foldl (step .none) { s := { capacity := some (c + 1) } }).ok = true ∧
      (ops.foldl (step .none) { s := { capacity := some (c + 1) } }).named = true
```

All are in `namespace Effect4.Queue.Model`, in
`src/Effect4/Laws/Modules/Queue/Invariant.lean`. `FirstRunInv`, `Requested` and `FirstOps` each
have a `Decidable` instance there. The battery pins these outputs:

```text
'Effect4.Queue.Model.first_step_inv' depends on axioms: [propext, Quot.sound]
'Effect4.Queue.Model.first_run_inv' depends on axioms: [propext, Quot.sound]
'Effect4.Queue.Model.first_run_flags' depends on axioms: [propext, Quot.sound]
Effect4.Queue.Model.first_step_inv: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.first_run_inv: proved; nearest [Effect4.Queue.Model.first_step_inv]; 0 lemmas, 0 definitions
Effect4.Queue.Model.first_run_flags: proved; nearest [Effect4.Queue.Model.first_run_inv]; 0 lemmas, 0 definitions
next goals: 0
```

The counts are of the battery's tree, which holds no step of the proof. No declaration of the
module reaches `Classical.choice`, and the axiom gate holds each one at `[propext, Quot.sound]`.

## 5. The invariant that the proof needed, and why

**Codex's six parts, and no other.** The statement of the packet elaborates as written, and it
is true as written. The module states it as a structure, so that a proof names a part. The
`Decidable` instance reads the structure as Codex's conjunction.

**Why each part is a premise.** Each row is a red control of the battery. Its run holds every
other part, its step keeps `firstOp` and `Requested`, and the next run loses a flag.

| Part | Where the proof uses it | Red control: the run, and its step | The next `(ok, named)` |
| --- | --- | --- | --- |
| `profile` | every lemma: the closed forms of `Profile.lean` | capacity 0 with a pending offer that holds no message; `take 1 1 1` | `(true, false)` |
| `profile` | the same | a peeker 5 beside a signalled taker 1; `take 5 1 1` | `(false, true)` |
| `within` | `step_within` alone, for the next bound | capacity 1, messages `[7, 8]`; `dropTake 99` | `(false, true)` |
| `tidy` | the arms that keep the offers and the buffer | capacity 2, one pending offer, no message; `dropTake 99` | `(false, true)` |
| `quiet` | `bump_inv`, for a request that the step does not name | capacity 1, message `[7]`, taker 5, nobody signalled; `poll` | `(false, true)` |
| `ok` | `bump`'s conjunction | the empty queue, `ok := false`; `dropTake 99` | `(false, true)` |
| `named` | `bump`'s conjunction | the empty queue, `named := false`; `dropTake 99` | `(true, false)` |

**Why the six suffice.** The proof has three layers.

1. `step_state` carries `first_profile_closed` and `positive_suspend_step_capacity` to a run with
   any history. They give the next profile and the next bound, as the brief says.
2. `Flags before own after signals` is what the two flags ask of one step beside the bound. It
   has three fields. `spent`: no pending offer can enter the next state. `woken`: a signal of the
   step names each request of the next wake. Otherwise the old wake named the request, and it
   is not the step's own. `accounted`: the model's `accounted`. Each operation of the model has
   one lemma that states it, by the operation's own cases (`fun_cases`): `take_flags`,
   `offer_flags`, `poll_flags`, `withdrawTake_flags` and `withdrawOffer_flags`.
3. `bump_inv` joins such a step to a run of the invariant. It takes the run's invariant
   (`FirstRunInv r`), the next state's profile (`FirstProfile s`), the next bound
   (`within s = true`) and `Flags`. (Corrected by the coordinator on 2026-10-06, after
   Codex's source check. The sentence said: "It needs no profile.")

Three lemmas carry the content.

- `quiet_iff_wake`: a state is quiet exactly when each request that its wake names is
  signalled. It holds on every state, with peekers. So no proof reads a closed form of `quiet`.
- `wake_blocked`: where a take at the bounds one and one is not served, the wake does not name
  the take's own request. The take's enrolment changes no wake. So `bump` may drop the request
  from `signalled`. This is the model's half of `wait-registration-no-gap`.
- `acceptLoop_spent`: after the accept pass no offer is pending, or the finite room is spent. It
  asks no premise of the offers, and it is the other half of `acceptLoop_length_le`.

The reuse is the packet's: `first_profile_closed`, `positive_suspend_step_capacity`,
`acceptLoop_single`, `wake_profile` and `ready_profile`. No proof unfolds the accept pass a
second time, and no proof repeats the capacity statement.

A finite probe agrees with the step law on a universe of 10240 runs. Of them 2008 hold the
invariant, 44608 steps keep both premises, and none leaves the invariant. The battery keeps
this census as a guard. With one part dropped from the premise, steps lose a flag.

| Premise without | Steps that lose a flag |
| --- | --- |
| `within` | 40016 |
| `tidy` | 49616 |
| `quiet` | 8688 |
| each of the three: the profile and the two flags alone | 142624 |

## 6. Landed theorems and their placement

One placement holds for `first_step_inv`, `first_run_inv` and `first_run_flags`.

- Concept: `reactive-scheduling`; property: preservation of an explicit state invariant.
- Question: no registry claim points at them yet. P1 proposes two claims of the role
  `preservation`. They are the model's half of two open parts: `wait-registration-no-gap` under
  R12, and `waiting-request-obligation-preserved` under R11. Consumer: the run-level law of the
  Queue's wrapper (decisions row 275, point 2).
- Reach: the model's `step` at `Fault.none`. The observation is the run: its state, its
  `signalled` and its two flags. The fragment is the first operations, each with `Requested` at
  the run before it, from a run of `FirstRunInv`. Rows 219, 233, 255 and 275 bound it.
- Does not establish: nothing about a program, a typed cell or the machine. No delivery:
  `signalled` records that a step named a request, not that the request ran again. No liveness
  and no fairness: an invariant is not progress. Nothing of `close`, `shutdown`, `peek`, `await`
  or a batch. The premise `FirstOps` stays open for a caller: the wrapper owes it.
- Unlocks: it serves R12. The wrapper's run law may take both flags and the three properties of
  the state at each step of the model.

Each of the 29 other theorems is a step of one of these three. A section's head names the
statement that its lemmas serve. `tidy_iff` serves `bump_inv` and `first_step_inv`, and
`empty_inv` serves `first_run_flags`. The five `Flags` lemmas of the operations give a step's
facts with no flag: a consumer can use them as they are.

## 7. What stays open

- **No law relates a program's run to the model's run.** Connectors 3 to 6 of
  `Test/contracts/queue.contract.md` stay open. Neither `quiet` nor `accounted` proves one.
- **`FirstOps` is a premise.** The wrapper must give fresh identities and the bounds one and
  one, at each step.
- **The broader model has no theorem.** `close`, `shutdown`, `peek`, `await`, a batch, capacity
  zero, the unbounded queue and the two other strategies rest on the bounded exploration. The
  two findings F4 and F5 name parts that a broader invariant would need.
- **The four other clauses of `waiting-request-obligation-preserved`** are untouched:
  cancellation before consumption, a completed commit, a masked interruption and a stale token.
- **The semantics registry's lines** are the coordinator's: P1.

**R1 to R13.** The slice serves R12 and R11, and it touches no other requirement. R12: the three
statements are placed there. They are the model's half of `wait-registration-no-gap`, and the
part stays open: no statement is of a program's run. R11: `waiting-request-obligation-preserved`
has the same model half for its first clause, and it stays open. R10: the slice reuses
`first_profile_closed` and `positive_suspend_step_capacity` unchanged, and it adds no node to
`queue-expansion-agrees`. R1 to R9 and R13: untouched. No declaration of the slice names a
signature, a type, a cell, a service, a host answer, a face or a tape.

## 8. Findings

- **F1. Codex's statement is true as written** (proved). The brief allowed a stronger
  invariant, and none was needed.
- **F2. `Requested` guards the profile alone, on the probe's universe** (a finite probe). Of
  5592 steps without it, 4080 leave the invariant, and none loses a flag. The battery's control
  shows one: `offer 1 5` beside a waiting taker 1. No theorem states that the flags hold
  without the premise.
- **F3. Some operations outside `firstOp` keep the invariant on the universe** (a finite
  probe): `clear`, `dropPeek` and `dropAwait`, at 2008 runs each. The step law says nothing of
  them.
- **F4. `firstOp` guards a flag: the bounds of a request do not change.** A stored taker of the
  bounds one and one runs again as `take 1 2 3`. Its retry is not served, its stored record is
  ready, and the run loses `ok` (the battery's control; 40 runs of the universe). The contract
  names this premise: immutable bounds within a request. The broader exploration never retries
  an identity at other bounds, so it does not see it.
- **F5. `FirstProfile` guards a flag: a pending offer holds a message.** At capacity zero `pull`
  drops a pending offer that holds no message, with no signal, and the run loses `named`. No arm
  of the model stores such an offer (reading: `offer`, `offerAll`, `acceptLoop` and `pull`
  each keep a non-empty `rest`). A broader invariant needs this as a part.
- **F6. The model's closed forms on the profile sit above the term encoding.**
  `src/Effect4/Laws/Modules/Queue/Steps.lean` holds `settle_opened`, `pull_buffered`,
  `afterConsume_closed` and their kin. The new module is of the model alone, so it imports none.
  It states `settle_idle`, which is more general than `settle_opened`, and it reads `pull` on a
  buffered state inside `consume_flags`. P4 proposes the moves.
- **F7. `aesop` closes none of the 41 theorems from its statement** (`#auto_census`). The
  model's definitions are in no bank, and the proofs are rewrites along the definitions.
- **F8. The base's default build gave no gate line.** Lake restored `Test.All` from its cache.
  `LEAN Test/All.lean` gave the base's lines.

## 9. Proposals (not rulings)

- **P1. The registry**, for `tools/Tools/SemanticsRegistry.lean`, and then `make gen-semantics`.
  Add `Effect4.Laws.Modules.Queue.Invariant` to the default modules of `reactive-scheduling`:
  its 38 untagged theorems count as unplaced until then. Add two claims of the role
  `preservation`: `queue-first-step-invariant` with the pointer `first_step_inv`, and
  `queue-first-run-flags` with the pointer `first_run_flags`. Add one sentence to each of the two
  open parts. It says that the Queue model's half is proved on the first profile, and that the
  wrapper's run stays open.

  ```lean
  { id := "queue-first-step-invariant", concept := "reactive-scheduling", role := .preservation
    title := "One step of a first operation of the Queue's abstract model keeps the run invariant of the first profile: the profile, the buffer's bound, tidy, quiet at the run's signalled, and the two flags (the model's half of wait-registration-no-gap and of waiting-request-obligation-preserved; no program, no delivery of a signal and no liveness; decisions rows 219, 233, 255 and 275)"
    pointer := .witness `Effect4.Queue.Model.first_step_inv },
  { id := "queue-first-run-flags", concept := "reactive-scheduling", role := .preservation
    title := "From the empty queue of a positive capacity both flags of the Queue's abstract model hold after every list of first operations whose requests keep their premises at each prefix (the bounded exploration's two flags at every length, on the first profile; decisions rows 219, 233, 255 and 275)"
    pointer := .witness `Effect4.Queue.Model.first_run_flags },
  ```

- **P2. The architecture's two texts.** The row of `src/Effect4/Laws/Modules` in
  `docs/ARCHITECTURE.md` and the role of `src/Effect4/Laws/Modules/Queue` in
  `tools/Tools/ArchitectureRoles.lean` name the Queue's law files. Add: the model's run invariant
  on the first profile, with its step law and its run law (`Invariant.lean`).
- **P3. The contract packet**, `Test/contracts/queue.contract.md`. Add one row to its evidence
  table: the three laws, proved at `[propext, Quot.sound]`. Its section of controls says that the
  exploration remains finite evidence: add that the first profile now has the run law.
- **P4. Four moves, each in a file that this seat did not edit.**
  1. Move the model's closed forms of `Steps.lean` beside the model: `settle_opened`,
     `isDone_opened`, `isOpen_opened`, `pull_buffered` and `withdrawOffer_opened`. `settle_opened`
     then follows from `settle_idle`.
  2. Give `room_of` (`Capacity.lean`) the capacity as its one premise. It asks `Kept` and uses
     the capacity alone. `room_eq` of the new module is that statement, and it then goes.
  3. Move `acceptLoop_spent` and `accept_spent` beside `acceptLoop_length_le`, in `Capacity.lean`.
  4. Move the instance `Decidable (Requested s op)` beside `Requested`, in `Profile.lean`.
- **P5. A decisions row**, in the coordinator's words. A candidate: "The Queue model's run
  invariant on the first profile is landed (`first_step_inv`, `first_run_inv`,
  `first_run_flags`). The wrapper's run law owes `FirstOps`: fresh identities, and the bounds one
  and one at each step. It owes the relation of a program's run to the model's list of
  operations. A broader invariant needs two more parts: a request keeps its bounds, and a
  pending offer holds a message (this receipt, F4 and F5)."
