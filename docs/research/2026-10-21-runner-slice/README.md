# 2026-10-21 Running a program: the reactor as a comodel, the queue as a client

Status: the design and the brief of one slice, for Codex to land. It rules nothing; it proposes decisions row 442.
The evidence words are those of `docs/core/controlled-english.md` §3.8. Every "tested" below is a finite evaluation run on the to-do at `62ccdab0b`.

## 1. The one thing to know

A program is a term of the free monad on its typing signature. A host is a comodel of that signature in a state. Running is the unique map out of the free monad into the state monad.
A client of a service is a program over the service's methods. The free monad's one-step unfolding makes every client a comodel of the session signature, with itself as its state.
The queue is the client whose continuations ignore replies, so it is a list.
This slice lands the queue and the tensor of two reactors in core, with their equations. It reads the agreement with the handled client off the to-do.
It lands no driver, generates no client, and leaves the general client-as-reactor as written equations.

## 2. The formal semantics, with the tree's names

### 2.1 Signatures and the free monad

A signature is a set of operations, each with a request type and an answer type: `Σ = { op : A_op → B_op }`.
In the tree a signature is the row table, `RowTable`, and each `Row` has its request, answer and error columns (`src/Effect4/Program/Eff.lean`).
The program is the free monad on Σ, which unfolds one step into a sum:

```text
T_Σ X  ≅  X  +  Σ_op ( A_op × (B_op → T_Σ X) )
```

In the tree the free monad is `Eff NativeOp`; an operation is `perform (.external i) a`, and the continuation is `bind` (`src/Effect4/Program/Eff.lean`).
The denotation reads a program this way (`denoteRows`, `src/Effect4/Laws/Program/DenoteRows.lean`).
Literature: Plotkin and Power 2003 (algebraic operations and generic effects); Plotkin and Pretnar 2013 (handling algebraic effects), by name.

### 2.2 The reactor is a comodel; running is the unique map

A comodel of Σ in a state S gives each operation a co-operation `ôp : A_op × S → B_op × S`.
In the tree a comodel is a reactor, `Reactor σ := Row → Val → σ → Option (Answer × σ)` (`src/Effect4/Run/Basic.lean`); `none` is a request the host does not answer.
The run is the unique map out of the free monad into the state monad, two equations:

```text
run_R : T_Σ X × S → X × S
run_R (return x, s)  =  (x, s)
run_R (op(a, k), s)  =  run_R (k b, s')     where (b, s') = ôp (a, s)
```

In the tree one round of `Run.drive` is bind, submit, apply (`src/Effect4/Run/Basic.lean`), and `agrees_hostRun_blocks` states that the journal's run is this fold (`src/Effect4/Laws/Program/ValidatedBlocks.lean`).
The journal is the trace of the interaction: the free monoid on `Command`, acting on the run (`replay_unique`, `journal_replays`).
Literature, by name: Plotkin and Power 2008 (tensors of comodels and models). Uustalu 2015 (stateful runners of effectful computations). Ahman and Bauer 2020 (runners in action).
The run as a natural transformation `T X × D Y → X × Y`, with D the cofree comonad on the dual signature, is an interaction law. Katsumata, Rivas and Uustalu 2020, by name. The tree states no interaction law.

### 2.3 The tensor of two reactors

Two comodels of disjoint signatures compose to one comodel of the sum signature over the product state: each co-operation acts on its component.
This is Plotkin and Power's tensor of comodels, by name.

```text
tensor (R, R') : comodel of Σ + Σ' in S × S'
  ôp (a, (s, s'))  =  ((b, (t, s'))  where (b, t) = ôp_R (a, s))          for op ∈ Σ
  ôp (a, (s, s'))  =  ((b, (s, t'))  where (b, t') = ôp_R' (a, s'))       for op ∈ Σ'
```

In the tree the reactor form answers the row by the left reactor when it answers, else by the right. `Reactor.first` on one state is the degenerate case (`src/Effect4/Run/Method.lean`).
Today the tensor exists twice outside core: `both` in the design's probe, `route` in `Test/Api/SessionFixtures.lean`.

### 2.4 The service block is a handler

The service's methods are operations a client may call: `Σ_svc = { m : A_m → Exit(B_m, E_m) }`; in the tree, `perform (.call k)`.
The block's bodies interpret each method by a program over the application's rows, `h : Σ_svc → T_Σapp`, and handling substitutes:

```text
handle_h : T_Σsvc X → T_Σapp X
handle_h (return x)  =  return x
handle_h (m(a, k))   =  h_m (a) >>= (handle_h ∘ k)
```

In the tree the block `Eff.defs decls bodies main layers` is `handle_h` applied to `main`: the machine's `call` is the substitution.
A client program is a `Σ_svc` term. The to-do's client, inlined, is `handle_h` applied. Tested: it builds over the service module, with the repository's four rows and one requirement.
Literature: Plotkin and Pretnar 2009 and 2013, by name.

### 2.5 A client is a reactor; the queue is the reply-blind client

The session signature makes the client's moves the server's operations:

```text
Σ_sess = { next : 1 → 1 + Σ_m A_m ,   reply_m : Exit_m → 1 }
```

In the tree these are the rows `Object.session` appends (`src/Effect4/Api/Session.lean`).
By §2.1's unfolding, a client `C : T_Σsvc 1` is a comodel of `Σ_sess` with itself as its state:

```text
asReactor (C) :  S = T_Σsvc 1
  nêxt    (⋆, return ⋆)  =  (none,       return ⋆)
  nêxt    (⋆, m(a, k))   =  (some (m,a), m(a, k))
  rêply_m (e, m(a, k))   =  (⋆,          k e)
```

A client whose continuations ignore replies is a list, and its state collapses to the remaining list:

```text
C_q  =  m₁(a₁, λ_. m₂(a₂, λ_. … return ⋆))     ≅     q = [(m₁,a₁), (m₂,a₂), …]
  nêxt    (⋆, q)  =  (head? q, tail q)
  rêply_m (e, q)  =  (⋆, q)
```

The agreement, observed on the replies and the application's store:

```text
run_{asReactor C} (session_h, C)   ≈   run_{R_app} (handle_h C)
```

Tested on the to-do in the queue case. The session program under the queue beside the repository records seven replies. The inlined client under the repository alone answers the same seven exits as nested pairs. Both leave the repository at `(3, [(2, "café 日本 🙂", false)])`.
The general case, `asReactor` of a program, needs the machine to step a client one call at a time. It is not this slice; its equations are above, and §5 places it.

### 2.6 The channel's type and its dual

The session rows are a session type, the server endpoint's protocol, and the client's type is its dual:

```text
S_srv  =  μX. &{ end : end,  m : ?A_m . !Exit_m . X }_m
S_cli  =  μX. ⊕{ end : end,  m : !A_m . ?Exit_m . X }_m
```

`next` is the offer and the receive together, or the end; `reply_m` is the send.
Literature, by name: Honda 1993 (types for dyadic interaction); Honda, Vasconcelos and Kubo 1998; Wadler 2012 (propositions as sessions). The encoding is Orchard and Yoshida 2016 (effects as sessions, sessions as effects), by name.
The tree states no session-type judgment; the rows are the encoding, and `Object.session` is its constructor.

## 3. The slice

Base: `62ccdab0b` or later on `refactor/phase1-phase3`. One branch, one worktree, commits by explicit paths after narrow builds.

### 3.1 Core: `src/Effect4/Run/Runner.lean`

A new non-module file, imported by `src/Effect4.lean` after `Effect4.Run.Method`. Its header states §2.2, §2.3 and §2.5 in the tree's words with the citations by name. It holds exactly:

```lean
/-- The tensor of two reactors: a row is answered by the left reactor when it answers, else by the
right, each on its own component of the product state (Plotkin and Power 2008, by name). -/
def Reactor.tensor {α β : Type} (r : Reactor α) (s : Reactor β) : Reactor (α × β)

/-- The queue: the reply-blind client as a reactor of the session rows. `next` answers the head
of the remaining requests, or none; a reply row answers the unit and keeps the queue. Rows are
known by their spellings `Session.next` and `Session.reply_`; no other row is answered. -/
def Reactor.queue (requests : List Val) : Reactor (List Val)
```

`queue` answers `Session.next` with `.ofExit (.success (.some r))` and the rest, or with `.ofExit (.success .none)` and `[]`. It answers a row whose spelling starts with `Session.reply_` with `.ofExit (.success .unit)` and the queue unchanged. It answers any other row with `none`.
The spellings are the ones `Object.session` writes. Read them from one definition beside `ServiceSession.rows`, used by the constructor and the queue both, never from two string literals.
No `String` traversal may reach `Classical.choice` in a definition the engine lowers. The fixtures use `String.startsWith` and `==` on spellings today, and the axiom gate decides.

### 3.2 Laws: `src/Effect4/Laws/Run/Runner.lean`

Imported by `src/Effect4/Laws.lean` after `Effect4.Laws.Run.Tape`. Placement before proof work: concept `host-session-protocol`, role compatibility, R6 and R13.
One registry claim, `queue-reactor`, in `tools/ProofGraph/Registry.lean` after `service-session-retains`, pointer `Effect4.Run.Reactor.queue_spec`:

```lean
@[semantics "host-session-protocol" (requirement := R6)]
theorem Reactor.queue_spec (requests : List Val) :
    (∀ row v q, row.spelling = "Session.next" →
      Reactor.queue requests row v q = some (.ofExit (.success (q.head?.elim .none Val.some)), q.tail)) ∧
    (∀ row v q, isReplyRow row = true → Reactor.queue requests row v q = some (.ofExit (.success .unit), q))
```

State it over the shared spelling definitions of §3.1, in whatever exact form compiles; the two equations of §2.5 are the content.
Two further theorems, `Reactor.tensor_left` and `Reactor.tensor_right`, state the tensor's two equations and are helpers of `queue-reactor`.
No theorem states the agreement of §2.5; it is a finite evaluation in this slice (§3.3), and §5 places the general case.

### 3.3 Batteries

- `Test/Api/SessionFixtures.lean`: delete `script` and `route`; the hosts are `Reactor.tensor (Reactor.queue requests) recordedRepository` and `Reactor.tensor (Reactor.queue requests) noHost`. Add the client fixture `clientMain`: the to-do's seven calls, each exit kept as nested pairs. Build it through `Author.build { m with main := clientMain }` over `application.serviceModule "TodoApp"`.
- `Test/Api/SessionContract.lean`: every existing line keeps its observation. Replies are read off the journal, `Run.rows` with the `.bound` verdict at the reply rows, not off a reactor's state. Add the agreement as two finite evaluations. The session under the queue and the inlined client give the same seven exits. They leave the same final repository. Add one control from the design's probe. A request outside the request row is refused at reply admission, and the run waits with no exit.
- `Test/Program/RunAdmissionControls.lean` or the nearest existing battery: `tensor_left` and `tensor_right` as readers on the to-do's two hosts.

### 3.4 Documents

- `docs/core/controlled-english.md` §3: three entries, one a line below.
- **tensor**: of two reactors, Plotkin and Power 2008 by name.
- **queue**: the reply-blind client as a reactor of the session rows.
- **client**: a program over a service's methods, `perform (.call k)` at the block. Its handled form is the block's main program.
- "Runner" is the literature's name for a reactor. It enters only the literature column, as the host entry already has it.
- `docs/core/semantics.md` concept 9: one entry for `queue-reactor` with the two equations, and one open part for the general client-as-reactor, with §2.5's equations and no pointer.
- `docs/core/host-boundary.md`: one paragraph. A deployment's reactor is whatever client exists outside the machine, read as a comodel. A gate's reactor is a trace replayed. No driver is generated.
- `docs/core/api-surface.md`: the `Run` row gains `Reactor.tensor`, `Reactor.queue` and the laws.
- `docs/STATE.md`: one line under what is true at HEAD.
- The decisions row is the coordinator's; propose it in the receipt.

### 3.5 Not in this slice

- No driver object, no driver file, no generated client: a client is user code (§4).
- No change to `Object.session`, to the printer, to TypeScript or to OCaml. If `ocaml/gen/closure-*.tsv` changes because `Runner.lean` is reached from a lowered root, regenerate (`python3 scripts/generate.py --only lcnf`) and run `make check-ocaml`; otherwise no behaviour gate is reached.
- No hosted stage: `asReactor` of a program stays equations.
- No new refusal alphabet, no `partial`, no `sorry`.

### 3.6 Finishing criteria, in order

1. `LEAN_NUM_THREADS=3 lake build Effect4.Run.Runner Effect4.Laws.Run.Runner Test.Api.SessionContract` and the direct importers.
2. `#axiom_audit Effect4.Run.Runner Effect4.Laws.Run.Runner Test.Api.SessionFixtures Test.Api.SessionContract` at `[propext, Quot.sound]`, no planned goal.
3. `LEAN_NUM_THREADS=3 make batteries-touched BASE=<base>`.
4. `python3 scripts/check-language.py --strict` on every document touched; `python3 scripts/check-docs.py`.
5. The receipt, folded into the landing's note. It records base and head, the changed files, the commands and their results, the axiom output, the open obligations and the proposed decisions row.

## 4. What comes next, so this slice does not pre-empt it

The handler is where composition starts. The client is a `Σ_svc` term and the block is `handle_h`. A second interpretation `h'` of the same methods is a second handler. Handlers compose along the signature, since a method's body over `Σ_app` is itself a client of `Σ_app`'s handler.
A handler written as an object is Ahman and Bauer's runner whose co-operations are computations, by name. It prints as a layer and lowers as a host record.
That is the next design note, after this slice lands. User code is the client, written by a person or an agent against the methods; it is never generated.

## 5. Placement of the open part

The general `asReactor` is a required property of concept 9. The session program under any client read as a reactor agrees with the client handled, on the replies and the store.
Its definition needs the machine to step a client one call at a time, the hosted stage. Until that definition exists the property has no pointer and no goal; §2.5 holds its equations, and `docs/core/semantics.md` lists it as open.
