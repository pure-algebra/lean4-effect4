import Lean

/-! Authored concepts and evidence pointers; facts and statuses are read from the environment.
The value below is the ten-concept registry Gemini drafted (2026-10-01), checked by the
coordinator against the tree and adopted with three repairs: the roots load the whole proof
graph, the frontier claim names the theorem its title states, and the M7 capstone is one claim
per ledger goal. A literature `work` is an author-year key of the source index
(`docs/research/2026-10-01-semantics/sources/README.md`) and a `locator` a row id of the
citations audit (`citations-audit.md`); checking keys against the index is owed. -/
namespace Tools.Semantics
open Lean

/-- The proof role a claim plays. The first ten are the owner's lemma list (status note §7b,
line 195); `adequacy`, `simulation` are Codex's (review §6); `compatibility` and
`fundamentalProperty` are the tree's own words for the slice's claims
(`Laws/Program/Typed/Seq.lean:55`, `Laws/Program/Typed/Assembly.lean:1636`). -/
inductive Role
  | inversion | canonicalForms | weakening | substitution | progress | preservation
  | monotonicity | transitivity | antisymmetry | decidability | adequacy | simulation
  | compatibility | fundamentalProperty
deriving Repr, Inhabited, BEq

/-- What the claim points at. Authored; never a status (§3 derives the status). -/
inductive Pointer
  /-- a theorem stating the claim, or a planned goal (`proof_goal`, decisions row 203); its status is
  derived from its proof: wanted for a goal, modulo when it rests on goals, proved otherwise (not
  `theorem`, a keyword, which v2 had to escape) -/
  | witness (name : Name)
  /-- a theorem refuting the claim, and the register row that records it -/
  | refutedBy (registerId : String) (witness : Name)
  /-- no witness, no goal, no refutation; the reason is required -/
  | absent (reason : String)
  /-- an external statement with no local evidence -/
  | assumed (source : String) (reason : String)
deriving Repr, Inhabited

/-- A key into seat A's source index (`docs/research/2026-10-01-semantics/sources/README.md`)
with a locator read off that file; never a locator from memory (owner, 21:30). -/
structure LiteratureRef where
  work : String
  locator : String
  relation : String   -- definitionUsed | proofTechnique | adaptedResult | analogy | excludedFeature
deriving Repr, Inhabited

structure Claim where
  id : String                     -- kebab-case, unique
  concept : String                -- a `Concept.id`
  role : Role
  title : String                  -- words; the statement itself is printed from the environment
  pointer : Pointer
  /-- register rows whose attacked statement is this claim's, kept open beside the status -/
  contestedBy : List String := []
  literature : List LiteratureRef := []
deriving Repr, Inhabited

structure Concept where
  id : String                     -- kebab-case, unique
  title : String
  /-- modules whose untagged theorems default to this concept (`inherited`, provisional) -/
  defaultModules : List Name := []
deriving Repr, Inhabited

/-- An applicability decision (R6): what a concept's claims exclude, by a decisions row.
The row's owner (`who`) is read from the register, not written here. -/
structure Cut where
  concept : String
  decisionRow : Nat
  excluded : String
  reason : String
deriving Repr, Inhabited

/-- A requirement row of the system map (`docs/core/system-map.md` §8) with the plan nodes that
state it in Lean: planned goals or theorems. Its status is derived from theirs. -/
structure Requirement where
  id : String                     -- the row, `R1` … `R13`
  title : String
  top : List Name
  /-- the parts of the row not yet stated as goals, each with what it waits on; while one remains,
  the requirement is open whatever its nodes' statuses -/
  openParts : List String := []
deriving Repr, Inhabited

structure Registry where
  roots : List Name               -- loaded with `importModules`; stated in the report
  concepts : List Concept
  claims : List Claim
  cuts : List Cut
  /-- the requirements with plan nodes, in the system map's order -/
  requirements : List Requirement := []
  /-- module prefixes whose planned goals join the plan as nodes -/
  planScope : List Name := []
  /-- the acceptance programs (decisions row 206): each battery's namespace, which declares the
  literal `stage` it reaches and the requirements it `waitsOn`; each module is a root -/
  acceptance : List Name := []
deriving Repr, Inhabited

def registry : Registry where
  roots := [`Effect4.Laws, `Test.Program.TypedProgBindRed, `Test.Program.ProtocolPosts,
    `Test.Dogfood.P1HttpCache, `Test.Dogfood.P2HandlerLayers, `Test.Dogfood.P3WorkerQueue,
    `Test.Dogfood.P4RateLimiter, `Test.Dogfood.P5LedgerService,
    -- the scenarios of the acceptance programs (decisions row 254): their placed claims and
    -- their planned goals are nodes of the plan
    `Test.Dogfood.Scenario, `Test.Dogfood.Scenario.Workers, `Test.Dogfood.Scenario.Routing,
    `Test.Dogfood.Scenario.Atomic, `Test.Dogfood.Scenario.Timeout]
  acceptance := [`Test.Dogfood.P1HttpCache, `Test.Dogfood.P2HandlerLayers,
    `Test.Dogfood.P3WorkerQueue, `Test.Dogfood.P4RateLimiter, `Test.Dogfood.P5LedgerService]
  concepts := [
    { id := "store-typing"
      title := "Store Typing: World-indexed semantic value membership (Fits) and store typings"
      defaultModules := [
        `Effect4.Laws.Program.Typed.Membership,
        `Effect4.Laws.Program.Typed.World,
        `Effect4.Laws.Program.Typed.Validity,
        `Effect4.Laws.Modules.Queue.Typing,
        -- the typing judgment of a builder's term and the term checker's rules in their
        -- introduction form: each consumer is a node of R4 (seat QTYPES, decisions row 257)
        `Effect4.Laws.Modules.Queue.Checking,
        `Effect4.Laws.Program.Typing.TermIntro,
        -- Semaphore's typing statements, and its model's profile: the closure is this
        -- concept's node, and the two facts of a visit carry their own tag (seat SEM's
        -- receipt, item 10, row 3, option (b); decisions row 265)
        `Effect4.Laws.Modules.Semaphore.Typing,
        `Effect4.Laws.Modules.Semaphore.Profile
      ] },
    { id := "residual-program-typing"
      title := "Residual Program Typing: TypedProg, the protocol-indexed judgment on residual programs"
      defaultModules := [
        `Effect4.Laws.Program.Typed.Residual,
        `Effect4.Laws.Program.Typed.Seq,
        `Effect4.Laws.Program.Typed.Assembly
      ] },
    { id := "scope-lifetime-finalization"
      title := "Scope Lifetime & Finalization: Lifetimes, finalizer registration, and LIFO unwinding"
      defaultModules := [
        `Effect4.Laws.Machine.ScopeMachine,
        `Effect4.Laws.Machine.ScopeRestoration
      ] },
    { id := "reactive-scheduling"
      title := "Reactive Scheduling: Multi-fiber execution, decision steps, and configuration invariants"
      defaultModules := [
        `Effect4.Laws.Machine.Scheduling,
        `Effect4.Laws.Machine.Lift,
        `Effect4.Laws.Program.Typed.Scheduler,
        `Effect4.Laws.Modules.Queue.Capacity,
        `Effect4.Laws.Modules.Queue.Profile
      ] },
    { id := "exact-codecs"
      title := "Exact Codecs: Invertible embeddings for JSON and Schema representations"
      defaultModules := [
        `Effect4.Laws.Schema.Codec,
        `Effect4.Laws.Codegen.ReadPrint,
        `Effect4.Laws.Codegen.Read
      ] },
    { id := "subtyping-algebra"
      title := "Subtyping Algebra: Preorder laws, normalization, and join-semilattice on CTy"
      defaultModules := [
        `Effect4.Laws.Program.TypeAlgebra
      ] },
    { id := "initial-algebras-folds"
      title := "Initial Algebras & Folds: Free syntax objects, catamorphisms, and fold uniqueness"
      defaultModules := [
        `Effect4.Laws.Program.Folds.Ty,
        `Effect4.Laws.Machine.Folds.Val,
        `Effect4.Laws.Machine.Folds.Stores
      ] },
    { id := "context-requirements"
      title := "Context Requirements: Graded coeffects, requirement rows, and layer discharge"
      defaultModules := [
        `Effect4.Laws.Effects.Protocol
      ] },
    { id := "host-session-protocol"
      title := "Host Session Protocol: Session automaton, external reply ingestion, and boundary capabilities"
      defaultModules := [
        `Effect4.Laws.Api.HostSession,
        `Effect4.Laws.Api.Frontier,
        `Effect4.Laws.Api.Guard
      ] },
    { id := "translation-simulation"
      title := "Translation & Simulation: Semantic preservation, replay relations, and capstone M7"
      defaultModules := [
        `Effect4.Laws.Program.Agreement.Machine,
        `Effect4.Laws.Program.Agreement.Loop,
        `Effect4.Laws.Program.LoopAgreement,
        `Effect4.Laws.Program.RuntimeR,
        `Effect4.Laws.Machine.Book,
        `Effect4.Laws.Modules.Queue.Relation,
        `Effect4.Laws.Modules.Queue.Reading,
        `Effect4.Laws.Modules.Queue.Steps,
        `Effect4.Laws.Modules.Semaphore.Relation,
        `Effect4.Laws.Modules.Semaphore.Reading,
        `Effect4.Laws.Modules.Semaphore.Steps
      ] }
  ]
  claims := [
    { id := "type-metadata-exact", concept := "exact-codecs", role := .compatibility
      title := "Structural TypeScript metadata retains the exact stored Ty declaration"
      pointer := .witness `Effect4.Codegen.Metadata.type_metadata_exact },
    { id := "raw-formation", concept := "subtyping-algebra", role := .decidability
      title := "Raw formation checking agrees with distinct record names, admitted map keys and a deferred's admitted error column"
      pointer := .witness `Effect4.Program.Formation.checkInput_eq_none_iff },
    { id := "instantiated-formation", concept := "residual-program-typing", role := .compatibility
      title := "Successful row template use checks instantiated map keys and deferred error columns"
      pointer := .witness `Effect4.Program.rowTy_instantiated_formed },
    -- 1. store-typing
    { id := "fits-mono", concept := "store-typing", role := .monotonicity
      title := "Membership is monotone under host world order"
      pointer := .witness `Effect4.Program.Typed.fits_mono
      literature := [
        { work := "TAPL", locator := "§13.5, pp. 165–169", relation := "proofTechnique" },
        { work := "Ahmed2004", locator := "audit P1", relation := "adaptedResult" }
      ] },
    { id := "fits-subn", concept := "store-typing", role := .preservation
      title := "Membership is closed under the checker's subtyping order"
      pointer := .witness `Effect4.Program.Typed.fits_subN
      literature := [
        { work := "TAPL", locator := "§15.1, p. 181", relation := "definitionUsed" }
      ] },
    { id := "fits-normalize", concept := "store-typing", role := .compatibility
      title := "Membership is invariant under type normalization"
      pointer := .witness `Effect4.Program.Typed.fits_normalize
      literature := [
        { work := "Castagna2024", locator := "audit P6", relation := "adaptedResult" }
      ] },
    { id := "fits-scope-inv", concept := "store-typing", role := .inversion
      title := "A member of Ty.scope is a present scope's handle"
      pointer := .witness `Effect4.Program.Typed.fits_scope_inv
      literature := [
        { work := "ATTAPL", locator := "ch. 3, pp. 87–136", relation := "analogy" }
      ] },
    { id := "term-maps-mono", concept := "store-typing", role := .monotonicity
      title := "A binder term's map between member types is monotone under host world order"
      pointer := .witness `Effect4.Program.Typed.TermMaps.mono
      literature := [
        { work := "Ahmed2004", locator := "audit P1", relation := "adaptedResult" }
      ] },
    { id := "term-typed-maps", concept := "store-typing", role := .fundamentalProperty
      title := "A binder term the term typer admits at the node's environment and the cell's type maps that type into its own type at every later world, over an environment that fits (the state plan's T3b)"
      pointer := .witness `Effect4.Program.Typed.termMaps_of_typed
      literature := [
        { work := "Ahmed2004", locator := "audit P1", relation := "adaptedResult" }
      ] },
    { id := "fold-typed-atomic-update", concept := "store-typing", role := .compatibility
      title := "The list fold with two binders, the accumulator and the element: its scope, evaluation, failure, weakening and typing rules; a fold the checker types answers a member of its type over values that fit, in a fixed world; a term reads back from its printed image; one Ref.modify whose term the checker types is one store step that answers B and stores A (decisions row 228)"
      pointer := .witness `Effect4.Program.Typed.fold_typed_atomic_update
      literature := [
        { work := "Ahmed2004", locator := "audit P1", relation := "adaptedResult" }
      ] },
    { id := "handle-identity-laws", concept := "store-typing", role := .canonicalForms
      title := "The identity of a handle in a term: sameHandle is total on two members of one handle type at any payload types, reflexive and symmetric, and it decides key equality; a handle an allocation just made is the same as no handle of a value that fits the earlier world; a later world keeps a list's membership; a term's handles are its environment's (decisions row 229)"
      pointer := .witness `Effect4.Program.Typed.handle_identity_laws
      literature := [
        { work := "Ahmed2004", locator := "audit P1", relation := "analogy" }
      ] },
    { id := "saved-mask-image-membership", concept := "store-typing", role := .canonicalForms
      title := "The mask's saved state: membership at Ty.maskRestore is exactly the two saved images, in Fits and in the shape check; the image is no Boolean, a Boolean is no image, and no subtyping relates the two types; the target is reserved against an external allocation, a host answer column and a service carrier; an image holds no handle, so every world, every store and every environment keep its membership (decisions row 244; no reply admission)"
      pointer := .witness `Effect4.Program.Typed.saved_mask_image_membership },
    { id := "store-safety", concept := "store-typing", role := .progress
      title := "Store safety through inductive configuration typing"
      pointer := .absent "Machine safety is established by inductive configuration typing rather than operational progress (decisions row 139)"
      literature := [
        { work := "TAPL", locator := "§13.5, pp. 165–169", relation := "excludedFeature" }
      ] },

    -- 2. residual-program-typing
    { id := "seq-typed", concept := "residual-program-typing", role := .compatibility
      title := "The seqR compatibility lemma: denoteR sequences with typed continuations"
      pointer := .witness `Effect4.Program.Typed.seq_typed
      literature := [
        { work := "ATTAPL", locator := "ch. 3, pp. 87–136", relation := "adaptedResult" }
      ] },
    { id := "close-typed", concept := "residual-program-typing", role := .preservation
      title := "Closing a typed program with unguard preserves typing"
      pointer := .witness `Effect4.Program.Typed.close_typed
      literature := [
        { work := "deVilhenaPottier2021", locator := "audit P8", relation := "proofTechnique" }
      ] },
    { id := "sound-at-app-signature", concept := "residual-program-typing", role := .compatibility
      title := "Meaning, loop and run soundness at an application's signature: any table, service declarations at fresh codes, by C3's reflection (R1)"
      pointer := .witness `Effect4.Program.Denote.run_typed_app },
    { id := "straight-meaning-typed", concept := "residual-program-typing", role := .fundamentalProperty
      title := "Typed straight programs return ExitHasTy from the empty environment and stores"
      pointer := .witness `Effect4.Program.Denote.meaning_typed },
    { id := "denote-typed", concept := "residual-program-typing", role := .fundamentalProperty
      title := "The denotation of a checked program is TypedProg at its certificate (M5)"
      pointer := .witness `Effect4.Program.Typed.denotesTyped
      contestedBy := ["E4-TYPED-CE-020", "E4-TYPED-CE-021", "E4-TYPED-CE-022", "E4-TYPED-CE-023",
        "E4-TYPED-CE-031"]
      literature := [
        { work := "XiaEtAl2020", locator := "audit P37", relation := "definitionUsed" }
      ] },
    { id := "rebuild-admission", concept := "residual-program-typing", role := .compatibility
      title := "Successful rebuilding checks the exact candidate under the retained host table and row names (Built.rebuild)"
      pointer := .witness `Effect4.Program.Authoring.rebuild_spec },
    { id := "denote-typed-layer-free", concept := "residual-program-typing",
      role := .fundamentalProperty
      title := "M5 on the layer-free fragment: every arm but provideLayer's, assembled by induction on fuel"
      pointer := .witness `Effect4.Program.Typed.denotesTyped_of_layerFree
      literature := [
        { work := "XiaEtAl2020", locator := "audit P37", relation := "definitionUsed" }
      ] },
    { id := "load-typed-layer-free", concept := "residual-program-typing", role := .preservation
      title := "The typed load on the layer-free fragment: a checked program loads into J (M5's load connector, the marker premise discharged)"
      pointer := .witness `Effect4.Program.Typed.loadsTyped_of_layerFree },
    { id := "provide-layer-arm", concept := "residual-program-typing", role := .compatibility
      title := "The layer family's arm: a layer build at an admitted layer point answers the built context at the layer's checked error type, and the provide protocol around it is typed (decisions rows 176 (b), 185-187)"
      pointer := .witness `Effect4.Program.Typed.provideLayerArm
      contestedBy := ["E4-TYPED-CE-023", "E4-TYPED-CE-031"] },
    { id := "load-typed", concept := "residual-program-typing", role := .preservation
      title := "M5: a lawful, checked, closed source with an empty requirement row loads into J"
      pointer := .witness `Effect4.Program.Typed.loadsTyped },
    { id := "load-typed-checked", concept := "residual-program-typing", role := .preservation
      title := "The typed load for every checked program: M5 with no lawful-signature or closed-row premise"
      pointer := .witness `Effect4.Program.Typed.load_typed },
    { id := "bind-closed", concept := "residual-program-typing", role := .compatibility
      title := "TypedProg is closed under bind"
      pointer := .refutedBy "E4-TYPED-CE-030" `Test.Program.TypedProgBindRed.typedProg_not_bind_closed
      literature := [
        { work := "deVilhenaPottier2021", locator := "audit P8", relation := "excludedFeature" }
      ] },
    { id := "guard-bind-typed", concept := "residual-program-typing", role := .compatibility
      title := "The guard compatibility lemma: a guarded program bound into its arms is typed (the general form of seq_typed, row 148)"
      pointer := .witness `Effect4.Program.Typed.guardBind_typed },
    { id := "on-failure-typed", concept := "residual-program-typing", role := .compatibility
      title := "The onFailure shape (catchCause, catchIf, orDie, a finalizer's cleanup) is typed"
      pointer := .witness `Effect4.Program.Typed.catchGuard_typed },
    { id := "all-guard-typed", concept := "residual-program-typing", role := .compatibility
      title := "The all and onExit guard shapes (exit, matchCause, a finalizer's boundary) are typed"
      pointer := .witness `Effect4.Program.Typed.allGuard_typed },
    { id := "on-exit-typed", concept := "residual-program-typing", role := .compatibility
      title := "The onExit shape onExitR builds: the body and the finalizer at their types"
      pointer := .witness `Effect4.Program.Typed.onExit_typed },
    { id := "scoped-body-substitution-boundary", concept := "residual-program-typing", role := .compatibility
      title := "A restore site is one node that binds nothing, with its checked body at child 0: both saved choices run that one body in the node's environment; a typed point at the node denotes a typed program, its saved term evaluates to an image, and its body's point is typed at the node's type; a saved value passed as data keeps its choice and holds no handle; the mask's builder is the program's own expansion over bind (decisions rows 245, 246; the restore node's half of the claim; no agreement with a target)"
      pointer := .witness `Effect4.Program.Typed.scoped_body_substitution_boundary },

    -- 3. scope-lifetime-finalization
    { id := "close-idempotent", concept := "scope-lifetime-finalization", role := .preservation
      title := "Closing an already-closed scope returns void without re-running finalizers"
      pointer := .witness `Effect4.Scope.close_idempotent
      literature := [
        { work := "PFPL", locator := "ch. 28, §28.1, p. 261", relation := "adaptedResult" }
      ] },
    { id := "close-twice", concept := "scope-lifetime-finalization", role := .preservation
      title := "A second close runs nothing"
      pointer := .witness `Effect4.Scope.close_twice },
    { id := "close-order-eq", concept := "scope-lifetime-finalization", role := .inversion
      title := "Scope finalizers run in reverse registration order (LIFO)"
      pointer := .witness `Effect4.Scope.closeOrder_eq
      literature := [
        { work := "ATTAPL", locator := "ch. 3, pp. 87–136", relation := "analogy" }
      ] },
    { id := "close-reentrant-add", concept := "scope-lifetime-finalization", role := .preservation
      title := "Re-entrant finalizer addition observes closed state immediately"
      pointer := .witness `Effect4.Scope.close_reentrant_add },
    { id := "close-seq-protocol", concept := "scope-lifetime-finalization", role := .fundamentalProperty
      title := "The close walk meets the iterator protocol for clean finalizers"
      pointer := .witness `Test.Program.ProtocolPosts.CloseIter.closeSeq_protocol
      literature := [
        { work := "deVilhenaPottier2021", locator := "audit P8", relation := "adaptedResult" }
      ] },
    { id := "saved-mask-restoration", concept := "scope-lifetime-finalization", role := .preservation
      title := "The mask's law at the boundaries of regions, on the frame machine: the getter masks and answers the image of the entry flag; a restore site at a true bit is the interruptible region over its body, and at a false bit it is its body's own code; a region's entry sets its own flag at every fiber and saves the earlier flag exactly when it changes it; the saved frame's pass returns that flag on every exit, and with a cause pending an exit that leaves the fiber interruptible fails there with it (decisions rows 227, 244 to 246; no progress, nothing about a module, and no statement for a region that changes no flag)"
      pointer := .witness `Effect4.Program.Typed.saved_mask_restoration },

    -- 4. reactive-scheduling
    { id := "machine-typed-not-halted", concept := "reactive-scheduling", role := .inversion
      title := "Halted machine configuration outside MachineTyped invariant"
      pointer := .witness `Effect4.Program.Typed.machineTyped_not_halted
      literature := [
        { work := "PFPL", locator := "ch. 28, §28.2, p. 263", relation := "adaptedResult" }
      ] },
    { id := "flush-fair", concept := "reactive-scheduling", role := .fundamentalProperty
      title := "Every initially armed owner in a duplicate-free queue is entered within its length in rounds"
      pointer := .witness `Effect4.Machine.Scheduling.flush_fair
      literature := [
        { work := "LynchVaandrager1995", locator := "audit C4", relation := "proofTechnique" }
      ] },
    { id := "step-loop-preserves", concept := "reactive-scheduling", role := .preservation
      title := "The loop decision preserves configuration typing"
      pointer := .witness `Effect4.Program.Typed.loop_preserves
      contestedBy := ["E4-TYPED-CE-012", "E4-TYPED-CE-025"]
      literature := [
        { work := "WrightFelleisen1994", locator := "audit P36", relation := "adaptedResult" }
      ] },
    { id := "step-deliver-preserves", concept := "reactive-scheduling", role := .preservation
      title := "The deliver decision preserves configuration typing"
      pointer := .witness `Effect4.Program.Typed.deliver_preserves
      contestedBy := ["E4-TYPED-CE-025"] },
    { id := "store-frame-typing", concept := "reactive-scheduling", role := .preservation
      title := "A store edit satisfying the stated frame, store typing, key and due-owner premises keeps configuration typing"
      pointer := .witness `Effect4.Program.Typed.configTyped_frame
      literature := [
        { work := "deVilhenaPottier2021", locator := "§4.2.4 (frame rule); audit P8", relation := "analogy" }
      ] },
    { id := "waiter-completion-typing", concept := "reactive-scheduling", role := .preservation
      title := "A completion fitting its cell's columns meets a waiter's declared answer and error demand"
      pointer := .witness `Effect4.Program.Typed.completionStrong_await
      literature := [
        { work := "deVilhenaPottier2021", locator := "§3.3 (protocol subsumption); audit P8", relation := "proofTechnique" }
      ] },
    { id := "step-wake-preserves", concept := "reactive-scheduling", role := .preservation
      title := "The wake command keeps configuration typing through its waiter-to-due transfer"
      pointer := .witness `Effect4.Program.Typed.wake_preserves
      contestedBy := ["E4-TYPED-CE-026"]
      literature := [
        { work := "LynchVaandrager1995", locator := "§6 (invariants); audit C4", relation := "proofTechnique" }
      ] },
    { id := "step-launch-preserves", concept := "reactive-scheduling", role := .preservation
      title := "The launch command keeps configuration typing when adding a fresh race entrant"
      pointer := .witness `Effect4.Program.Typed.launch_preserves
      contestedBy := ["E4-TYPED-CE-029"] },
    { id := "step-registration-done-preserves", concept := "reactive-scheduling", role := .preservation
      title := "Completing race registration keeps configuration typing through immediate settlement or parking"
      pointer := .witness `Effect4.Program.Typed.registrationDone_preserves
      contestedBy := ["E4-TYPED-CE-028"] },
    { id := "drivestate-lift", concept := "reactive-scheduling", role := .simulation
      title := "Command loop invariant lifting for driveState"
      pointer := .witness `Effect4.Machine.Lift.driveState_lift
      literature := [
        { work := "PFPL", locator := "ch. 28, pp. 261–268", relation := "proofTechnique" }
      ] },
    { id := "typed-state-admitted", concept := "reactive-scheduling", role := .preservation
      title := "Every admitted replay of a checked program ends in J: host answers admitted at the ghost token table keep the typed state"
      pointer := .witness `Effect4.Program.Typed.reachable_typed },
    { id := "run-work-selection", concept := "reactive-scheduling", role := .compatibility
      title := "The opt-in control planner selects exactly a queued flush or the first runnable evaluation on a non-stuck machine"
      pointer := .witness `Effect4.Run.nextControl_spec },
    { id := "scheduler-progress", concept := "reactive-scheduling", role := .progress
      title := "Operational progress with successor transitions or live frontier classification"
      pointer := .absent "Operational progress is an open obligation; machineTyped_not_halted provides an invariant consequence (stuck = none) without successor existence" },
    { id := "fair-tape-drains-armed", concept := "reactive-scheduling", role := .adequacy
      title := "A fair finite tape that suffices leaves no armed owner at its live end (R12-a: the finite endpoint consequence of FairTape's final prefix; not general fairness, not infinite tapes)"
      pointer := .witness `Effect4.Machine.Scheduling.fairTape_unarmed },
    { id := "frontier-names-work", concept := "reactive-scheduling", role := .inversion
      title := "R12-b: at a live, unfinished machine whose tape ran out, the frontier is empty exactly at a deadlock: nothing runnable, nothing armed, no host request, no timer, no compile budget (not progress, not liveness)"
      pointer := .witness `Effect4.Api.frontier_empty_iff_deadlocked },
    { id := "decision-keeps-typed", concept := "reactive-scheduling", role := .preservation
      title := "M6b: one tape decision keeps J when its host answer, if any, is admitted"
      pointer := .witness `Effect4.Program.Typed.decision_preserves },
    { id := "fair-scheduling", concept := "reactive-scheduling", role := .adequacy
      title := "Progress under weak fairness"
      pointer := .absent "Weak fairness progress is open (R12; decisions row 86)"
      literature := [
        { work := "PFPL", locator := "chs. 39–41, pp. 371–406", relation := "excludedFeature" }
      ] },
    { id := "queue-step-capacity", concept := "reactive-scheduling", role := .preservation
      title := "One step of the Queue's abstract model under suspend keeps the capacity, the strategy and the buffer's bound (a helper of queue-expansion-agrees on its abstract client's side; lengths in the natural-number model, no delivery and no target; decisions rows 219, 233 and 255)"
      pointer := .witness `Effect4.Queue.Model.positive_suspend_step_capacity },
    { id := "queue-first-profile-closed", concept := "reactive-scheduling", role := .preservation
      title := "Each first operation of the Queue's abstract model keeps the first profile, when its request keeps the step's premise (a helper of queue-expansion-agrees: the domain of the step goals; no agreement of a term with the model; decisions rows 219, 233 and 255)"
      pointer := .witness `Effect4.Queue.Model.first_profile_closed },
    { id := "semaphore-profile-closed", concept := "store-typing", role := .preservation
      title := "Each transition of Semaphore's abstract model keeps the first profile, with no premise on its request (the model's half of semaphore-accounting-preserved; nothing about a program, and no progress of a waiter; decisions rows 259 to 261 and 265)"
      pointer := .witness `Effect4.Semaphore.Model.profile_closed },
    { id := "semaphore-visit-selects-earliest", concept := "reactive-scheduling", role := .inversion
      title := "One visit of Semaphore's model selects the earliest fitting waiter at or after its cursor, and that waiter leaves (a helper of semaphore-expansion-agrees' waiting clauses; one visit, no walk and no liveness; decisions row 259)"
      pointer := .witness `Effect4.Semaphore.Model.visit_selects_earliest },
    { id := "semaphore-visit-stops", concept := "reactive-scheduling", role := .inversion
      title := "One visit of Semaphore's model selects nobody exactly when no permit is free or no waiter at or after the cursor fits, and then it changes nothing (a helper of semaphore-expansion-agrees' waiting clauses; one visit, no walk and no liveness; decisions row 259)"
      pointer := .witness `Effect4.Semaphore.Model.visit_stops_iff },

    -- 5. exact-codecs
    { id := "decode-iff", concept := "exact-codecs", role := .decidability
      title := "Exactness of JSON decoding modulo normJ"
      pointer := .witness `Effect4.Schema.decode_iff
      literature := [
        { work := "RendelOstermann2010", locator := "audit P32", relation := "definitionUsed" }
      ] },
    { id := "decode-encode", concept := "exact-codecs", role := .compatibility
      title := "Retraction of JSON encoding on canonical types"
      pointer := .witness `Effect4.Schema.decode_encode
      literature := [
        { work := "FosterEtAl2007", locator := "audit P11", relation := "adaptedResult" }
      ] },
    { id := "of-schema-exact", concept := "exact-codecs", role := .compatibility
      title := "Exactness of Schema reader modulo normS"
      pointer := .witness `Effect4.Schema.Bridge.ofSchema_exact
      literature := [
        { work := "RendelOstermann2010", locator := "audit P32", relation := "adaptedResult" }
      ] },
    { id := "of-schema-schema", concept := "exact-codecs", role := .compatibility
      title := "Retraction of Schema generation on reserved-free types"
      pointer := .witness `Effect4.Schema.Bridge.ofSchema_schema },
    { id := "collection-term-print-read", concept := "exact-codecs", role := .compatibility
      title := "Every scoped term reconstructs after structural printing, including records, payload class constructions under classes that cover them (decisions row 120), and every static tuple index"
      pointer := .witness `Effect4.Program.readTerm_printTerm },
    { id := "record-codec-layout", concept := "exact-codecs", role := .compatibility
      title := "Record JSON decoding is exact under normJ; named record values retain optional presence"
      pointer := .witness `Effect4.Schema.decode_iff },
    { id := "service-identifier-injective", concept := "exact-codecs", role := .compatibility
      title := "At one signature's scope key, distinct service keys print distinct target Identifier types"
      pointer := .witness `Effect4.Program.keyIdentifier_injective },
    { id := "error-payload-exact", concept := "exact-codecs", role := .compatibility
      title := "A typed failure's record payload reads back exactly through the error image: errOf inverts valOfErr at every represented error, the handle-free record frame included (decisions row 120)"
      pointer := .witness `Effect4.Program.errOf_valOfErr },
    { id := "payload-class-decl-exact", concept := "exact-codecs", role := .compatibility
      title := "An admitted module's payload class declarations are exactly the ones the printer writes for the program it reads to (decisions row 120, part E2)"
      pointer := .witness `Effect4.Codegen.admitModule_classDecls },
    { id := "mask-rows-table-premises", concept := "exact-codecs", role := .compatibility
      title := "The mask's two printed rows, the getter as the mask that answers its own restore and a restore site as pipe(E, saved), have two reserved heads and keep the row table's nine decided premises at the extended table; a restore site is readable exactly when its saved term is a readable leaf and its body is readable; read_print and read_exact keep their statements (decisions row 245; program syntax only)"
      pointer := .witness `Effect4.Program.mask_rows_table_premises },

    -- 6. subtyping-algebra
    { id := "subn-refl", concept := "subtyping-algebra", role := .compatibility
      title := "Reflexivity of normalized subtyping"
      pointer := .witness `Effect4.Program.Ty.subN_refl
      literature := [
        { work := "TAPL", locator := "§15.2, p. 182", relation := "definitionUsed" }
      ] },
    { id := "subn-trans", concept := "subtyping-algebra", role := .transitivity
      title := "Transitivity of normalized subtyping"
      pointer := .witness `Effect4.Program.Ty.subN_trans
      literature := [
        { work := "TAPL", locator := "§15.2, p. 182", relation := "proofTechnique" }
      ] },
    { id := "subn-equiv-iff", concept := "subtyping-algebra", role := .decidability
      title := "Kernel of subN is syntactic normal form equality"
      pointer := .witness `Effect4.Program.Ty.subN_equiv_iff
      literature := [
        { work := "TAPL", locator := "§16.3, p. 218", relation := "adaptedResult" }
      ] },
    { id := "normalize-idem", concept := "subtyping-algebra", role := .compatibility
      title := "Normalization idempotence"
      pointer := .witness `Effect4.Program.Ty.normalize_idem },
    { id := "sub-antisymm-canonical", concept := "subtyping-algebra", role := .antisymmetry
      title := "Antisymmetry of subtyping on canonical representatives CTy"
      pointer := .witness `Effect4.Program.Ty.sub_antisymm_canonical
      literature := [
        { work := "Castagna2024", locator := "audit P6", relation := "adaptedResult" }
      ] },
    { id := "template-match-anchored", concept := "subtyping-algebra", role := .decidability
      title := "The row match is complete on anchored templates: a normal request with no never outside an invariant handle's argument, below some instance, has a match (the state plan's T3a)"
      pointer := .witness `Effect4.Program.Ty.matchTemplate_complete_anchored },

    -- 7. initial-algebras-folds
    { id := "hom-eq-cata-eff", concept := "initial-algebras-folds", role := .fundamentalProperty
      title := "Pointwise equality of algebra homomorphisms with cata_eff"
      pointer := .witness `Effect4.Program.hom_eq_cata_eff
      literature := [
        { work := "MeijerFokkingaPaterson1991", locator := "audit P24", relation := "definitionUsed" },
        { work := "Gibbons2002", locator := "audit P12", relation := "proofTechnique" }
      ] },
    { id := "inhabited-iff-fits", concept := "initial-algebras-folds", role := .decidability
      title := "Syntactic inhabited fold agrees with semantic value existence in Fits"
      pointer := .witness `Effect4.Program.Typed.inhabited_iff_fits
      literature := [
        { work := "TAPL", locator := "§16.1, p. 210", relation := "adaptedResult" }
      ] },
    { id := "cata-eff-congr-on", concept := "initial-algebras-folds", role := .compatibility
      title := "Fold congruence along agreeing signature algebras"
      pointer := .witness `Effect4.Program.cata_eff_congr_on },
    { id := "addressed-replacement", concept := "initial-algebras-folds", role := .compatibility
      title := "Successful same-sort path replacement reads back, retains the root sort, and restores the original tree"
      pointer := .witness `Effect4.Program.Node.replaceAt_spec },
    { id := "operation-data-scoped", concept := "initial-algebras-folds", role := .decidability
      title := "The scope fold decides a perform node: scoped exactly when its operation's own data (the alphabet's ScopedOp) and its request are"
      pointer := .witness `Effect4.Program.Eff.perform_scoped_iff },

    -- 8. context-requirements
    { id := "satisfies-empty", concept := "context-requirements", role := .compatibility
      title := "The empty requirement is satisfied by every context"
      pointer := .witness `Effect4.Machine.Env.Context.satisfies_empty
      literature := [
        { work := "PetricekOrchardMycroft2014", locator := "audit C8", relation := "analogy" }
      ] },
    { id := "satisfies-single", concept := "context-requirements", role := .inversion
      title := "A singleton requirement is satisfied iff the key is present in the context"
      pointer := .witness `Effect4.Machine.Env.Context.satisfies_single },
    { id := "satisfies-union", concept := "context-requirements", role := .compatibility
      title := "Union requirement satisfaction splits across components"
      pointer := .witness `Effect4.Machine.Env.Context.satisfies_union },
    { id := "satisfies-weaken", concept := "context-requirements", role := .weakening
      title := "Context satisfaction is monotone under requirement row inclusion"
      pointer := .witness `Effect4.Machine.Env.Context.satisfies_weaken },
    { id := "emission-requirements-complete", concept := "context-requirements", role := .compatibility
      title := "A checked emission's main declaration carries its answer, error and complete requirement row"
      pointer := .witness `Effect4.Codegen.ModuleEmission.annotation_complete },
    { id := "provide-discharges", concept := "context-requirements", role := .preservation
      title := "Providing a layer discharges its output services from requirement rows"
      pointer := .witness `Effect4.Program.Provision.LayerTy.provide_discharges
      literature := [
        { work := "Leijen2014", locator := "audit P22", relation := "adaptedResult" }
      ] },
    { id := "provide-closed", concept := "context-requirements", role := .fundamentalProperty
      title := "A closed dependency layer that covers all requirements yields a closed program"
      pointer := .witness `Effect4.Program.Provision.LayerTy.provide_closed },
    { id := "build-total", concept := "context-requirements", role := .progress
      title := "Build totality: under a typed leaf semantics, a layer the checker types builds under every context satisfying its requirement row, and the built context satisfies its output row (restored, decisions row 147)"
      pointer := .witness `Effect4.Program.Provision.build_total },

    -- 9. host-session-protocol
    { id := "allows-answer", concept := "host-session-protocol", role := .preservation
      title := "Answering an async request is an allowed transition from awaitingAsync"
      pointer := .witness `Effect4.Run.allows_answer
      literature := [
        { work := "Wadler2012", locator := "audit P35", relation := "adaptedResult" }
      ] },
    { id := "reply-commute", concept := "host-session-protocol", role := .compatibility
      title := "Independent host replies commute in session submission"
      pointer := .witness `Effect4.Api.HostSession.reply_commute
      literature := [
        { work := "LynchVaandrager1995", locator := "audit C4", relation := "analogy" }
      ] },
    { id := "session-success-prepared-membership", concept := "host-session-protocol", role := .preservation
      title := "A session-accepted successful reply prepares a member of its selected shape-decided row"
      pointer := .witness `Effect4.Api.HostSession.preflight_success_prepared_fits },
    { id := "session-failure-shape-free", concept := "host-session-protocol", role := .preservation
      title := "A session-accepted failing reply carries no reserved defect: the failure half of admit_sound (decisions row 191, E4-HOST-CE-008)"
      pointer := .witness `Effect4.Api.HostSession.preflight_failure_noShapeDefect
      contestedBy := ["E4-HOST-CE-008"] },
    { id := "frontier-awaithost", concept := "host-session-protocol", role := .inversion
      title := "Machine awaitingAsync state matches frontier awaitHost reasons"
      pointer := .witness `Effect4.Api.observe_awaitingAsync_iff },
    { id := "host-progress", concept := "host-session-protocol", role := .progress
      title := "Host session progress under external answers"
      pointer := .assumed "docs/core/host-boundary.md" "Host session progress is subject to external driver execution; outside closed runtime" },

    -- 10. translation-simulation
    { id := "run-eq-meaning", concept := "translation-simulation", role := .simulation
      title := "Frame machine execution matches denotational meaning on Straight fragment"
      pointer := .witness `Effect4.Program.Agreement.run_eq_meaning
      literature := [
        { work := "Leroy2009", locator := "audit C10", relation := "analogy" }
      ] },
    { id := "loop-agreement", concept := "translation-simulation", role := .simulation
      title := "Loop agreement on the loop-bearing fragment (Looped)"
      pointer := .witness `Effect4.Program.Agreement.loopAgreement },
    { id := "run-eq-ref", concept := "translation-simulation", role := .simulation
      title := "Frame machine replay matches term reference replay at empty host table"
      pointer := .witness `Effect4.Program.Sched.run_eq_ref
      literature := [
        { work := "LynchVaandrager1995", locator := "audit C4", relation := "proofTechnique" }
      ] },
    { id := "m7-route", concept := "translation-simulation", role := .fundamentalProperty
      title := "M7 conditional route: typed exits and stores from ledger hypotheses M5 and M6"
      pointer := .witness `Effect4.Program.Typed.m7_of_ledger
      literature := [
        { work := "WrightFelleisen1994", locator := "audit P36", relation := "analogy" }
      ] },
    { id := "m7-exits-typed", concept := "translation-simulation", role := .adequacy
      title := "M7a: every exit the observation records fits its fiber's declared type on M7Fragment"
      pointer := .witness `Effect4.Program.Typed.m7_proved
      literature := [
        { work := "WrightFelleisen1994", locator := "audit P36", relation := "analogy" }
      ] },
    { id := "m7-stores-typed", concept := "translation-simulation", role := .adequacy
      title := "M7b: the observed stores fit at a world that describes them on M7Fragment"
      pointer := .witness `Effect4.Program.Typed.m7_proved },
    { id := "m7-never-halts", concept := "translation-simulation", role := .progress
      title := "M7c: the frame machine never halts on M7Fragment (row 139's stuck = none in J)"
      pointer := .witness `Effect4.Program.Typed.m7_proved },
    { id := "m7-admitted", concept := "translation-simulation", role := .fundamentalProperty
      title := "M7a–c for a program the API admits at the empty row table, with a closed requirement row and an answer-free tape"
      pointer := .witness `Effect4.Program.Typed.m7_admitted },
    { id := "admitted-source-lawful", concept := "residual-program-typing", role := .compatibility
      title := "An admitted program's signature, its row table and its service declarations, is lawful: program admission runs admitSig (the bridge from admission to the typed state)"
      pointer := .witness `Effect4.Program.Typed.lawfulSig_of_admitted
      contestedBy := ["E4-TYPED-CE-041"] },
    { id := "m7-exit-handles-valid", concept := "translation-simulation", role := .preservation
      title := "Recorded exits name only live scope handles on every reachable machine (row 139)"
      pointer := .witness `Effect4.Program.Typed.exitHandles_valid },
    { id := "obs-typed-admitted", concept := "translation-simulation", role := .adequacy
      title := "The frame machine's observation on every ghost-admitted tape of a checked program is typed and the run has not halted"
      pointer := .witness `Effect4.Program.Typed.obs_typed },
    { id := "m7-results-exit-hasty", concept := "translation-simulation", role := .adequacy
      title := "Every recorded exit of a checked program's frame-machine run satisfies the meaning layer's exit judgment at its declared type (T1)"
      pointer := .witness `Effect4.Program.Typed.exits_hasTy },
    { id := "replay-externals", concept := "translation-simulation", role := .preservation
      title := "No replay at the empty row table allocates an external handle"
      pointer := .witness `Effect4.Program.Sched.replay_externals },
    { id := "run-controls-replay", concept := "translation-simulation", role := .simulation
      title := "Journaled control rows leave the raw replay's machine whenever every added phase progressed"
      pointer := .witness `Effect4.Run.play_controls_eq_replay },
    { id := "run-tape-replay", concept := "translation-simulation", role := .simulation
      title := "A journal's machine is the raw replay of its tape: the controls that progressed and the reply applications, each as the decision the session hands the machine (machine equality for any run and any journal whose tape reads to its end; no session ledger, no journal that stops at a frontier, no lowered engine; decisions row 254)"
      pointer := .witness `Test.Dogfood.Scenario.tape_replays },
    { id := "queue-steps-agree", concept := "translation-simulation", role := .simulation
      title := "Each of the Queue's six step terms agrees with the abstract model's step on the first profile: the reply, the stored value through the encoding table, and the ordered signals (a part of queue-expansion-agrees; no delivery, no cancellation law, no liveness, no wrapper and no host; decisions row 255)"
      pointer := .witness `Effect4.Queue.Model.queue_steps_agree },
    { id := "semaphore-steps-agree", concept := "translation-simulation", role := .simulation
      title := "Each of Semaphore's five step terms agrees with the abstract model's step on every model state: the reply, the stored value through the encoding table, and the selected waiter's record (a part of semaphore-expansion-agrees; no order of the wake across visits, no cancellation law, no liveness, no wrapper and no host; decisions rows 259 to 261 and 265)"
      pointer := .witness `Effect4.Semaphore.Model.semaphore_steps_agree },
    { id := "straight-composition-agreement", concept := "translation-simulation", role := .simulation
      title := "StraightEq programs run to equal exits and stores at their own sufficient budgets (the straight-fragment composition relation)"
      pointer := .witness `Effect4.Program.Denote.StraightEq.run_agrees },
    { id := "mask-printed-form-profile", concept := "translation-simulation", role := .compatibility
      title := "The mask as a derived form, the getter bound to its body under uninterruptible: the surface's builder is that expansion; it types as its body under the saved state's binder, and a restore site of any other saved term has no type; it is readable exactly when its body is, so it prints and reads back; inside the getter the fiber is masked and a pending cause fails it at the getter's restoring frame, and after that frame an interruptible caller is interruptible until the body's mask (decisions rows 245, 246; no equality with the native spelling and no agreement with a release)"
      pointer := .witness `Effect4.Program.mask_printed_form_profile }
  ]
  cuts := [
    -- 1. store-typing
    { concept := "store-typing", decisionRow := 163
      excluded := "function values and closures in Val: Fits contains no arrow clause"
      reason := "the language cut, docs/research/history/language-cut.md section 1" },
    { concept := "store-typing", decisionRow := 96
      excluded := "raw subtyping in handle arms: comparisons use Equiv under Ty.subN"
      reason := "checker compares and joins in normalized order (decisions row 137, E4-TYPED-CE-009)" },
    { concept := "store-typing", decisionRow := 156
      excluded := "dangling scope handles: ScopeLive presence required at Ty.scope"
      reason := "machine halts on absent scope in prepareScopedExitR (E4-SCHED-CE-020)" },

    -- 2. residual-program-typing
    { concept := "residual-program-typing", decisionRow := 163
      excluded := "stored function values and closures: stored Eff syntax uses first-order program trees, while proof-side RProgram carries Lean function continuations at visible operations"
      reason := "the language cut, docs/research/history/language-cut.md section 1; row 163 excludes stored function values, not functions in the semantic model" },
    { concept := "residual-program-typing", decisionRow := 117
      excluded := "open root requirement rows: M5, M6c and M7 take the premise rootTy.requires = empty"
      reason := "rc.112 runs closed root rows (Effect.ts:17494-17497), while retaining separate per-position obligations" },
    { concept := "residual-program-typing", decisionRow := 148
      excluded := "general bind closure: sequencing is proved per construct via compatibility lemmas"
      reason := "closing marker unguard fixes exit type (E4-TYPED-CE-030)" },

    -- 3. scope-lifetime-finalization
    { concept := "scope-lifetime-finalization", decisionRow := 156
      excluded := "closure or exit of absent scopes: ScopeLive required"
      reason := "machine halts on absent scope in prepareScopedExitR" },
    { concept := "scope-lifetime-finalization", decisionRow := 152
      excluded := "badName and notImplemented defect transmission during close walk"
      reason := "ShapeFree exclusion on encoded causes in exit types (row 152)" },

    -- 4. reactive-scheduling
    { concept := "reactive-scheduling", decisionRow := 106
      excluded := "unbounded token indices: QueueOk enforces GuardState.keysBelow"
      reason := "fresh token bounds protect scheduler invariants (decisions row 106)" },
    { concept := "reactive-scheduling", decisionRow := 107
      excluded := "defect-bearing exit boundaries: ExitOk requires NoShapeDefect"
      reason := "badName and notImplemented defects excluded from typed exits" },
    { concept := "reactive-scheduling", decisionRow := 134
      excluded := "untyped timer and race columns in configuration typing"
      reason := "E4-TYPED-CE-024 through CE-029 separate timer, waiter, and race keys" },

    -- 5. exact-codecs
    { concept := "exact-codecs", decisionRow := 128
      excluded := "arbitrary syntactic equality: embeddings are exact modulo normJ and normS"
      reason := "JSON object key order and Schema AST annotations do not affect decoding" },
    { concept := "exact-codecs", decisionRow := 179
      excluded := "unconditional metadata preservation: normS erases only nine approved keys"
      reason := "arbitrary effect4/* annotations cannot be silently discarded" },

    -- 6. subtyping-algebra
    { concept := "subtyping-algebra", decisionRow := 137
      excluded := "raw subtyping for checker comparisons: subN normalizes both sides first"
      reason := "raw sub does not distribute products over unions (E4-TYPED-CE-009)" },
    { concept := "subtyping-algebra", decisionRow := 163
      excluded := "arrow subtyping: Ty contains no function constructor"
      reason := "the language cut, docs/research/history/language-cut.md section 1" },

    -- 7. initial-algebras-folds
    { concept := "initial-algebras-folds", decisionRow := 127
      excluded := "recursive-type unfolding in inhabited: inhabited is a fold over finite syntax"
      reason := "Ty is an inductive data type with no infinite equi-recursive unfolding" },

    -- 8. context-requirements
    { concept := "context-requirements", decisionRow := 117
      excluded := "open root requirement rows: M5, M6c and M7 require rootTy.requires = empty"
      reason := "rc.112 runs closed rows (Effect.ts:17494-17497)" },
    { concept := "context-requirements", decisionRow := 104
      excluded := "lexical environment capture in layers: layers build at closed points"
      reason := "Point.layerBuild prevents layer bodies from reading outer environments (E4-PROV-CE-005)" },
    { concept := "context-requirements", decisionRow := 105
      excluded := "mismatched layer values: layer value must fit declared service type"
      reason := "LayerHasTy requires declared service carrier and value subtyping (E4-PROV-CE-006)" },

    -- 9. host-session-protocol
    { concept := "host-session-protocol", decisionRow := 122
      excluded := "in-engine boundary decoding: Decision 12 adopts Route A typed membership"
      reason := "boundary decode checks membership before runtime admission (host-boundary.md section 7)" },
    { concept := "host-session-protocol", decisionRow := 97
      excluded := "internal handle kinds at host boundary: cells, promises, fibers, scopes refused"
      reason := "prevents leaking internal runtime capabilities across boundary (E4-HOST-CE-007)" },

    -- 10. translation-simulation
    { concept := "translation-simulation", decisionRow := 138
      excluded := "non-empty host tables in M7: M7 is stated strictly on M7Fragment with root.table = []"
      reason := "table-aware agreement is deferred to R6 (DI-57)" },
    { concept := "translation-simulation", decisionRow := 95
      excluded := "host answers on decision tapes: M6 and M7 quantify over answer-free tapes"
      reason := "reference machine has no host table and refuses every answer (emptyTable_refuses_every_answer)" },
    { concept := "translation-simulation", decisionRow := 117
      excluded := "open requirement rows: M7Fragment enforces rootTy.requires = empty"
      reason := "rc.112 runs closed rows (Effect.ts:17494-17497)" }
  ]
  requirements := [
    { id := "R1", title := "The signature is a parameter: one located refusal admits Σ_app, and every milestone statement takes it"
      top := [`Conform.Effect4.Typing.check_sound, `Conform.Effect4.Typing.check_complete,
        `Effect4.Program.admitSig_ok_iff, `Effect4.Program.Denote.meaning_typed_app,
        `Effect4.Program.Denote.run_typed_app, `Effect4.Program.Denote.meaningB_typed_app,
        `Effect4.Program.Typed.reachable_typed_admitted]
      openParts := ["program admission at declared services is reached by tests only: authoring, Built, the session and Run.open admit at the table's own signature ⟨table, []⟩, and code generation's admission check is at nativeSignature table (decisions row 21; the slice plan's steps 3 and 4, docs/research/2026-10-04-claude-lead/sigapp-slice-plan.md)",
        "the faces (22 lines) pinned to the built-in signature: Laws/Codegen/Admit, Laws/Codegen/Checked and Laws/Api/ModuleReadable take nativeSignature table (the Σ_app slice; C7, conditional on decisions row 115)",
        "meaning, loop and run soundness at service declarations that rebind a code: restored 2026-10-04 at fresh codes only (SoundAnySignature.lean)",
        "structured service carriers: LawfulSig admits flat carriers only (decisions row 118, open: waits on a program that needs one)"] },
    { id := "R2", title := "Extension is conservative: C1–C8 over DI-47's relation on Σ_app"
      top := [`Effect4.Program.check_ext, `Effect4.Program.check_restrict, `Effect4.Program.lawful_append]
      openParts := ["C2 for host rows: operational until DI-69's row meaning lands",
        "C4 for TypedProg (the generic judgment is proved both ways)",
        "C5: the world projection with its back condition (its red controls are proved)",
        "C7: conditional on decisions row 115", "C8: per form"] },
    { id := "R3", title := "Data: the type language closed under records and variants as Ty growth"
      top := [`Effect4.Program.Formation.checkInput_eq_none_iff, `Effect4.Program.Typed.fits_normalize,
        `Effect4.Program.Typed.fits_subN, `Effect4.Program.Typed.inhabited_iff_fits,
        `Effect4.Program.hom_eq_cata_ty, `Effect4.Schema.decode_iff,
        `Effect4.Schema.Bridge.ofSchema_exact, `Effect4.Program.readTerm_printTerm,
        `Effect4.Codegen.Metadata.type_metadata_exact, `Effect4.Program.errOf_valOfErr]
      openParts := ["variants: the tag select over records landed (decisions row 195 (d)); catchTag's residual, the caught tag subtracted from the error column, waits on decisions row 130",
        "recursive types are row 124 (open): nominal Σ_app declarations through Ty.app",
        "error payloads: the carrier (decisions row 120, part E1) and the face (part E2: one Data.TaggedError class per tag, printed and read back) landed; open: catchTag's residual over records (decisions row 130), int and number fields (row 121; a number field is refused by name as unreadable), a field typed by another class (refused by name), a record update of a class instance (it answers a structural object), and a host row answering a payload (R6, parked)",
        "int inhabited inside row 108's profile: ruled 2026-10-02 (decisions row 121), not landed; the admission's int scan still refuses it",
        "the Schema and JSON images of app, null, undefined, number and bytes: unlowered or refused by name (decisions rows 121, 158, 160, 161)",
        "equality at records: eq stays refused at records until a program compares them (decisions row 126)"] },
    { id := "R4", title := "State: the world types every cell at any type, with rows as templates"
      top := [`Effect4.Program.Typed.order_refl, `Effect4.Program.Typed.order_trans,
        `Effect4.Program.Typed.refMake_extension, `Effect4.Program.Typed.deferredMake_extension,
        `Effect4.Program.Typed.memoBuild_extension,
        `Effect4.Program.Typed.fold_typed_atomic_update,
        `Effect4.Program.Typed.handle_identity_laws,
        `Effect4.Program.Typed.saved_mask_image_membership,
        `Effect4.Program.Typed.scoped_body_substitution_boundary]
      openParts := ["the faces of Ref<A> and Deferred<A, E>, the type arguments' part: landed in the state plan's T5 for a binder term and for Deferred.make: a read-modify-write row's binder term is printed as a function of the cell's current value and read back (part A: printPerform, readPerform); Deferred.make<A, E>() is printed from the operation's own type arguments and read back at every instance whose types are readable (part B: Signature.typeArgsOf and withTypeArgs, printCall, readCall, LawfulTypeArgs; Classes.readTyChecked on Classes.ReadableTy), a bare Deferred.make() is refused by its spelling and never typed at a default, the native row declares no type argument of its own, and an operation's type arguments are program annotations (ScopedOp.typeArgs: raw formation, the integer scan and the module's class table read them; decisions row 212); read_print and read_exact keep their statements; open: Ref.make<A>, which needs an appended constructor (decisions rows 210 and 212); a type argument outside the readable types (a handle type, unknown, a class name: printed where it has a printed form, and refused at reading; int and number: read at nat); a list fold's stated accumulator type, which is printed and not read; and the instance's row in the other estates: the TypeScript profile and the OCaml metadata list Deferred.make once, at the face's instance, so a consumer that needs an instance's answer column derives it from the operation",
        "the target half of handle-identity-laws (decisions row 229): the identity correspondence in each target's relation, in both directions: two handles have equal keys exactly when their host objects are one object; no goal states it, and the laws over Fits and the world's order are handle_identity_laws",
        "semaphore-accounting-preserved (proposed claim; store-typing): along a run of the public operations the cell stays a member of its type and its state stays in the first profile; the model's half is profile_closed, and the cell's half is the six typing statements with step_keeps_cell; no goal states the run-level claim (decisions rows 260, 261, 265)",
        "atomic-attempt-isolation (proposed claim; store-typing and reactive-scheduling): an admitted atomic body's ordered dynamic reads and writes, the exact state that a failure or a retry restores, and no step of another fiber between its first access and its commit (decisions rows 80, 223; waits on the body profile's grammar and on row 226's budget or suspension)",
        "the second half of scoped-body-substitution-boundary (residual-program-typing): for a later constructor that does bind a scope, the code after the scope runs only after it, and substitution neither captures it nor copies it into a child body (decisions rows 225, 227); no goal states it: the mask adds no scoped constructor, and its restore node's half is scoped_body_substitution_boundary"] },
    { id := "R5", title := "Services: the service table, layers and provision"
      top := [`Effect4.Program.Provision.build_total]
      openParts := ["lower_refines_build: the machine's build of a layer refines `build` (decisions row 147)",
        "reference keys, Config, minted keys, and context validation at any runtime bridge (system map §8, R5)"] },
    { id := "R6", title := "The host: a lawful HostSpec, receipt and application, DI-57's table-aware reference"
      top := [`Effect4.Program.Typed.reachable_typed,
        `Effect4.Api.HostSession.preflight_success_prepared_fits,
        `Effect4.Api.HostSession.preflight_failure_noShapeDefect]
      openParts := ["admit_sound's value half: executable admission implies the ghost AnswerOk on success values (waits on decisions row 97's handle declarations)",
        "DI-57's table-aware reference relation: run_eq_ref holds at the empty table only (parked by the owner, 2026-09-30)",
        "DI-69: the row table's meaning in code",
        "H related to the machine: M6's premise is a predicate on tapes (decisions row 95), not a host relation",
        "receipt and application on the keyed lifecycle, and their converse (host-boundary §4.5; decisions rows 98–100, parked by the owner, 2026-09-30)",
        "a world extension meeting C5, a retirement edge, per-row cancellation, one root (DI-58, DI-65)",
        "the public typed guarantee for programs using host services (decisions row 99)"] },
    { id := "R7", title := "Retained behaviour: a resolved code entry is typed at its reference's type"
      top := []
      openParts := ["resolve_typed: a resolved code entry is typed at its reference's type, with capture layout fixed at resolution and identity by allocation or structure (decisions row 82, open)",
        "code-valued services with a capture law, R5's through R7 (decisions row 82)",
        "the reserved contract of a retained behaviour: its entry, captures, invocation context and lifetime, designed now for the planned Cache, Pool and callback modules; the value form and its evaluator wait for the first of them (decisions row 234)",
        "posted-body-entry-typed (proposed claim; residual-program-typing): a checked Eff body supplied at a posting site, with its resolved entry, typed lexical environment and selected service policy, stays typed under world extension (decisions rows 82, 225)"] },
    { id := "R8", title := "Runs and faces as named connections: equal to the reference inside a profile, refused outside it"
      top := [`Effect4.Program.read_print, `Effect4.Program.read_exact,
        `Effect4.Program.Agreement.run_eq_meaning, `Effect4.Program.Agreement.loopAgreement,
        `Effect4.Program.Sched.run_eq_ref, `Effect4.Program.mask_rows_table_premises]
      openParts := ["typed lowering open: what verified lowering means (decisions row 28); the OCaml engine is outside M7 until it is ruled",
        "numbers open (decisions row 108): each face equal to the reference inside its bounded profile and refusing outside it, intermediates included (DI-56)",
        "K2 holds on the readable domain; since the state plan's T5, part B, a loop's stated cursor type and an operation's type arguments read back through one checked type reader (Classes.readTyChecked, DI-91's fallback (a) in a checked form), and the domain excludes a stated type outside the readable types (Classes.ReadableTy: a collision such as int, a spelling with no reading such as a handle type) and every list fold that states its accumulator's type, which is printed and not read",
        "one identity bijection across faces: the fiber identity carrier is ruled, not landed (DI-81)",
        "the TypeScript face against rc.112: finite checks only, by the truth harness and by the keyed lane's runs of the scenarios' scripts on their printed modules (DI-49; decisions row 254)",
        "the profile as data, named by each face's law (decisions row 79, R79.5)"] },
    { id := "R9", title := "Never goes wrong: M7a–c on M7Fragment (the empty host table, answer-free tapes)"
      top := [`Effect4.Program.Typed.m7_proved, `Effect4.Program.Typed.m7_admitted]
      openParts := ["part two: a saved frame transports missingService across a change in the requirement row (decisions row 117)"] },
    { id := "R10", title := "Library code inherits theorems: a composed module's law is Agrees profile module expansion"
      top := [`Effect4.Codegen.Forms.andThenEffect_typed,
        `Effect4.Codegen.Forms.andThenContinuation_typed,
        `Effect4.Codegen.Forms.andThenThunk_typed, `Effect4.Codegen.Forms.as_typed,
        `Effect4.Codegen.Forms.asVoid_typed, `Effect4.Codegen.Forms.tapContinuation_typed,
        `Effect4.Codegen.Forms.tapEffect_typed, `Effect4.Codegen.Forms.ensuring_typed,
        `Effect4.Codegen.Forms.void_typed, `Effect4.Codegen.Forms.die_typed,
        `Effect4.Codegen.Forms.yieldKey_typed, `Effect4.Codegen.Forms.matchCause_typed,
        `Effect4.Codegen.Forms.matchCauseEffect_typed,
        `Effect4.Codegen.Forms.yieldNow_typed,
        `Effect4.Codegen.Forms.forkChildDefault_typed,
        `Effect4.Codegen.Forms.forkDetachDefault_typed,
        `Effect4.Codegen.Forms.forkInDefault_typed,
        `Effect4.Codegen.Forms.forkScopedDefault_typed,
        `Effect4.Codegen.Forms.releaseOne_typed,
        `Effect4.Program.mask_printed_form_profile]
      openParts := ["a composed module's law, Agrees profile module expansion (decisions row 79, R79.5; DI-89)",
        "no form has a behaviour law (DI-89)",
        "the agreement half of mask-printed-form-profile (translation-simulation, serving R10 and R11): the compiled derived form against the named release's printed form, equal observation on a named observation under compatible decisions; the three operations more than the native mask are measured on the machine and on the target, not proved, and the cuts at the two checkpoints on the pin rest on Codex's runs; the expansion, the typing, the readability and the two checkpoints on the machine are mask_printed_form_profile (decisions rows 245, 246); no goal states the agreement",
        "none of DI-89's named forms exists: retry, catchTag, forEach, all, Schedule over iterate, the option and result eliminators",
        "per form: reader admission, a readable expansion (C8) and a stable identity (DI-89; the model probe's D9, unruled)",
        "DI-39's six rows not landed",
        "a composite's contract by a stuttering route (post-Phase C §11.4)",
        "queue-expansion-agrees (proposed claim; translation-simulation): the Queue's expansion agrees with its application-signature clients on the Queue's profile, which defines the public requests, commits, replies, interruptions and terminations before it hides a private cell or a helper identity (decisions rows 79, 219 to 222, 230)",
        "semaphore-expansion-agrees (proposed claim; translation-simulation): Semaphore's expansion agrees with the first profile's public observation; it keeps the selected identities and the permit commits, with its premises on the wake's policy, the admitted callers, interruption and the work budget; its parts on one atomic step are semaphore-steps-agree, and the wrapper, the walk across visits and the protected form are not stated (decisions rows 79, 226, 259 to 261)",
        "posted-wake-profile-agrees (proposed claim; translation-simulation): one producer's posted delivery, with its dispatch owner, priority, receiver and token, capture time, coalescing and cancellation, agrees with its module expansion; the Queue's producer is first (decisions rows 81, 220, 225; DB-13)",
        "atomic-attempt-agreement (proposed claim; translation-simulation): the restricted transaction profile against the named release, with flat nesting, immutable payloads and explicit retry; then tx-choice-rollback-union for the retry-only alternative (decisions rows 80, 84, 223, 224)",
        "fair composition of tickets that are enrolled apart is outside the first profile: the opposing-ticket cycle stays a refused case until an enrolment protocol resolves it (decisions row 223)"] },
    { id := "R11", title := "Resources are released: at most once per registration, exactly once in close order"
      top := [`Effect4.ScopeMachine.runState_complete, `Effect4.ScopeMachine.runState_restore,
        `Effect4.ScopeMachine.runState_prefix, `Effect4.Scope.close_twice,
        `Effect4.Scope.close_reentrant_add, `Effect4.Scope.closeOrder_eq,
        `Effect4.Program.Typed.saved_mask_restoration]
      openParts := ["the whole run open: release at most once per registration, counted by identity (DB-07)",
        "the whole run open: exactly once in close order over closed scopes and structured regions, with a completed-cleanup receipt (DB-07, DI-65)",
        "state retained at a frontier, open scopes closed only by an explicit abandon (the owner's ruling of 2026-09-07)",
        "a scope a finished run leaves open is an observation, as in rc.112 (the model probe's D8, unruled per DB-07)",
        "the run-level half of saved-mask-restoration (scope-lifetime-finalization): a region that changes no flag ends with its entry flag, for an arbitrary body, as an invariant of runs; a candidate is that the flag is a function of the saved stack, since a region that changes the flag pushes the frame that returns it; the boundary statements are saved_mask_restoration, and a client premise stays, nothing acquired or registered before the body begins (decisions rows 227, 244 to 246); no goal states the invariant",
        "waiting-request-obligation-preserved (proposed claim; reactive-scheduling, serving R10 to R12): a selected request's notification stays in store debt, queued commands, dispatcher work or the receiver's accepted continuation until it is discharged; when cancellation wins and withdraws the request before consumption, the operation consumes nothing; a completed commit stays committed, even when the caller is interrupted before its continuation; an interruption that is only requested, and stays pending under a mask, withdraws nothing; an old token is inert after rearming (decisions rows 221, 222)"] },
    { id := "R12", title := "Frontiers name what they await"
      top := [`Effect4.Machine.Scheduling.fairTape_unarmed, `Effect4.Api.frontier_empty_iff_deadlocked]
      openParts := ["R12-c: liveness on infinite tapes under FairTape (waits on a ruling on infinite tapes)",
        "stability over the allowed internal decisions, with a named progress observation (not stated)",
        "divergence by compatible prefixes (DB-03; not stated)",
        "driver-continuation-split and driver-suspension-keeps-typed (proposed claims; reactive-scheduling, extending drivestate-lift): a retained driver suspension keeps the commands, the remaining dispatcher tasks, the enclosing flush or clock phase and any atomic owner, and continuing it with budgets n and k equals one run with n + k; until then an owned operation runs under a proved embedded budget (decisions rows 84, 226)",
        "wait-registration-no-gap (proposed claim; reactive-scheduling): the decision to wait and the registration are one transition, so each eligible waiter is retrying or owns a notification (decisions rows 221, 223; finite controls in docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean)",
        "posted-task-decision-preserves (proposed claim; reactive-scheduling): a posted task keeps the typed state, with its execution identity, its owner, its receiver's token and a stale delivery (decisions row 225)",
        "posted-wake-debt-progress and a module's request progress: separate claims under named fairness, body-progress and budget premises; dispatcher service (flush_fair) does not give them (decisions rows 220, 225, 230)"] },
    { id := "R13", title := "A run's inputs are data: equal recorded inputs give equal replay observations"
      top := [`Effect4.Run.journal_replays]
      openParts := ["load inputs, the environment snapshot and the seed: designed (the 2026-09-10 Config route B), not implemented (decisions rows 51, 83)",
        "supplied values fit the admitted load requirements: restates M5 (loadsTyped, the retired ledger's typedState_load) when Config lands",
        "the service half of the signature as a recorded input: Built carries the row table only (decisions row 21)",
        "clock-unit-compatibility (proposed claim; translation-simulation): exact nanoseconds inside, with every recorded millisecond input kept in meaning by an explicit conversion; public nanosecond readings wait for the target's bigint contract (decisions rows 83, 231)"] }
  ]
  planScope := [`Effect4, `Test.Dogfood.Scenario]

end Tools.Semantics
