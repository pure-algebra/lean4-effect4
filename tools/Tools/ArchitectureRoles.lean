/-!
# Tools.ArchitectureRoles — the one hand-written input of the architecture map

`tools/Tools/Architecture.lean` measures the tree and writes `docs/core/architecture-map.html`.
Everything measured comes from the tree itself: the import headers through Lean's own parser,
declaration counts from the loaded roots, sizes from disk, the generated groups from
`docs/GENERATED.md`, the pinned packages from `lakefile.toml`. What the tree cannot say is
*what a directory is for* and *which direction imports are supposed to run*. That is this
module: one area per directory with its column, its height in the column and its role; the
layering rule; the imports a document names and accepts; the milestone's modules, planned and
landed, so the map's proof stack updates itself as slices land.

The table is total in both directions, the same way `Typed/Sources.lean` is: a Lean file
under no declared area, or a declared path that does not exist, stops the driver with the
name. It is the role register's totality gate, not a test gate: the map is a report, and the
driver exits 0 on every import it finds against the direction.
-/

namespace Tools.Architecture

/-- The column of the map a path belongs to. The first four are Lean roots and carry import
edges; the rest are estates measured by file walk. -/
inductive Column
  | runtime | laws | tools | tests | ocaml | ts | host | docs | vendor
deriving BEq, Repr, Inhabited, DecidableEq

def Column.title : Column → String
  | .runtime => "The runtime root · lake library Effect4"
  | .laws => "The proof graph · lake library Effect4Laws"
  | .tools => "The tool roots · ProofGraph, Conform, Tools, OCaml5, Effect4Gen"
  | .tests => "The batteries and gates · lake library Test"
  | .ocaml => "The OCaml estate · ocaml/"
  | .ts => "The TypeScript face · ts/eff and the tsgo oracle"
  | .host => "Host gates, scripts and promoted results"
  | .docs => "The authorities and the record"
  | .vendor => "Pinned references"

def Column.isLean : Column → Bool
  | .runtime | .laws | .tools | .tests => true
  | _ => false

def Column.order : Column → Nat
  | .runtime => 0 | .laws => 1 | .tools => 2 | .tests => 3
  | .ocaml => 4 | .ts => 5 | .host => 6 | .docs => 7 | .vendor => 8

/-- One area: a directory, or one file, and what it is for. `layer` is its height in the
column: an import inside a column may only point at the same height or lower. A `detail`
area is listed in the file map but its edges roll up to the enclosing area, so the diagram
stays readable. `measure := false` lists a path without walking it (the vendored sources). -/
structure Area where
  path : String
  column : Column
  layer : Nat
  title : String
  role : String
  detail : Bool := false
  measure : Bool := true
deriving Repr, Inhabited

/-- Every directory with a Lean file, and every estate the map shows, has one row here. -/
def areas : List Area := [
  -- the runtime root, bottom up
  ⟨"src/Effect4/Data", .runtime, 0, "Data", "requirement rows, JSON, lawful optics, ASCII", false, true⟩,
  ⟨"src/Effect4/Store/Carrier", .runtime, 1, "Store/Carrier", "value trees, their byte codec, images, digests and folds below Machine", false, true⟩,
  ⟨"src/Effect4/Store/Domain", .runtime, 4, "Store/Domain", "canonical documents, nodes, persistence, and program wire projections above Schema", false, true⟩,
  ⟨"src/Effect4/Store/Domain/Derived", .runtime, 4, "Store/Domain/Derived", "generated `Canonical` instances (the derived group)", true, true⟩,
  ⟨"src/Effect4/Machine", .runtime, 2, "Machine", "`Cause` and `Exit`, the frame alphabet, the scope machine, the fiber machine (`RunMachine`, `replayEval`), the stores, the wake protocol, the logical clock", false, true⟩,
  ⟨"src/Effect4/Program", .runtime, 3, "Program", "`Eff`, `Ty`, the checker, the native rows and atoms, `compile`, provision and config", false, true⟩,
  ⟨"src/Effect4/Program/Authoring", .runtime, 3, "Program/Authoring", "the authoring surface: modules, lifts, rows, forms", true, true⟩,
  ⟨"src/Effect4/Program/Typing", .runtime, 3, "Program/Typing", "the typing rules the checker and the declarative judgement share", true, true⟩,
  ⟨"src/Effect4/Program/Packages", .runtime, 3, "Program/Packages", "the two package tables", true, true⟩,
  ⟨"src/Effect4/Schema", .runtime, 4, "Schema", "the persisted Schema data plane; `Codec` is the type-directed JSON boundary; `Image` and `Bridge` the arrows in and out", false, true⟩,
  ⟨"src/Effect4/Codegen", .runtime, 5, "Codegen", "the pinned Effect profile: print and read, the template table, forms, bindings, module admission", false, true⟩,
  ⟨"src/Effect4/Ingest", .runtime, 5, "Ingest", "the ingest taxonomy", false, true⟩,
  ⟨"src/Effect4/Api", .runtime, 6, "Api", "the application face: author and build, run, the host session and protocol, supervision, inspection", false, true⟩,
  ⟨"src/Effect4/Run.lean", .runtime, 7, "Run", "the run API over `Api`: commands, the journal, replay", false, true⟩,
  ⟨"src/Effect4.lean", .runtime, 8, "Effect4", "the root: the face and the functional utilities; never Laws", false, true⟩,
  -- the proof graph
  ⟨"src/Effect4/Laws/Effects", .laws, 0, "Laws/Effects", "layer 0 of the typed-state invariant: the protocol-typed predicate on the free monad; imports the pinned `Effects` only", false, true⟩,
  ⟨"src/Effect4/Laws/Auto", .laws, 1, "Laws/Auto", "the instruments: the censuses, the position gate, `#typed_state`, `#frame_rules`, the obligation ledger, the aesop banks", false, true⟩,
  ⟨"src/Effect4/Laws/Store", .laws, 1, "Laws/Store", "the store's laws", false, true⟩,
  ⟨"src/Effect4/Laws/Store/Folds", .laws, 1, "Laws/Store/Folds", "fold connectors for store values", true, true⟩,
  ⟨"src/Effect4/Laws/Machine", .laws, 2, "Laws/Machine", "store and frame invariants, the store kernel, `Book` and `BMeans`, observations, approximation and scheduling laws", false, true⟩,
  ⟨"src/Effect4/Laws/Machine/Folds", .laws, 2, "Laws/Machine/Folds", "fold connectors for machine stores", true, true⟩,
  ⟨"src/Effect4/Laws/Program", .laws, 3, "Laws/Program", "typing soundness, meaning, the reference scheduler and evaluator, replay agreement, simulation, guards, authoring, the typed state", false, true⟩,
  ⟨"src/Effect4/Laws/Program/Typing", .laws, 3, "Laws/Program/Typing", "the checker sound and complete against `HasTy`; inversion", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Guard", .laws, 3, "Laws/Program/Guard", "the guard family's laws", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Intro", .laws, 3, "Laws/Program/Intro", "the introduction laws by path", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Handles", .laws, 3, "Laws/Program/Handles", "handle validity across the alphabet", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Simulation", .laws, 3, "Laws/Program/Simulation", "the compiled machine paired with the reference, step by step", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Agreement", .laws, 3, "Laws/Program/Agreement", "`run_eq_meaning` and its kin", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Authoring", .laws, 3, "Laws/Program/Authoring", "the authoring surface's laws", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Typed", .laws, 3, "Laws/Program/Typed", "the typed-state invariant: the vocabulary, the source table, the skeleton, the frames", true, true⟩,
  ⟨"src/Effect4/Laws/Program/Folds", .laws, 3, "Laws/Program/Folds", "fold connectors for the denotations", true, true⟩,
  ⟨"src/Effect4/Laws/Schema", .laws, 4, "Laws/Schema", "the Schema boundary's laws", false, true⟩,
  ⟨"src/Effect4/Laws/Codegen", .laws, 4, "Laws/Codegen", "printer and reader laws over the template table; module admission and checked production", false, true⟩,
  ⟨"src/Effect4/Laws/Api", .laws, 5, "Laws/Api", "the runner, host session, supervision, frontier and fuel laws", false, true⟩,
  ⟨"src/Effect4/Laws/Run.lean", .laws, 5, "Laws/Run", "the run API's laws: `journal_replays`, `replay_unique`, `drive_eq_play`", false, true⟩,
  ⟨"src/Effect4/Laws.lean", .laws, 6, "Effect4.Laws", "the root of the proof graph", false, true⟩,
  -- the tool roots
  ⟨"tools/ProofGraph", .tools, 0, "ProofGraph", "checked theorem references, rolled-back search, published theorems, the obligation join; below Laws and Conform", false, true⟩,
  ⟨"tools/Conform", .tools, 1, "Conform", "generic conformance: source descriptions, reports and evidence, obligations, the LCNF walkers and semantics, layouts, models, the `Std.Do` pilot", false, true⟩,
  ⟨"tools/Conform/Core", .tools, 1, "Conform/Core", "reports, evidence, obligations, policy, the proof shim", true, true⟩,
  ⟨"tools/Conform/Lcnf", .tools, 1, "Conform/Lcnf", "the mono-LCNF walkers, rules, validity and semantics", true, true⟩,
  ⟨"tools/Conform/Layout", .tools, 1, "Conform/Layout", "layout coherence: build, check, reflect, native", true, true⟩,
  ⟨"tools/Conform/Model", .tools, 1, "Conform/Model", "model builders", true, true⟩,
  ⟨"tools/Conform/Spec", .tools, 1, "Conform/Spec", "the specification reflection pilot", true, true⟩,
  ⟨"tools/Conform/Source", .tools, 1, "Conform/Source", "the generic source description", true, true⟩,
  ⟨"tools/Conform/Manifest", .tools, 1, "Conform/Manifest", "manifest readers and the mirror", true, true⟩,
  ⟨"tools/Conform/Cli", .tools, 5, "Conform/Cli", "the `--run` drivers over the generic core and the Effect4 adapters", false, true⟩,
  ⟨"tools/Tools", .tools, 2, "Tools", "shared descriptions, stamps, inventory and neutral tool utilities", false, true⟩,
  ⟨"tools/Drivers", .tools, 4, "Drivers", "Effect4 drivers that consume the OCaml5 projection", false, true⟩,
  ⟨"tools/TestSupport", .tools, 2, "TestSupport", "shared immutable fixtures consumed by tooling and batteries; no runtime imports", false, true⟩,
  ⟨"src/OCaml5", .tools, 3, "OCaml5", "the Lean half of the OCaml estate: the `Eff` closed world and emitters, the LCNF → OCaml backend, the OCaml language model, the drivers", false, true⟩,
  ⟨"src/OCaml5/Eff", .tools, 3, "OCaml5/Eff", "the closed world, the emitters, the goldens", true, true⟩,
  ⟨"src/OCaml5/Lcnf", .tools, 3, "OCaml5/Lcnf", "the LCNF → OCaml translator, its types, externs and naming", true, true⟩,
  ⟨"src/OCaml5/Ml", .tools, 3, "OCaml5/Ml", "the OCaml syntax the backend prints through, its renderer, profile and checker", true, true⟩,
  ⟨"src/OCaml5/Tools", .tools, 3, "OCaml5/Tools", "the `--run` cuts: the engine, the `Eff` library, the wire goldens, the store goldens", true, true⟩,
  ⟨"tools/Conform/Effect4", .tools, 4, "Conform/Effect4", "the Effect4 adapters: profiles, fixtures, the LCNF and layout worlds, the native target", false, true⟩,
  ⟨"tools/Effect4Gen", .tools, 5, "Effect4Gen", "the deriving generator (`Canonical`, folds, views, rows, atoms, forms) and its projection guard; `guards/` holds the fragments appended to generated files, not modules", false, true⟩,
  ⟨"tools/conform-red", .tools, 6, "conform-red", "negative probes for Conform, deliberately red, in no root", false, true⟩,
  -- the batteries
  ⟨"Test", .tests, 0, "Test", "`Test/All.lean` is the green battery and the gate's root; the areas mirror the runtime's", false, true⟩,
  ⟨"Test/Audit", .tests, 0, "Test/Audit", "the axiom gate, the runtime coverage join, the censuses, the proof-graph and ledger controls", true, true⟩,
  ⟨"Test/Counterexamples", .tests, 0, "Test/Counterexamples", "the durable attacks, by stable ID", true, true⟩,
  ⟨"Test/contracts", .tests, 0, "Test/contracts", "the packets: what each area promises, as prose", true, true⟩,
  ⟨"Test/fixtures", .tests, 0, "Test/fixtures", "the sample trees and the trust-boundary fixture; its `.lean` files are fixtures, not modules", true, true⟩,
  ⟨"Test/Api", .tests, 0, "Test/Api", "the face's batteries", true, true⟩,
  ⟨"Test/Codegen", .tests, 0, "Test/Codegen", "printer, reader and module batteries", true, true⟩,
  ⟨"Test/Data", .tests, 0, "Test/Data", "rows, JSON and optics", true, true⟩,
  ⟨"Test/Ingest", .tests, 0, "Test/Ingest", "the taxonomy", true, true⟩,
  ⟨"Test/Machine", .tests, 0, "Test/Machine", "the machine's batteries and the runtime contracts", true, true⟩,
  ⟨"Test/Program", .tests, 0, "Test/Program", "the program batteries, the generator, the red controls", true, true⟩,
  ⟨"Test/Run", .tests, 0, "Test/Run", "the run API", true, true⟩,
  ⟨"Test/Schema", .tests, 0, "Test/Schema", "the Schema plane", true, true⟩,
  ⟨"Test/Store", .tests, 0, "Test/Store", "the store and its derived instances", true, true⟩,
  -- the OCaml estate
  ⟨"ocaml/gen", .ocaml, 0, "ocaml/gen", "the visible machine, cut from LCNF by `OCaml5.Tools.LcnfGen`", false, true⟩,
  ⟨"ocaml/engine", .ocaml, 1, "ocaml/engine", "the host engine under the generated machine: the store carriers and their property tests, the dispatcher, the log, the API functor", false, true⟩,
  ⟨"ocaml/eff", .ocaml, 0, "ocaml/eff", "`Eff` as an OCaml library: types, wire, JSON, native rows, layout, cut by `OCaml5.Tools.EffGen`", false, true⟩,
  ⟨"ocaml/goldens", .ocaml, 0, "ocaml/goldens", "the wire goldens the OCaml reader is held to", false, true⟩,
  ⟨"ocaml/tools", .ocaml, 0, "ocaml/tools", "the engine's own tools", false, true⟩,
  -- the TypeScript face
  ⟨"ts/eff", .ts, 0, "ts/eff", "the `Eff` IR as a TypeScript library: `read.ts` by hand, the nodes, JSON, profile, forms and wire generated; `ingest/` the foreign recognizers", false, true⟩,
  ⟨"tools/target", .ts, 0, "tools/target", "the tsgo oracle: assignability, rows and atoms against the exports, the profile", false, true⟩,
  -- host gates, scripts, promoted results
  ⟨"harness", .host, 0, "harness", "the host gates: the truth differential (Lean against rc.112), the Schema host, tsdiag, the generation fixtures", false, true⟩,
  ⟨"scripts", .host, 0, "scripts", "the check and generate scripts the Makefile runs", false, true⟩,
  ⟨"generated", .host, 0, "generated", "the promoted TSVs: the corpus index, assignability, row citations, tsdiag, the runtime census, the proof shape", false, true⟩,
  -- the authorities and the record
  ⟨"docs/core", .docs, 0, "docs/core", "the authorities: ontology, coherence, the census, decisions, the language cut, the API surface, the LCNF route, the machine's state", false, true⟩,
  ⟨"docs/STATE.md", .docs, 0, "STATE", "one page: what is true at HEAD, what is next, what the owner must decide", false, true⟩,
  ⟨"docs/ARCHITECTURE.md", .docs, 0, "ARCHITECTURE", "the tree and its dependency direction, in prose", false, true⟩,
  ⟨"docs/GENERATED.md", .docs, 0, "GENERATED", "every generated group: producer, inputs, consumers, check, evidence", false, true⟩,
  ⟨"docs/DESIGN-ISSUES.md", .docs, 0, "DESIGN-ISSUES", "the DI register; a ruling exists only when written here", false, true⟩,
  ⟨"AGENTS.md", .docs, 0, "AGENTS", "the operating rules and the vocabulary", false, true⟩,
  ⟨"docs/research", .docs, 0, "docs/research", "history, not authority, and not walked (two gigabytes of evidence trees); the notes that matter are force-added", false, false⟩,
  ⟨"docs/design", .docs, 0, "docs/design", "the design language notes", false, true⟩,
  -- pinned references
  ⟨"vendor/effect-4.0.0-rc.112", .vendor, 0, "effect rc.112", "the behavioral reference every citation points into", false, false⟩
]

/-- Lean files that are not modules: fixtures a gate reads as text, and the fragments the
generator appends to its outputs. They are counted as files and never as modules. -/
def notModules : List String := ["Test/fixtures", "tools/Effect4Gen/guards"]

/-- An import against the layering that a document names and accepts. `from` is a prefix of
the importing file's path; `to` a prefix of the imported module's name. -/
structure Accepted where
  fromPath : String
  toModule : String
  reason : String
deriving Repr, Inhabited

def accepted : List Accepted := [
  ⟨"tools/Drivers", "Test.Program.Gen", "the corpus generator is the input of `Tools.Corpus` (ARCHITECTURE.md, the Tools row)"⟩
]

/-- May a module in `a` import a module in `b`? Inside a Lean column, only the same height
or lower. The runtime imports only itself. The proof graph imports the runtime, itself and
`ProofGraph`. A tool root imports the runtime, the proof graph and lower tools. The
batteries import everything. Columns without import edges never reach this question. -/
def allowed (a b : Area) : Bool :=
  if a.path == b.path then true else
  match a.column, b.column with
  | .runtime, .runtime => b.layer ≤ a.layer
  | .runtime, _ => false
  | .laws, .runtime => true
  | .laws, .laws => b.layer ≤ a.layer
  | .laws, .tools => b.path == "tools/ProofGraph"
  | .laws, _ => false
  | .tools, .runtime => true
  | .tools, .laws => true
  | .tools, .tools => b.layer ≤ a.layer
  | .tools, _ => false
  | .tests, _ => true
  | _, _ => true

/-- The roots loaded for declaration counts. A module that defines `main` cannot share an
environment with another such module, so the drivers stay out and are measured from disk. -/
def roots : List String := [
  "Test", "OCaml5", "ProofGraph.Ledger", "ProofGraph.Search",
  "Tools.ProgramStructure", "Tools.WireTags", "Drivers.Styles", "Drivers.ForeignCorpus",
  "Tools.ProfileJson", "Tools.GeneratedStamp",
  "Conform.Core.Evidence", "Conform.Core.Obligation", "Conform.Core.Policy", "Conform.Core.Proof",
  "Conform.Core.Report", "Conform.Layout.Build", "Conform.Layout.Check", "Conform.Layout.Laws",
  "Conform.Layout.Layout", "Conform.Layout.Native", "Conform.Layout.Reflect", "Conform.Layout.Types",
  "Conform.Lcnf.Cases", "Conform.Lcnf.Index", "Conform.Lcnf.Rules", "Conform.Lcnf.Semantics",
  "Conform.Lcnf.SemanticsTarget", "Conform.Lcnf.Validity", "Conform.Manifest.Mirror",
  "Conform.Manifest.Readers", "Conform.Model.Container", "Conform.Source.Description",
  "Conform.Spec.Reflect", "Conform.Effect4.Fixtures.Traffic", "Conform.Effect4.LayoutWorld",
  "Conform.Effect4.NormalizationInputs", "Conform.Effect4.TargetLeanNative",
  "Conform.Cli.BoundaryControls", "Conform.Cli.Selftest"
]

/-- One row of the typed-state proof stack: a slice of the plan (§14) and the modules it
lands, by module name. A module is drawn solid once its file exists, dashed until then. -/
structure Slice where
  name : String
  what : String
  modules : List String
deriving Repr, Inhabited

def milestone : List Slice := [
  ⟨"layer 0", "the protocol-typed predicate on the free monad", ["Effect4.Laws.Effects.Protocol"]⟩,
  ⟨"T1", "the checked evidence seam", ["ProofGraph.Proof", "ProofGraph.Search", "ProofGraph.Ledger"]⟩,
  ⟨"T2", "the census, the source table, the skeleton in place", ["Effect4.Laws.Auto.Positions", "Effect4.Laws.Program.Typed.PositionGate", "Effect4.Laws.Program.Typed.Vocabulary", "Effect4.Laws.Program.Typed.Sources", "Effect4.Laws.Program.Typed.TypedStateDecl", "Effect4.Laws.Program.Typed.State"]⟩,
  ⟨"T3 · T4", "frames and the ledger", ["Effect4.Laws.Auto.Frames", "Effect4.Laws.Program.Typed.Frames", "Effect4.Laws.Auto.Obligations"]⟩,
  ⟨"M2", "layer 1: the world, its order, the columns on data", ["Effect4.Laws.Program.Typed.World"]⟩,
  ⟨"M3", "the residual protocol under an answer gate", ["Effect4.Laws.Program.Typed.Residual", "Effect4.Laws.Auto.AnswerGate"]⟩,
  ⟨"M4", "the unary ladder and the typed stack", ["Effect4.Laws.Machine.Keeps", "Effect4.Laws.Program.Typed.Stack"]⟩,
  ⟨"M5", "S1: the denotation is typed; the hooks", ["Effect4.Laws.Program.Typed.Denotation", "Effect4.Laws.Program.Typed.Hooks"]⟩,
  ⟨"M6", "S2 by ledger row", ["Effect4.Laws.Program.Typed.Ledger", "Effect4.Laws.Program.Typed.Step"]⟩,
  ⟨"M7", "S3: the transfer to the compiled machine's exits", ["Effect4.Laws.Program.Typed.Transfer"]⟩,
  ⟨"P2", "the storage interface the store kernel is restated over", ["Effect4.Laws.Machine.Arena"]⟩
]

end Tools.Architecture
