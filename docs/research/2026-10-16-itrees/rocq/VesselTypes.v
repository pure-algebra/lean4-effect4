(** * VesselTypes: the vessel's domain and services as typed events

    The liquid buffer vessel (branch [codex/vessel-dogfood], [apps/vessel/]) sizes a tank, builds
    its STEP assembly through OCCT and simulates its level through an FMI unit. Its Lean domain
    ([Test/Dogfood/Scenario/Vessel/Domain.lean]) types quantities, units, the level datum, design
    revisions, studies and evidence, but its workflow ([Workflow.lean]) passes untyped records:
    "Two declarations with the same fields have the same [Ty] description" ([domain/BASIS.md]).
    So the workflow checks at run time that each reply belongs to the request's study.

    Here the same domain indexes the services themselves:
    - a quantity is indexed by its dimension, so a flow cannot stand where a duration stands, and
      the one product the workflow takes, flow by duration, is a volume ([inventory]);
    - a level is indexed by its datum, and the workflow's levels are all from the internal bottom;
    - a revision is positive by its type, as [DesignRef] admits only a positive one;
    - evidence is indexed by its study and its kind, and exists only for a passed check;
    - each service is an event family whose answer type depends on the study in the request:
      [Exchange s r] answers a [geometry_reply s], whose evidence is for [s] by type.

    So "the reply belongs to the request's study" is a typing fact of every host of these events,
    not a property each run checks ([Vessel.v] relates the two). This file uses only the
    standard library, so the ITree development and the ctrees one ([VesselCtree.v]) share it. *)

(* An event family's index universe stays above Set, as [interp] needs. *)
Unset Universe Minimization ToSet.

From Coq Require Import NArith String Bool.

(** ** Quantities, levels, revisions *)

(** A dimension; each has one canonical unit: µL/s, s, mm and µL ([domain/BASIS.md]). *)
Inductive dim : Set := Flow | Duration | Length | Volume.

(** A quantity of a dimension, in its canonical unit. *)
Record qty (d : dim) : Set := Qty { magnitude : N }.
Arguments Qty {d}.
Arguments magnitude {d}.

(** The inventory a flow needs over a hold-up time: [requiredInventoryMicrolitre]. *)
Definition inventory (f : qty Flow) (t : qty Duration) : qty Volume :=
  Qty (magnitude f * magnitude t).

(** A level datum. Every level of the first profile is from the internal bottom. *)
Inductive datum : Set := InternalBottom | SiteElevation.

(** A level above a datum, in millimetres. *)
Record level (z : datum) : Set := Level { level_mm : N }.
Arguments Level {z}.
Arguments level_mm {z}.

(** A design and its revision, positive by type ([DesignRef]). *)
Record design : Set := Design { vessel_id : string; revision : positive }.

(** A study: one revision with the digest of its exact request ([StudyRef]). *)
Record study : Set := Study { design_of : design; input_digest : string }.

(** ** Evidence *)

Inductive kind : Set := Geometry | LevelSimulation | StepAssembly.

(** Evidence of a kind for a study, by type: [EvidenceRelevant]'s [e.study = expected] and
    [e.kind = kind] hold by construction. It exists only for a passed check. *)
Record evidence (s : study) (k : kind) : Set := Evidence {
  tool : string;
  tool_version : string;
  artifact : string }.
Arguments Evidence {s k}.
Arguments tool {s k}. Arguments tool_version {s k}. Arguments artifact {s k}.

(** ** The request and the services' replies, each for one study *)

Record request (s : study) : Set := Request {
  diameter : qty Length;
  height : qty Length;
  minimum_level : level InternalBottom;
  maximum_level : level InternalBottom;
  initial_level : level InternalBottom;
  flow : qty Flow;
  hold_up : qty Duration;
  inlet : qty Flow;
  outlet : qty Flow;
  duration : qty Duration }.
Arguments Request {s}.
Arguments diameter {s}. Arguments height {s}. Arguments minimum_level {s}.
Arguments maximum_level {s}. Arguments initial_level {s}. Arguments flow {s}.
Arguments hold_up {s}. Arguments inlet {s}. Arguments outlet {s}. Arguments duration {s}.

(** The STEP service's reply: the usable capacity, and the geometry and assembly evidence. *)
Record geometry_reply (s : study) : Set := GeometryReply {
  capacity : qty Volume;
  geometry_evidence : evidence s Geometry;
  step_evidence : evidence s StepAssembly }.
Arguments GeometryReply {s}.
Arguments capacity {s}. Arguments geometry_evidence {s}. Arguments step_evidence {s}.

(** The FMI service's reply: the sampled level's extremes, and the simulation's evidence. *)
Record simulation_reply (s : study) : Set := SimulationReply {
  minimum_observed : level InternalBottom;
  maximum_observed : level InternalBottom;
  simulation_evidence : evidence s LevelSimulation }.
Arguments SimulationReply {s}.
Arguments minimum_observed {s}. Arguments maximum_observed {s}.
Arguments simulation_evidence {s}.

(** A service answers, or fails with a message (the rows' [ToolFailure]). *)
Inductive tool_result (A : Set) : Set :=
| Answered (a : A)
| ToolFailure (message : string).
Arguments Answered {A}.
Arguments ToolFailure {A}.

(** ** The services as typed events *)

(** The STEP service: its answer's type depends on the study in the request. *)
Variant GeometryE : Type -> Type :=
| Exchange (s : study) (r : request s) : GeometryE (tool_result (geometry_reply s)).

(** The FMI service. *)
Variant SimulationE : Type -> Type :=
| Simulate (s : study) (r : request s) : SimulationE (tool_result (simulation_reply s)).

(** ** The workflow's result *)

(** An accepted assessment, with the evidence bundle of its study ([CheckedBundle]). *)
Record assessment (s : study) : Set := Assessment {
  required : qty Volume;
  usable : qty Volume;
  maximum_seen : level InternalBottom;
  geometry_of : evidence s Geometry;
  simulation_of : evidence s LevelSimulation;
  step_of : evidence s StepAssembly }.
Arguments Assessment {s}.
Arguments required {s}. Arguments usable {s}. Arguments maximum_seen {s}.
Arguments geometry_of {s}. Arguments simulation_of {s}. Arguments step_of {s}.

(** Why the workflow refuses: the three checks it makes on the replies' values. *)
Inductive refusal : Set := BelowHoldUp | BelowWorkingLimit | AboveWorkingLimit.

Inductive verdict (s : study) : Set :=
| Accepted (a : assessment s)
| Refused (why : refusal)
| Failed (message : string).
Arguments Accepted {s}.
Arguments Refused {s}.
Arguments Failed {s}.

(** The capacity check: the usable capacity is not below the inventory the duty needs. *)
Definition holds_up {s} (r : request s) (g : geometry_reply s) : bool :=
  negb (N.ltb (magnitude (capacity g)) (magnitude (inventory (flow r) (hold_up r)))).

(** The level checks: the sampled extremes stay inside the working limits. *)
Definition above_minimum {s} (r : request s) (m : simulation_reply s) : bool :=
  negb (N.ltb (level_mm (minimum_observed m)) (level_mm (minimum_level r))).
Definition below_maximum {s} (r : request s) (m : simulation_reply s) : bool :=
  negb (N.ltb (level_mm (maximum_level r)) (level_mm (maximum_observed m))).

(** The assessment the two replies make. *)
Definition assessment_of {s} (r : request s) (g : geometry_reply s) (m : simulation_reply s)
    : assessment s :=
  Assessment (inventory (flow r) (hold_up r)) (capacity g) (maximum_observed m)
    (geometry_evidence g) (simulation_evidence m) (step_evidence g).

(** The verdict after the simulation's reply. *)
Definition judge {s} (r : request s) (g : geometry_reply s) (m : simulation_reply s) : verdict s :=
  if negb (above_minimum r m) then Refused BelowWorkingLimit
  else if negb (below_maximum r m) then Refused AboveWorkingLimit
  else Accepted (assessment_of r g m).
