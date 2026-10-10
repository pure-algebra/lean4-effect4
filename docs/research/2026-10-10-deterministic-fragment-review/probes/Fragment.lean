import Effect4.Author
import Effect4.Program.LayerView

/-!
Design probe only. Placement: PLAN.md, fragment_summary_sound -> workers_commute ->
fragment_observations_agree. This executable checker has no soundness theorem.
The carrier of each fold is analysis metadata, never executable program syntax.
-/
namespace DetProbe
open Effect4 Effect4.Program

inductive Abstract where
  | unit | scalar | atom | cell (origin : Nat) | fiber (worker : Nat)
  | tuple (left right : Abstract)
  deriving Repr, BEq

def Abstract.dataOnly : Abstract → Bool
  | .unit | .scalar | .atom => true
  | .tuple a b => a.dataOnly && b.dataOnly
  | _ => false

abbrev Env := List Abstract
abbrev TR (_ : TermFam) := Env → Option (List Abstract)

/-- A small abstract term algebra. Unknown atoms and aggregate selectors refuse. -/
def termAlg : TermAlgebra TR where
  term_var i := fun env => (env[i]?).map fun a => [a]
  term_lit l := fun _ => some [match l with | .unit => .unit | .nat _ => .scalar | _ => .atom]
  term_app name args := fun env => do
    let xs ← args env
    if name == "pair" then
      match xs with | [a, b] => some [.tuple a b] | _ => none
    else if name == "succ" then
      match xs with | [.scalar] => some [.scalar] | _ => none
    else if name == "add" || name == "mul" then
      match xs with | [.scalar, .scalar] => some [.scalar] | _ => none
    else none
  term_record _ _ _ := fun _ => none
  term_field _ _ _ := fun _ => none
  term_recordSet _ _ _ := fun _ => none
  term_tupleAt _ _ := fun _ => none
  term_fold _ _ _ _ := fun _ => none
  terms_nil := fun _ => some []
  terms_cons a rest := fun env => do
    let [a] ← a env | none
    let xs ← rest env
    some (a :: xs)

def term (env : Env) (t : Term) : Option Abstract := do
  let [a] ← cata_term termAlg t env | none
  some a

inductive Mode where
  | read | write | add
  deriving Repr, BEq

structure Access where
  origin : Nat
  mode : Mode
  path : List Nat
  deriving Repr

structure Worker where
  path : List Nat
  accesses : List Access
  result : Abstract
  deriving Repr

inductive Reason where
  | term | expectedCell | nonData
  | workerAllocation | allocationAfterFork | parentDuringWorkers
  | nestedFork | unsupportedFork | forkAfterJoin | badJoin
  | workerResult | unjoined | returnedHandle
  | unsupported (constructor : String)
  | conflict (origin : Nat) (otherPath : List Nat)
  deriving Repr, BEq

structure Fault where
  path : List Nat
  reason : Reason
  deriving Repr

structure State where
  env : Env := []
  worker : Bool := false
  origins : List (List Nat) := []
  accesses : List Access := []
  workers : List Worker := []
  joined : List Nat := []
  deriving Repr

abbrev Reader := List Nat → State → Except Fault (Abstract × State)
abbrev Carrier (_ : EffFam) := Reader

def refuse (p : List Nat) (why : Reason) : Except Fault α := .error ⟨p, why⟩
def readTerm (p : List Nat) (env : Env) (t : Term) : Except Fault Abstract :=
  match term env t with | some a => .ok a | none => refuse p .term

def State.waiting (s : State) : Bool :=
  (List.range s.workers.length).any fun i => !(s.joined.contains i)

def addAccess (p : List Nat) (s : State) (i : Nat) (m : Mode) (result : Abstract) :
    Except Fault (Abstract × State) :=
  if !s.worker && s.waiting then refuse p .parentDuringWorkers
  else .ok (result, {s with accesses := s.accesses ++ [⟨i, m, p⟩]})

/-- Recognized addition is a closed operation family, not a caller-supplied commutativity flag. -/
def isAddition (level : Nat) : Term → Bool
  | .app "succ" (.cons (.var i) .nil) => i == level
  | .app "add" (.cons (.var i) (.cons (.lit (.nat _)) .nil)) => i == level
  | _ => false

def row (op : NativeOp) (request : Term) : Reader := fun p s => do
  let a ← readTerm p s.env request
  match op, a with
  | .refMake, .scalar =>
    if s.worker then refuse p .workerAllocation
    else if !s.workers.isEmpty then refuse p .allocationAfterFork
    else .ok (.cell s.origins.length, {s with origins := s.origins ++ [p]})
  | .refGet, .cell i => addAccess p s i .read .scalar
  | .refSet, .tuple (.cell i) .scalar => addAccess p s i .write (.cell i)
  | .refUpdateWith f, .cell i =>
    let value ← readTerm p (s.env ++ [.scalar]) f
    if value != .scalar then refuse p .nonData
    else addAccess p s i (if isAddition s.env.length f then .add else .write) .unit
  | .refGetAndUpdateWith f, .cell i | .refUpdateAndGetWith f, .cell i =>
    let value ← readTerm p (s.env ++ [.scalar]) f
    if value != .scalar then refuse p .nonData
    else addAccess p s i .write .scalar
  | .refMake, _ | .refSet, _ => refuse p .nonData
  | .refGet, _ | .refUpdateWith _, _ | .refGetAndUpdateWith _, _ |
      .refUpdateAndGetWith _, _ => refuse p .expectedCell
  | _, _ => refuse p (.unsupported "operation")

/-- The phase analysis consumes the generated layer view and defaults to refusal. -/
def layer (fam : EffFam) (ctor : String) (args : List (ArgF NativeOp Carrier)) : Reader :=
  fun p s => do
  match fam, ctor, args with
  | .eff, "succeed", [.term t] | .eff, "sync", [.term t] =>
    let a ← readTerm p s.env t
    .ok (a, s)
  | .eff, "bind", [.child .eff a, .child .eff b] =>
    let (value, s') ← a (p ++ [0]) s
    let (result, s'') ← b (p ++ [1]) {s' with env := s.env ++ [value]}
    .ok (result, {s'' with env := s.env})
  | .eff, "suspend", [.child .eff body] => body (p ++ [0]) s
  | .eff, "perform", [.op op, .term request] => row op request p s
  | .eff, "yieldNow", [.nat _] => .ok (.unit, s)
  | .eff, "withFiber", [.child .action action] => action (p ++ [0]) s
  | .action, "fork", [.child .eff body, .forkOptions opts] =>
    if s.worker then refuse p .nestedFork
    else if opts.daemon || opts.startImmediately then refuse p .unsupportedFork
    else if !s.joined.isEmpty then refuse p .forkAfterJoin
    else
      let (value, child) ← body (p ++ [0])
        {s with worker := true, accesses := [], workers := [], joined := []}
      if !value.dataOnly then refuse p .workerResult
      else .ok (.fiber s.workers.length,
        {s with workers := s.workers ++ [⟨p, child.accesses, value⟩]})
  | .eff, "awaitFiber", [.term t, .mode .joinEffect] =>
    if s.worker then refuse p .badJoin
    else
      let .fiber i ← readTerm p s.env t | refuse p .badJoin
      match s.workers[i]? with
      | some w => .ok (w.result, {s with joined := i :: s.joined})
      | none => refuse p .badJoin
  | _, _, _ => refuse p (.unsupported ctor)

def compatible (a b : Access) : Bool :=
  a.origin != b.origin || (a.mode == .read && b.mode == .read) ||
    (a.mode == .add && b.mode == .add)

def collision (xs ys : List Access) : Option Fault :=
  xs.findSome? fun a => ys.findSome? fun b =>
    if compatible a b then none else some ⟨a.path, .conflict a.origin b.path⟩

def conflicts : List Worker → Option Fault
  | [] => none
  | w :: ws => (ws.findSome? fun other => collision w.accesses other.accesses).orElse
      fun _ => conflicts ws

/-- Reuse the existing typing certificate. Only fragment refusals arise here. -/
def analyze (typed : Api.Typed []) : Except Fault State := do
  let (value, s) ← cata_eff (EffAlgebra.ofLayer layer) typed.program [] {}
  if s.waiting then refuse [] .unjoined
  else if !value.dataOnly then refuse [] .returnedHandle
  else match conflicts s.workers with
    | some f => .error f
    | none => .ok s

/-- A type refusal retains its original path and reason. A fragment refusal is distinct. -/
inductive InspectRefusal where
  | typing (refusal : TypeRefusal)
  | fragment (fault : Fault)

/-- Convenience entry for a raw program. The typed entry does not repeat its typing check. -/
def inspect (program : NativeEff) : Except InspectRefusal State := do
  let typed ← (Api.check program).mapError InspectRefusal.typing
  (analyze typed).mapError InspectRefusal.fragment

end DetProbe
