import Effect4.Api.HostSession
import Effect4.Program.Profile
import Effect4.Program.Stream
import Effect4.Program.Packages.SqliteBun
import Effect4.Program.Packages.KeyValueStoreMemory

/-! Three design paths for handle types at the host boundary, tried side by side.
Research evidence, outside the Test root. Base `be15b062`. Finite checks, not proofs.

- Path A: refuse internal handle kinds in host rows' answer and error types.
- Path B: derive a fiber's declared type from its recorded creation site and the checker.
- Path C: check shape and handle declarations in one recursion over the actual encoding. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.HostAnswerPaths
open Effect4 Effect4.Machine Effect4.Program

/-! ## Path A: a located refusal at table admission -/

/-- A type mentions an internal handle kind: fiber, cell, deferred, or a reserved spelling. -/
def mentionsInternal : Ty → Bool
  | .fiberOf _ _ => true
  | .refOf _ => true
  | .deferredOf _ _ => true
  | .handle target => internalHandleTargets.contains target
  | .option a => mentionsInternal a
  | .list a => mentionsInternal a
  | .causeOf a => mentionsInternal a
  | .prod a b => mentionsInternal a || mentionsInternal b
  | .except a b => mentionsInternal a || mentionsInternal b
  | .exitOf a b => mentionsInternal a || mentionsInternal b
  | .union a b => mentionsInternal a || mentionsInternal b
  | _ => false

def hostRowOk (row : Row) : Bool := !mentionsInternal row.answer && !mentionsInternal row.error

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "research probe"

/-- Every host row the tree defines. -/
def inTreeRows : List Row :=
  Packages.sqliteBun ++ Packages.keyValueStoreMemory ++ Stream.table "Stream.Probe" .nat .never ++
    [Profile.Scalar.waitRow, Profile.Resource.acquireRow, Profile.Resource.useRow,
     Profile.Resource.releaseRow]

#guard hostRowOk fiberRow = false
#guard inTreeRows.all hostRowOk
#guard inTreeRows.length = 15

/-! ## Path B: fiber declarations from creation sites -/

def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩
def table : RowTable := [fiberRow]

/-- Fork a child returning `child`, ask the host for a fiber, join the fiber it names. -/
def program (child : Term) : Api.Program :=
  .bind (.withFiber (.fork (.succeed child) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

def wrongProgram : Api.Program := program (.lit (.str "wrong"))
def rightProgram : Api.Program := program (.lit (.nat 7))

/-- The machine after the root's first evaluation: the child forked, the root parked. -/
def parkedOf (p : Api.Program) : NativeMachine := (Api.replay p 1000 [Api.evaluate] [] table).machine

/-- The declared type of a fiber, from its recorded origin and the checker. Source forks are
typed at their site (the path of the fork action, here `[0, 0]`); this probe's fork is under no binder, so the empty static environment is
exact. A general version needs the static environment at the site (not yet a function), and an
internal fork, whose site is `[]` (`Machine/Fibers.lean:226`), has no source evidence at all. -/
def declaredFiberTy (root : Api.Program) (m : NativeMachine) (id : FiberId) : Option EffTy :=
  match m.fiber? id with
  | none => none
  | some f =>
    match f.origin with
    | .root => Api.typeOf root table
    | .forked _ _ [] => none
    | .forked _ _ site =>
      match Node.at_ (.eff root) site with
      | some (.action (.fork body _)) => effTy (nativeSignature table) [] body
      | some (.action (.forkIn body _ _)) => effTy (nativeSignature table) [] body
      | some (.action (.forkScoped body _)) => effTy (nativeSignature table) [] body
      | _ => none

#guard ((parkedOf wrongProgram).fiber? ⟨1⟩).map (·.origin) = some (.forked ⟨0⟩ true [0, 0])
#guard (declaredFiberTy wrongProgram (parkedOf wrongProgram) ⟨1⟩).map (·.answer) = some .string
#guard (declaredFiberTy rightProgram (parkedOf rightProgram) ⟨1⟩).map (·.answer) = some .nat
#guard (declaredFiberTy wrongProgram (parkedOf wrongProgram) ⟨0⟩).map (·.answer) = some .nat

/-! ## Path C: one recursion for shape and handles -/

/-- Shape and fiber declarations together, over the encoding `Val.hasTy` reads: products as a
two-cell list, Results and exits as constructors, snapshots decoded. Everything else falls back
to the existing shape check (scalars, today's number-only cells and deferreds, causes). -/
def fitsB (decl : FiberId → Option EffTy) (v : Val) : Ty → Bool
  | .fiberOf a e =>
    match v with
    | .handle 1 id =>
      match decl ⟨id⟩ with
      | some d => d.answer.sub a && d.error.sub e
      | none => false
    | _ => false
  | .prod a b =>
    match v with
    | .list [x, y] => fitsB decl x a && fitsB decl y b
    | _ => false
  | .except e a =>
    match v with
    | .ctor 0 [err] => fitsB decl err e
    | .ctor 1 [val] => fitsB decl val a
    | _ => false
  | .exitOf a e =>
    match v with
    | .ctor 0 [x] => fitsB decl x a
    | _ => Val.hasTy v (.exitOf a e)
  | .option a =>
    match v with
    | .none => true
    | .some x => fitsB decl x a
    | _ => false
  | .list a =>
    match v with
    | .list xs => xs.attach.all fun ⟨x, _⟩ => fitsB decl x a
    | _ =>
      match Val.snapshot? v with
      | some ids => ids.all fun id => fitsB decl (Value.fiber id.value) a
      | none => false
  | .union l r => fitsB decl v l || fitsB decl v r
  | ty => Val.hasTy v ty

/-- Fiber 1 is declared to return a string. -/
def stringFiber : FiberId → Option EffTy := fun id => if id = ⟨1⟩ then some (EffTy.pure .string) else none
def natFiber : FiberId → Option EffTy := fun id => if id = ⟨1⟩ then some (EffTy.pure .nat) else none

-- the four gaps the contract's predicate probe shows in `HandlesFit`, now refused
#guard fitsB stringFiber (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit) = false
#guard fitsB stringFiber (.ctor 1 [Value.fiber 1]) (.except .never (.fiberOf .nat .never)) = false
#guard fitsB stringFiber (Value.exitOk (Value.fiber 1)) (.exitOf (.fiberOf .nat .never) .never) = false
#guard fitsB stringFiber (Value.fiber 1) (.union (.fiberOf .nat .never) .unit) = false
-- and accepted when the declaration fits
#guard fitsB natFiber (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit)
#guard fitsB natFiber (.ctor 1 [Value.fiber 1]) (.except .never (.fiberOf .nat .never))
#guard fitsB natFiber (Value.exitOk (Value.fiber 1)) (.exitOf (.fiberOf .nat .never) .never)
#guard fitsB natFiber (Value.fiber 1) (.union (.fiberOf .nat .never) .unit)
-- the existing shape check passes all four regardless of the declaration
#guard Val.hasTy (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit)

/-- On handle-free values the combined check agrees with the existing shape check. -/
def samples : List (Val × Ty) :=
  [(.nat 3, .nat), (.str "a", .string), (.nat 1, .string), (.unit, .unit),
   (.list [.nat 1, .str "x"], .prod .nat .string), (.list [.nat 1], .prod .nat .string),
   (.some (.nat 1), .option .nat), (.none, .option .string), (.some (.str "x"), .option .nat),
   (.ctor 1 [.nat 2], .except .string .nat), (.ctor 0 [.str "e"], .except .string .nat),
   (.ctor 0 [.nat 2], .except .string .nat), (.unit, .union .nat .unit),
   (.str "b", .union .nat .unit), (.list [.nat 1, .nat 2], .list .nat),
   (.list [.nat 1, .str "x"], .list .nat), (.str "k", .lit "k"), (.str "j", .lit "k"),
   (Value.exitOk (.nat 4), .exitOf .nat .never), (.nat 0, .never), (.bool true, .unknown)]

#guard samples.all fun (v, ty) => fitsB (fun _ => none) v ty == Val.hasTy v ty

/-! ## B and C together: the boundary check with a derived registry

The forged reply is refused and the honest one accepted, with no type stored in any value:
the declaration comes from the recorded site and the checker. -/

def admitWithRegistry (root : Api.Program) (v : Val) (ty : Ty) : Bool :=
  fitsB (declaredFiberTy root (parkedOf root)) v ty

#guard admitWithRegistry wrongProgram (Value.fiber 1) (.fiberOf .nat .never) = false
#guard admitWithRegistry rightProgram (Value.fiber 1) (.fiberOf .nat .never)
-- today's check accepts both
#guard Val.hasTy (Value.fiber 1) (.fiberOf .nat .never)

/-! ## D: a fiber handle inside a pair, with no host involved

M6 must type this program, since it is checked and closed. Its typed state stores the pair,
whose handle evidence `HandlesFit` skips (products are two-cell lists, the rule looks for a
pair). After `fst` the awaited handle needs its fiber's declaration, which the stored pair's
evidence cannot supply. So the membership amendment is needed for M6 itself, not only for host
replies. -/

def pairProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 7))) opts))
    (.bind (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))
      (.awaitFiber (.app "fst" (.cons (.var 1) .nil)) .joinEffect))

#guard Api.typeOf pairProgram [] = some (EffTy.pure .nat)
#guard (Api.run pairProgram 1000).exit = some (.success (.nat 7))

#eval IO.println "Host-answer path probes: all guards passed."

end Research.HostAnswerPaths
