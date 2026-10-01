import registry.Core
import Test.Program.ExitTypeLane

/-! Verifier of the registry seat: does the exit-type lane reach the two layer gaps?

Research evidence outside the Test root. Base `be15b062`. Written by the adversarial verifier;
it imports the seat's `Core.lean` unchanged. Finite checks, not proofs.

The seat's note (§5) says the lane cannot reach the gaps. This counts, over every typed lane
program (`lanePrograms`: the typed corpus, its pairs and the random corpus), the layer leaves
that could show them:

* gap 1: a `Layer.effect` or `Layer.effectDiscard` body holding a binder, whose enclosing
  `provideLayer` sits under a non-empty static environment (`staticEnvAt`);
* gap 2: a `Layer.effect` body whose checked answer is not below the key's service type, or a
  `Layer.succeed` literal whose type is not.

The seat's three programs are appended as positive controls; the detector must find them and
only them. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.RegistryVerify.LaneReach
open Effect4 Effect4.Machine Effect4.Program Research.Pass.Registry
open Test.Program.ExitTypeLane (lanePrograms)
open Test.Program.TypedCorpus (Entry)

def layerSites (p : NEff) : List (LayerTerm NativeOp × List Nat) :=
  foldMapAt_eff [] (· ++ ·) [] p (f_layer := fun l q => [(l, q)])

def effPaths (program : NEff) : List (List Nat) :=
  foldMapAt_eff [] (· ++ ·) [] program (f_eff := fun _ p => [p])

def isBinder : NEff → Bool
  | .bind _ _ | .gen _ | .catchCause _ _ | .catchIf _ _ _ | .select _ _ _ _ | .matchCause _ _ _
  | .onExit _ _ | .iterate _ _ _ _ _ _ | .acquireRelease _ _ => true
  | _ => false

def hasBinder (body : NEff) : Bool :=
  (effPaths body).any fun q => match Node.at_ (.eff body) q with
    | some (.eff e) => isBinder e
    | _ => false

/-- The nearest enclosing `provideLayer` path of a layer path. -/
def enclosingProvide (root : NEff) (q : List Nat) : Option (List Nat) :=
  ((List.range q.length).reverse.map fun k => q.take k).find? fun pre =>
    match Node.at_ (.eff root) pre with
    | some (.eff (.provideLayer _ _ _)) => true
    | _ => false

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def errLeak : NEff :=
  .bind (.succeed (.lit (.nat 9)))
    (.scoped (.provideLayer (.effect key (.bind (.succeed (.lit (.str "x"))) (.fail (.var 0)))) false
      (.service key)))
def valueLeak : NEff := .scoped (.provideLayer (.effect key (.succeed (.lit (.str "x")))) false (.service key))
def succeedLeak : NEff := .provideLayer (.succeed key (.bool true)) false (.service key)
def controls : List Entry :=
  [{ name := "errLeak", program := errLeak }, { name := "valueLeak", program := valueLeak },
   { name := "succeedLeak", program := succeedLeak }]

def typed : List (String × Signature NativeOp × NEff) :=
  (lanePrograms ++ controls).filterMap fun (e : Entry) =>
    if Api.wellTyped e.program e.table then
      some (e.name, nativeSignature e.table, e.program.expandRefs)
    else none

/-- Gap 1 candidates: an effect or effectDiscard body with a binder inside, whose enclosing
provideLayer has a non-empty static environment. -/
def gap1 : List String :=
  typed.filterMap fun (name, sig, root) =>
    let hits := (layerSites root).filter fun (l, q) =>
      let body? : Option NEff := match l with
        | .effect _ b => some b
        | .effectDiscard b => some b
        | _ => none
      match body? with
      | none => false
      | some b =>
        hasBinder b &&
          ((enclosingProvide root q).bind fun pre => staticEnvAt sig root pre).any (!·.isEmpty)
    if hits.isEmpty then none else some name

/-- Gap 2 candidates: an effect leaf whose body's answer is not below the key's service type,
or a succeed leaf whose value's type is not. -/
def gap2 : List String :=
  typed.filterMap fun (name, sig, root) =>
    let hits := (layerSites root).filter fun (l, q) =>
      match l with
      | .effect key b =>
        match (Checker.check sig [] (q ++ [0]) b).toOption, sig.serviceTy key with
        | some t, some want => !(t.answer.sub want)
        | _, _ => false
      | .succeed key lit =>
        match (termTy sig [] (.lit lit)), sig.serviceTy key with
        | some t, some want => !(t.sub want)
        | _, _ => false
      | _ => false
    if hits.isEmpty then none else some name

#guard typed.length = 8587
#guard (typed.filter fun (_, _, r) => !(layerSites r).isEmpty).length = 1346
-- the detector finds the seat's controls and nothing in the 8584 typed lane programs
#guard gap1 = ["errLeak"]
#guard gap2 = ["valueLeak", "succeedLeak"]

#eval IO.println "verify-LaneReach: all guards passed."

end Research.Pass.RegistryVerify.LaneReach
