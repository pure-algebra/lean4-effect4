import registry.Core
import Test.Program.TypedCorpus

/-! Registry seat, task 2: `staticEnvAt` validated against the real checker.

Research evidence outside the Test root. Base `be15b062`. Finite checks, not proofs.

How the validation works. `probeEntry` (`Core.lean`) replaces the node at a path by
`withFiber (closeScope (var i) (var i))` and runs `Checker.check` on the whole program. That
node always refuses, and the refusal names level `i`'s type, or says level `i` is unbound. The
replacement leaves the environment at the path unchanged: each checker rule computes a child's
environment from the parent and the siblings checked before it, never from the child. The
checker stops at its first refusal, which in a well-typed program is the probe's. So the probe
reads the environment the checker itself uses at that path, one level at a time, using nothing
of the fold. The refusal's path is also checked (`q = p ++ [0]`), so the checker's path
numbering is the one `Node.at_` and the machine's sites use.

Three checks:

1. Every program node of every typed-corpus program: fold and oracle agree.
2. Every fork site and race cell of the typed corpus and its interleaving pairs: the
   environment at the forked program agrees, the declaration exists, and where the fork is the
   first child of a `bind`, the handle type the checker puts in the continuation's environment
   is `fiberOf` of the declared answer and error.
3. Red controls: eleven deliberately wrong folds, one rule each; each must disagree with the
   oracle somewhere in the corpus or the binder forms. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.Registry.StaticEnvCheck
open Effect4 Effect4.Machine Effect4.Program Research.Pass.Registry

/-- The program the checker types: layer references expanded (`typeOfProgram`). -/
def expanded (program : NEff) : NEff := program.expandRefs

/-- Every program-node path (`foldMapAt`, the generated traversal with paths). -/
def effPaths (program : NEff) : List (List Nat) :=
  foldMapAt_eff [] (· ++ ·) [] program (f_eff := fun _ p => [p])

/-- The fold and the oracle agree at `p`. -/
def agreesWith (fold : List Nat → Option TyEnv) (sig : Signature NativeOp) (root : NEff)
    (p : List Nat) : Bool :=
  match fold p with
  | none => false
  | some env => probeEnv sig root p (env.length + 1) == some env

open Test.Program.TypedCorpus in
def corpus : List (String × Signature NativeOp × NEff) :=
  programs.map fun e => (e.name, nativeSignature e.table, expanded e.program)

open Test.Program.TypedCorpus in
def corpusWithPairs : List (String × Signature NativeOp × NEff) :=
  (programs ++ pairPrograms).map fun e => (e.name, nativeSignature e.table, expanded e.program)

/-! ## 1. Every program node -/

def disagreementsOf (fold : Signature NativeOp → NEff → List Nat → Option TyEnv) :
    List (String × List Nat) :=
  corpus.flatMap fun (name, sig, root) =>
    (effPaths root).filterMap fun p =>
      if agreesWith (fold sig root) sig root p then none else some (name, p)

def checkedPaths : Nat := (corpus.map fun (_, _, root) => (effPaths root).length).sum

def boundPaths : Nat :=
  (corpus.map fun (_, sig, root) =>
    ((effPaths root).filter fun p => (staticEnvAt sig root p).any (!·.isEmpty)).length).sum

def realDisagreements : List (String × List Nat) := disagreementsOf staticEnvAt

#guard corpus.all fun (_, sig, root) => (Checker.check sig [] [] root).toOption.isSome
#guard realDisagreements = []
#eval s!"(1) every node: {corpus.length} programs, {checkedPaths} program paths, {boundPaths} under a binder, {realDisagreements.length} disagreements"

/-! ## 2. Fork sites and race cells -/

/-- One fork site's verdicts: environment agreement at the forked program, a declaration, and
where observable, the handle type in the continuation. -/
structure SiteVerdict where
  envAgrees : Bool
  declared : Bool
  underBinder : Bool
  /-- `none` when the fork is not the first child of a `bind`. -/
  handleAgrees : Option Bool

/-- The recorded-site rule: a race cell's kind is `raceEntrant`, an action's is `action`. -/
def kindOfSite (s : Api.ForkSite) : ForkKind :=
  match s.kind with
  | .raceEntrant => .raceEntrant
  | _ => .action

def verdictAt (sig : Signature NativeOp) (root : NEff) (s : Api.ForkSite) : SiteVerdict :=
  let env := staticEnvAt sig root s.path
  let decl := ForkRecord.declared sig root ⟨⟨0⟩, ⟨0⟩, false, s.path, kindOfSite s⟩
  let bodyEnv := probeEnv sig root (s.path ++ [0]) ((env.map List.length).getD 0 + 1)
  let handle : Option Bool :=
    match kindOfSite s, s.path.reverse with
    | .action, 0 :: 0 :: rest =>
      let q := rest.reverse
      match Node.at_ (.eff root) q, decl with
      | some (.eff (.bind _ _)), some d =>
        let after := probeEnv sig root (q ++ [1]) ((env.map List.length).getD 0 + 2)
        some ((after.bind List.getLast?) == some (.fiberOf d.answer d.error))
      | _, _ => none
    | _, _ => none
  ⟨env.isSome && bodyEnv == env, decl.isSome, env.any (!·.isEmpty), handle⟩

def siteVerdicts : List (String × List Nat × SiteVerdict) :=
  corpusWithPairs.flatMap fun (name, sig, root) =>
    (Api.supervision root).map fun s => (name, s.path, verdictAt sig root s)

def siteCount : Nat := siteVerdicts.length
def siteFailures : List (String × List Nat) :=
  siteVerdicts.filterMap fun (name, p, v) =>
    if v.envAgrees && v.declared && v.handleAgrees != some false then none else some (name, p)
def sitesUnderBinder : Nat := (siteVerdicts.filter fun (_, _, v) => v.underBinder).length
def handleObservations : Nat := (siteVerdicts.filter fun (_, _, v) => v.handleAgrees.isSome).length
def raceCells : Nat :=
  (corpusWithPairs.map fun (_, _, root) =>
    ((Api.supervision root).filter fun s => kindOfSite s == .raceEntrant).length).sum

#guard siteFailures = []
#eval s!"(2) fork sites: {corpusWithPairs.length} programs, {siteCount} sites ({raceCells} race cells), {sitesUnderBinder} under a binder, {handleObservations} handle types observed in a bind's continuation, {siteFailures.length} failures"

/-! ## 2b. Forks under each binder form, with bodies that read the binder -/

open Research.Pass.Registry.Fixtures

/-- The innermost fork site of a program and its declared answer. -/
def innermostDeclared (root : NEff) : Option Ty :=
  ((Api.supervision root).getLast?).bind fun site =>
    (ForkRecord.declared (nativeSignature []) root ⟨⟨0⟩, ⟨0⟩, false, site.path, kindOfSite site⟩).map
      (·.answer)

#guard binderForms.all fun (_, p, _) => Api.wellTyped p
#guard binderForms.all fun (_, p, want) => innermostDeclared p == some want
#guard binderForms.all fun (_, p, _) =>
  (effPaths p).all fun q => agreesWith (staticEnvAt (nativeSignature []) p) (nativeSignature []) p q
-- a race cell under a binder: each entrant declared at its own type
#guard (let p : NEff := .bind (.succeed (s "x")) (.withFiber (.raceAll (.cons (.succeed (v 0))
      (.cons (.fail (n 1)) .nil))))
    (Api.supervision p).map fun site =>
      (ForkRecord.declared (nativeSignature []) p ⟨⟨0⟩, ⟨0⟩, false, site.path, .raceEntrant⟩).map
        fun d => (d.answer, d.error)) =
  [some (.string, .never), some (.never, .nat)]

/-! ## 3. Red controls: wrong folds the oracle must catch -/

/-- One wrong rule each. -/
inductive Flaw
  | bindRest | gen | catchHandler | catchIfHandler | selectArm | matchValue | onExitFinalizer
  | iterateCursor | releaseEnv | layerInherits | stmtBinds
deriving DecidableEq, Repr

def Flaw.all : List Flaw :=
  [.bindRest, .gen, .catchHandler, .catchIfHandler, .selectArm, .matchValue, .onExitFinalizer,
   .iterateCursor, .releaseEnv, .layerInherits, .stmtBinds]

def flawedStep (flaw : Flaw) (sig : Signature NativeOp) (st : TyEnv × Bool) (p : List Nat)
    (node : Node NativeOp) (i : Nat) : Option (TyEnv × Bool) :=
  match flaw, node, i with
  | .bindRest, .eff (.bind _ _), 1 => some st
  | .gen, .eff (.gen _), 0 => some ([], false)
  | .catchHandler, .eff (.catchCause body _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b => (st.1 ++ [b.error], st.2)
  | .catchIfHandler, .eff (.catchIf _ _ _), 1 => some st
  | .selectArm, .eff (.select _ _ _ _), 1 => some st
  | .matchValue, .eff (.matchCause body _ _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b => (st.1 ++ [b.error], st.2)
  | .onExitFinalizer, .eff (.onExit body _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b => (st.1 ++ [b.answer], st.2)
  | .iterateCursor, .eff (.iterate _ _ _ _ _ _), 0 => some st
  | .releaseEnv, .eff (.acquireRelease acquire _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) acquire).toOption.map fun a => (st.1 ++ [a.answer], st.2)
  | .layerInherits, .eff (.provideLayer _ _ _), 0 => some st
  | .layerInherits, .layer _, _ => some st
  | .layerInherits, .layers _, _ => some st
  | .stmtBinds, .stmts (.cons _ _), 1 => some st
  | _, _, _ => stepEnv sig st p node i

def flawedAlong (flaw : Flaw) (sig : Signature NativeOp) :
    Node NativeOp → List Nat → TyEnv × Bool → List Nat → Option (TyEnv × Bool)
  | _, _, st, [] => some st
  | node, p, st, i :: rest =>
    (flawedStep flaw sig st p node i).bind fun st' =>
      (node.child i).bind fun c => flawedAlong flaw sig c (p ++ [i]) st' rest

def flawedEnvAt (flaw : Flaw) (sig : Signature NativeOp) (root : NEff) (path : List Nat) :
    Option TyEnv :=
  (flawedAlong flaw sig (.eff root) [] ([], false) path).map (·.1)

/-- Disagreements each wrong fold produces over the corpus programs and the binder forms. -/
def flawCounts : List (Flaw × Nat) :=
  Flaw.all.map fun flaw =>
    let onCorpus := (disagreementsOf (flawedEnvAt flaw)).length
    let onForms := (binderForms.map fun (_, p, _) =>
      ((effPaths p).filter fun q =>
        !agreesWith (flawedEnvAt flaw (nativeSignature []) p) (nativeSignature []) p q).length).sum
    (flaw, onCorpus + onForms)

#guard flawCounts.all fun (_, k) => 0 < k
#eval s!"(3) red controls: {flawCounts.map fun (f, k) => s!"{repr f}={k}"}"

end Research.Pass.Registry.StaticEnvCheck
