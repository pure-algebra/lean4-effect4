import Effect4.Program.Check
import Effect4.Program.Typing.SourceDocument
set_option autoImplicit false
namespace Effect4.Program.CheckCache
open Effect4 Effect4.Program Check
/-- The contextual evidence for a candidate at a target address and focus. -/
inductive Evidence where
  /-- The candidate types at the target's signature and environment with the focus's exact type (`ty`). -/
  | exactFit (ty : EffTy)
  /-- The candidate types at the target's signature and environment with a different type (`actual` vs `expected`). -/
  | typeMismatch (expected actual : EffTy)
  /-- The candidate is refused by the checker at the target's signature, environment and path. -/
  | refused (why : TypeRefusal)
  /-- The candidate comes from another lexical environment (`sourceEnv` vs `targetEnv`); moving it needs a scope shift (Slice F). -/
  | differentEnv (sourceEnv targetEnv : TyEnv)
deriving DecidableEq

/-- One candidate returned by `suggest`, with its source address (if local), its context key, and
its contextual evidence. -/
structure Suggestion where
  program : NativeEff
  sourcePath : Option (List Nat)
  key : CheckInput
  evidence : Evidence
deriving DecidableEq

def evaluateCandidate (o : Oracle) (sig : SigData) (targetEnv : TyEnv) (expected : EffTy)
    (targetPath : List Nat) (sourcePath : Option (List Nat)) (sourceEnv : TyEnv)
    (prog : NativeEff) : Checked Suggestion := do
  let key := CheckInput.part sig targetEnv prog
  if sourceEnv = targetEnv then
    let answer ← Checked.ask o key
    let verdict := answer.result.mapError ((fun r => ⟨targetPath ++ r.path,r.reason⟩))
    let evidence := match verdict with
      | .ok ty => if ty = expected then Evidence.exactFit ty else .typeMismatch expected ty
      | .error why => .refused why
    pure ⟨prog, sourcePath, key, evidence⟩
  else pure ⟨prog, sourcePath, key, .differentEnv sourceEnv targetEnv⟩

def evaluateCandidates (o : Oracle) (sig : SigData) (targetEnv : TyEnv) (expected : EffTy)
    (targetPath : List Nat) : List (Option (List Nat) × TyEnv × NativeEff) → Checked (List Suggestion)
  | [] => pure []
  | (sp, sourceEnv, prog) :: rest => do
    let suggestion ← evaluateCandidate o sig targetEnv expected targetPath sp sourceEnv prog
    let later ← evaluateCandidates o sig targetEnv expected targetPath rest
    pure (suggestion :: later)
/-- Harvest local candidate items `(sourcePath, sourceEnv, prog)` for `d` at `targetPath` and
`focus`:
1. Any caller-supplied candidate programs `supplied`, checked at `focus.env`.
2. Variables in `focus.env` as `.succeed (.var i)`.
3. Unit-request external rows in `(d.session.app.withHoles d.session.sketch.holes).rows` as
   `.perform (.external i) (.lit .unit)`.
4. Typed sub-programs in `d.session.table` outside `targetPath`, with their own `e.path` and
   `e.env`. -/
def localCandidates (d : Doc) (targetPath : List Nat) (focus : Focus NativeOp)
    (supplied : List NativeEff := []) : List (Option (List Nat) × TyEnv × NativeEff) :=
  let suppliedItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    supplied.map fun p => (none, focus.env, p)
  let varItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    (List.range focus.env.length).map fun i => (none, focus.env, .succeed (.var i))
  let allRows := (d.session.app.withHoles d.session.sketch.holes).rows
  let rowItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    allRows.zipIdx.filterMap fun (r, i) =>
      if r.request == .unit then some (none, focus.env, .perform (.external i) (.lit .unit))
      else none
  let tableItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    d.session.table.filterMap fun e =>
      if decide (e.path = targetPath) then none
      else
        match (Node.eff d.session.sketch.program).at_ e.path, e.env with
        | some (.eff p), some (.env tys) => some (some e.path, tys, p)
        | _, _ => none
  (suppliedItems ++ varItems ++ rowItems ++ tableItems).eraseDups

/-- Bounded search response from `suggest`, carrying its pagination bounds, next cursor, document
revision, target context, and candidate suggestions. -/
structure SuggestResult where
  doc : DocId
  revision : Nat
  path : List Nat
  cursor : Nat
  limit : Nat
  total : Nat
  nextCursor : Option Nat
  sig : SigData
  env : TyEnv
  expected : EffTy
  suggestions : List Suggestion

def suggest (o : Oracle) (d : Doc) (path : List Nat) (limit : Nat := 16)
    (cursor : Nat := 0) (supplied : List NativeEff := []) : Checked (Option SuggestResult) := do
  match d.session.focusAt path with
  | none => pure none
  | some focus =>
    let sig := sketchSigData d.session.sketch d.session.app path
    let all := localCandidates d path focus supplied
    let total := all.length
    let page := (all.drop cursor).take limit
    let nextCursor := if cursor + limit < total then some (cursor + limit) else none
    let suggestions ← evaluateCandidates o sig focus.env focus.ty path page
    pure (some {
      doc := d.id, revision := d.revision, path := path,
      cursor := cursor, limit := limit, total := total, nextCursor := nextCursor,
      sig := sig, env := focus.env, expected := focus.ty, suggestions := suggestions })
end Effect4.Program.CheckCache
