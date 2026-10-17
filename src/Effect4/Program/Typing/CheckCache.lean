import Effect4.Program.Typing.SourceDocument

/-!
# Program.Typing.CheckCache — contextual signature data, verdict cache, and bounded local candidate search

Slice C of `docs/research/2026-10-17-proof-scout/README.md` (§7.3).

* `PartSig`, `SigData`, `SigData.signature`, `bodyIndex`, `partSigAt`, `sketchSigData`: the typing
  signature at an address of a sketch represented as first-order data, read off the root and the
  path with no traversal of the program.
* `CheckKey`, `Entry`, `SigData.extendsB`, `lookup`, `insert`: a checker-verdict cache keyed by the
  program, the signature data, and the ordered environment (omitting the path). An exact hit rebases
  its refusal to the asked path (`TypeRefusal.rebase`), and a positive verdict also answers at a
  prefix extension of the rows (`SigData.extendsB`).
* `Evidence`, `Suggestion`, `SuggestResult`, `suggest`: a bounded, paginated local candidate search
  at an address of a `Doc`, returning each candidate with its contextual evidence and the search
  bounds and document revision.

The laws are in `Effect4.Laws.Program.Typing.CheckCache`.
-/

set_option autoImplicit false

deriving instance DecidableEq for Effect4.Program.SigApp

namespace Effect4.Program

open Effect4 Effect4.Store

/-! ## The signature at an address, as data -/

/-- Which part of a whole program an address is in, as data. -/
inductive PartSig where
  /-- the application's signature with the hole table -/
  | root
  /-- a block's main program or its module layers: the block's signature -/
  | block (decls : List DefDecl)
  /-- a block's body: the block's signature with the body's parameters -/
  | body (decls : List DefDecl) (params : List ParamDecl)
deriving DecidableEq, Repr

/-- The data that the signature at an address is derived from. -/
structure SigData where
  app : SigApp
  holes : RowTable
  part : PartSig
deriving DecidableEq

/-- The signature that the data spells. -/
def SigData.signature (d : SigData) : Signature NativeOp :=
  match d.part with
  | .root => (d.app.withHoles d.holes).signature
  | .block decls => (d.app.withHoles d.holes).signature.withDefs decls
  | .body decls ps => ((d.app.withHoles d.holes).signature.withDefs decls).withParams ps

/-- The index of the body that an address inside a block's bodies' spine names: each `1` steps
along the spine, and `0` enters the body. Path arithmetic only: no walk of the program. -/
def bodyIndex : List Nat → Option Nat
  | 0 :: _ => some 0
  | 1 :: rest => (bodyIndex rest).map (· + 1)
  | _ => none

/-- The part of an address, as data, read off the root's declarations and the path: a one-level
case analysis of the root (decisions row 143), no traversal. -/
def partSigAt (p : NativeEff) (path : List Nat) : PartSig :=
  match p, path with
  | .defs decls _ _ _, 0 :: rest =>
    match (bodyIndex rest).bind fun k => decls[k]? with
    | some d => .body decls d.params
    | none => .root
  | .defs decls _ _ _, 1 :: _ => .block decls
  | .defs decls _ _ (.cons _ _), 2 :: _ => .block decls
  | _, _ => .root

/-- The data at an address of a sketch. -/
def sketchSigData (s : Sketch) (app : SigApp) (path : List Nat) : SigData :=
  ⟨app, s.holes, partSigAt s.program path⟩

/-! ## The checker-verdict cache -/

namespace CheckCache

/-- A cache key: the program's content, the signature's data and the ordered environment. The
path is not part of it (`Checker.check_rebase`). -/
structure CheckKey where
  program : NativeEff
  sig : SigData
  env : TyEnv
deriving DecidableEq

/-- An entry: a key and the checker's verdict at the empty path. -/
structure Entry where
  key : CheckKey
  verdict : Except TypeRefusal EffTy
deriving DecidableEq

/-- Compute the checker's verdict for `key` at the empty path (`[]`). -/
def Entry.compute (key : CheckKey) : Entry :=
  ⟨key, Checker.check key.sig.signature key.env [] key.program⟩

/-- The rows of the data's sketch signature. -/
def _root_.Effect4.Program.SigData.allRows (d : SigData) : RowTable := d.app.rows ++ d.holes

/-- **A prefix extension, decided**: the same services, named types and part, and rows that
extend the old rows at their end. -/
def _root_.Effect4.Program.SigData.extendsB (a b : SigData) : Bool :=
  decide (a.app.services = b.app.services) && decide (a.app.types = b.app.types) &&
    decide (a.part = b.part) && a.allRows.isPrefixOf b.allRows

/-- **A lookup**: an exact hit answers its verdict, its refusal moved below the asked path; a
positive verdict at a prefix extension answers too; anything else is a miss. -/
def lookup (cache : List Entry) (key : CheckKey) (p : List Nat) :
    Option (Except TypeRefusal EffTy) :=
  match cache.find? (fun e => decide (e.key = key)) with
  | some e => some (e.verdict.mapError (fun (r : TypeRefusal) => (⟨p ++ r.path, r.reason⟩ : TypeRefusal)))
  | none =>
    match cache.find? (fun e => decide (e.key.program = key.program) &&
        decide (e.key.env = key.env) && e.key.sig.extendsB key.sig && e.verdict.toBool) with
    | some e => some e.verdict
    | none => none

/-- Insert a computed entry for `key` into `cache` if `key` is not already present. -/
def insert (cache : List Entry) (key : CheckKey) : List Entry :=
  if cache.any (fun e => decide (e.key = key)) then cache
  else Entry.compute key :: cache

/-! ## Bounded local candidate catalogue (`suggest`) -/

/-- The contextual evidence for a candidate at a target address and focus. -/
inductive Evidence where
  /-- The candidate types at the target's signature and environment with the focus's exact type (`ty`). -/
  | exactFit (ty : EffTy) (fromCache : Bool)
  /-- The candidate types at the target's signature and environment with a different type (`actual` vs `expected`). -/
  | typeMismatch (expected actual : EffTy) (fromCache : Bool)
  /-- The candidate is refused by the checker at the target's signature, environment and path. -/
  | refused (why : TypeRefusal) (fromCache : Bool)
  /-- The candidate comes from another lexical environment (`sourceEnv` vs `targetEnv`); moving it needs a scope shift (Slice F). -/
  | differentEnv (sourceEnv targetEnv : TyEnv)
deriving DecidableEq

/-- One candidate returned by `suggest`, with its source address (if local), its context key, and
its contextual evidence. -/
structure Suggestion where
  program : NativeEff
  sourcePath : Option (List Nat)
  key : CheckKey
  evidence : Evidence
deriving DecidableEq

/-- Evaluate one candidate `prog` (from `sourcePath` and `sourceEnv`) against a target focus
`(sig, targetEnv, expected)` at `targetPath`, updating `cache`. -/
def evaluateCandidate (cache : List Entry) (sig : SigData) (targetEnv : TyEnv) (expected : EffTy)
    (targetPath : List Nat) (sourcePath : Option (List Nat)) (sourceEnv : TyEnv)
    (prog : NativeEff) : List Entry × Suggestion :=
  let key : CheckKey := ⟨prog, sig, targetEnv⟩
  if decide (sourceEnv = targetEnv) then
    let (cache', verdict, fromCache) :=
      match lookup cache key targetPath with
      | some v => (cache, v, true)
      | none =>
        let e := Entry.compute key
        (e :: cache, e.verdict.mapError (fun (r : TypeRefusal) => (⟨targetPath ++ r.path, r.reason⟩ : TypeRefusal)), false)
    let ev : Evidence :=
      match verdict with
      | .ok ty =>
        if decide (ty = expected) then .exactFit ty fromCache
        else .typeMismatch expected ty fromCache
      | .error why => .refused why fromCache
    (cache', ⟨prog, sourcePath, key, ev⟩)
  else
    (cache, ⟨prog, sourcePath, key, .differentEnv sourceEnv targetEnv⟩)

/-- Evaluate a list of candidates `(sourcePath, sourceEnv, prog)` in order, threading `cache`. -/
def evaluateCandidates (cache : List Entry) (sig : SigData) (targetEnv : TyEnv) (expected : EffTy)
    (targetPath : List Nat) :
    List (Option (List Nat) × TyEnv × NativeEff) → List Entry × List Suggestion
  | [] => (cache, [])
  | (sp, sEnv, prog) :: rest =>
    let (cache1, sug) := evaluateCandidate cache sig targetEnv expected targetPath sp sEnv prog
    let (cache2, sugs) := evaluateCandidates cache1 sig targetEnv expected targetPath rest
    (cache2, sug :: sugs)

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
revision, target context, candidate suggestions, and updated cache. -/
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
  cache : List Entry

/-- **Bounded local candidate search (`suggest`)** at `path` of `d`, starting from `cursor` and
returning at most `limit` candidates, with `cache` updated. Returns `none` when `d.session.focusAt path`
has no typed focus. -/
def suggest (d : Doc) (cache : List Entry) (path : List Nat) (limit : Nat := 16)
    (cursor : Nat := 0) (supplied : List NativeEff := []) : Option SuggestResult :=
  match d.session.focusAt path with
  | none => none
  | some focus =>
    let sig := sketchSigData d.session.sketch d.session.app path
    let all := localCandidates d path focus supplied
    let total := all.length
    let page := (all.drop cursor).take limit
    let nextCursor := if cursor + limit < total then some (cursor + limit) else none
    let (cache', suggestions) := evaluateCandidates cache sig focus.env focus.ty path page
    some
      { doc := d.id
        revision := d.revision
        path := path
        cursor := cursor
        limit := limit
        total := total
        nextCursor := nextCursor
        sig := sig
        env := focus.env
        expected := focus.ty
        suggestions := suggestions
        cache := cache' }

end CheckCache

end Effect4.Program
