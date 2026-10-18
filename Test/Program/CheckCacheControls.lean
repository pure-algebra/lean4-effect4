import Tools.Session
import Effect4.Laws.Program.Typing.CheckCache
import Effect4.Program.Scoped

/-!
# CheckCache and candidate catalogue controls (Slice C)

Acceptance controls for Slice C (`docs/research/2026-10-17-proof-scout/README.md` §7.3 and
`probes/C.lean`):

1. Case 3: the same bytes check differently at two row tables (C2's control), so their keys differ;
   `suggest` retrieves a same-context fragment (`exactFit`) and explains a signature-mismatched
   candidate (`refused`), carrying pagination bounds and document revision.
2. Finding C: an exact hit moves its refusal to `[8, 4]`.
3. Finding B: a positive verdict answers at the larger row table (`SigData.extendsB`); the refusal
   of a missing row is not reused there.
4. Control C3: a fragment that reads no outside variable (`closedAtRoot`) misses at another
   environment, and `partSigAt` distinguishes root, block, and body addresses.
-/

set_option autoImplicit false

namespace Test.Program.CheckCacheControls

open Effect4 Effect4.Program Effect4.Store
open Effect4.Program.CheckCache
open Tools.Session (answer)
open Tools.JsonBridge (toHex)

def rowsSmall : SigApp := { rows := [Program.Row.hole "n" .nat] }
def rowsLarge : SigApp := { rows := [Program.Row.hole "n" .nat, Program.Row.hole "s" .string] }
def call0 : NativeEff := .perform (.external 0) (.lit .unit)
def call1 : NativeEff := .perform (.external 1) (.lit .unit)
def natTy : EffTy := .pure .nat

def dataAt (app : SigApp) : SigData := ⟨app, [], .root⟩
def computed (program : NativeEff) (d : SigData) (env : TyEnv) : Entry :=
  Entry.compute ⟨program, d, env⟩

/-! ## Control 1: Case 3 — row table difference in keys, and `suggest` with contextual evidence -/

def natApp : SigApp := { rows := [Program.Row.hole "external" .nat] }
def strApp : SigApp := { rows := [Program.Row.hole "external" .string] }

#guard Checker.check (dataAt natApp).signature [] [] call0 !=
  Checker.check (dataAt strApp).signature [] [] call0
#guard !(dataAt natApp).extendsB (dataAt strApp)
#guard (⟨call0, dataAt natApp, []⟩ : CheckKey) != ⟨call0, dataAt strApp, []⟩

-- `suggest` on a document with a hole at `[1]` under a `.nat` binder:
-- `.succeed (.var 0)` is an exact fit, `call1` (missing row) is refused with its explanation,
-- and `.succeed (.lit (.nat 1))` at `[0]` (environment `[]` vs `[.nat]`) is marked `differentEnv`.
def suggestSketch : Sketch :=
  { program := .bind (.succeed (.lit (.nat 1))) (Sketch.hole {} 0),
    holes := [Program.Row.hole "h" .nat] }
def suggestDoc : Doc := Doc.open {} suggestSketch ⟨"suggest-doc", 0⟩
def suggestRes : Option SuggestResult :=
  suggest suggestDoc [] [1] 10 0 [call1]

#guard suggestRes.isSome
#guard (suggestRes.map (·.revision)) = some 0
#guard (suggestRes.map (·.cursor)) = some 0
#guard (suggestRes.map (·.limit)) = some 10
#guard (suggestRes.map (·.env)) = some [.nat]
#guard (suggestRes.map (·.expected)) = some natTy

-- Same-context fragment `.succeed (.var 0)` is `exactFit`:
#guard (suggestRes.map fun r =>
  r.suggestions.any fun s =>
    s.program == .succeed (.var 0) && s.evidence == .exactFit natTy false) = some true

-- Signature-mismatched candidate `call1` is `refused` at `[1]`:
#guard (suggestRes.map fun r =>
  r.suggestions.any fun s =>
    s.program == call1 && match s.evidence with
      | .refused why false => why.path == [1]
      | _ => false) = some true

-- Candidate at `[0]` has `differentEnv [] [.nat]`:
#guard (suggestRes.map fun r =>
  r.suggestions.any fun s =>
    s.sourcePath == some [0] && s.evidence == .differentEnv [] [.nat]) = some true

-- Second `suggest` call with the populated cache hits the cache (`fromCache = true`):
def suggestResCached : Option SuggestResult :=
  suggestRes.bind fun r1 => suggest suggestDoc r1.cache [1] 10 0 [call1]

#guard (suggestResCached.map fun r =>
  r.suggestions.any fun s =>
    s.program == .succeed (.var 0) && s.evidence == .exactFit natTy true) = some true

-- Session tool `suggest` returns bounds, revision, and suggestions.
#guard
  let r0 := answer {}
    { op := "open", program := some (toHex suggestSketch.program),
      holes := some (toHex suggestSketch.holes) }
  let r1 := answer r0.1
    { op := "suggest", path := [1], limit := 2, cursor := 0,
      candidates := some (toHex [call1]) }
  r1.2.ok &&
    r1.2.result.getObjValAs? Nat "revision" == .ok 0 &&
    (r1.2.result.getObjValD "bounds").getObjValAs? Nat "limit" == .ok 2 &&
    !r1.1.cache.isEmpty

/-! ## Control 2: Finding C — an exact hit moves its refusal to `[8, 4]` -/

def badVar : NativeEff := .bind (.succeed (.lit (.nat 1))) (.succeed (.var 42))
def cache1 : List Entry := [computed badVar (dataAt rowsSmall) []]

#guard lookup cache1 ⟨badVar, dataAt rowsSmall, []⟩ [8, 4] =
  some (Checker.check rowsSmall.signature [] [8, 4] badVar)
#guard lookup cache1 ⟨badVar, dataAt rowsSmall, []⟩ [8, 4] !=
  some (Checker.check rowsSmall.signature [] [] badVar)

/-! ## Control 3: Finding B — positive verdict answers at a prefix extension; refusal does not -/

#guard (dataAt rowsSmall).extendsB (dataAt rowsLarge)
#guard !(dataAt rowsLarge).extendsB (dataAt rowsSmall)

def cache2 : List Entry := [computed call0 (dataAt rowsSmall) []]
#guard lookup cache2 ⟨call0, dataAt rowsLarge, []⟩ [3] = some (.ok natTy)

def cache3 : List Entry := [computed call1 (dataAt rowsSmall) []]
#guard (Checker.check rowsSmall.signature [] [] call1).toOption.isNone
#guard (Checker.check rowsLarge.signature [] [] call1).toOption = some (.pure .string)
#guard lookup cache3 ⟨call1, dataAt rowsLarge, []⟩ [] = none

/-! ## Control 4: Control C3 — closed fragment misses at another environment, and `partSigAt` -/

def closedAtRoot : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
#guard closedAtRoot.scopedAt 0
#guard Checker.check (dataAt {}).signature [] [] closedAtRoot = .ok natTy
#guard Checker.check (dataAt {}).signature [.string] [] closedAtRoot = .ok (.pure .string)

def cache4 : List Entry := [computed closedAtRoot (dataAt {}) []]
#guard lookup cache4 ⟨closedAtRoot, dataAt {}, [.string]⟩ [] = none
#guard Checker.check (dataAt {}).signature [.string] [] (Eff.weaken 0 closedAtRoot) = .ok natTy

def fDecl : DefDecl := { name := "f", request := .unit, answer := .nat }
def blockSketch : Sketch :=
  { program := .defs [fDecl] (.cons (.succeed (.lit (.nat 1))) .nil) (.succeed (.lit (.nat 2))) .nil }
#guard partSigAt blockSketch.program [0, 0] = .body [fDecl] []
#guard partSigAt blockSketch.program [0, 1, 0] = .root
#guard partSigAt blockSketch.program [1] = .block [fDecl]
#guard partSigAt blockSketch.program [] = .root

end Test.Program.CheckCacheControls
