import Effect4.Api.Author
import Effect4.Codegen.Read
import Effect4.Program.Packages

/-!
# Pedigree verifier probe (2026-09-30): what today's build guard admits, and how the authoring
# surface orders a link table

Finite checks (tested, not proved) on the tree's own definitions.

1. **The service guard is agreement-only.** The seat says `BuildRefusal.serviceCarrier` "acts as
   the freshness-or-agreement guard" (finding P8; its note §3.5 calls it "today's freshness
   guard"). `Api.Author.disagreeingService` (`src/Effect4/Api/Author.lean:45-50`) compares a
   declared carrier with `(nativeSignature table).serviceTy key`, so a fresh key (typed by
   nothing) is refused with `signature := none`, exactly like an override. It admits only
   declarations that agree with the built-in signature: no seventh carrier, fresh or not.
2. **A later `Package.install` prepends.** `Package.install ps m` sets
   `rows := rowsOf ps ++ m.rows` (`src/Effect4/Program/Authoring/Services.lean:186-187`), and
   `Module.table` is `m.rows ++ services' ops` (`src/Effect4/Program/Authoring.lean:322-326`).
   Installing a second package into a module that already has one inserts its rows in front,
   so the same source elaborates to different `Eff` indices, and the earlier `Eff` read against
   the new table is retyped: the insertion the seat's `RowExtensionRed.lean` shows, produced by
   the authoring surface itself. Installing both packages in one call, old one first, is an
   append and leaves the `Eff` unchanged.
3. **C6's shape, finitely.** `LawfulTable` of two disjoint lawful tables appended holds; a
   table appended to itself is refused (duplicate keys).
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Research.PedigreeVerify.Guards

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The build guard on service declarations -/

/-- A key whose type code (20) no built-in carrier spells: fresh for the built-in signature. -/
def freshSvc : ServiceDef := { key := ⟨⟨11⟩, ⟨20⟩⟩, carrier := .string }

/-- A key the built-in signature types at `nat` (type code 4), declared at `string`. -/
def overrideSvc : ServiceDef := { key := ⟨⟨10⟩, ⟨4⟩⟩, carrier := .string }

/-- The same key declared at the carrier the built-in signature gives it. -/
def agreeSvc : ServiceDef := { key := ⟨⟨10⟩, ⟨4⟩⟩, carrier := .nat }

def withSvc (s : ServiceDef) : Module NativeOp := { services := [s], main := succeed (nat 0) }

def buildError (m : Module NativeOp) : Option Effect4.Api.BuildRefusal :=
  match Effect4.Api.Author.build m with
  | .error e => some e
  | .ok _ => none

-- A fresh key is refused, with no signature type: the guard is not a freshness guard.
#guard Effect4.Api.Author.disagreeingService (withSvc freshSvc) [] =
  some (.serviceCarrier freshSvc.key .string none)
#guard buildError (withSvc freshSvc) = some (.serviceCarrier freshSvc.key .string none)

-- An override is refused, citing the built-in type.
#guard Effect4.Api.Author.disagreeingService (withSvc overrideSvc) [] =
  some (.serviceCarrier overrideSvc.key .string (some .nat))
#guard buildError (withSvc overrideSvc) = some (.serviceCarrier overrideSvc.key .string (some .nat))

-- Only an agreeing declaration passes, and the module builds.
#guard Effect4.Api.Author.disagreeingService (withSvc agreeSvc) [] = none
#guard buildError (withSvc agreeSvc) = none

/-! ## 2. Package installation order -/

def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory
def sql : Package := Package.ofRows "sql" Packages.sqliteBun

/-- One source: make a store, read a key. Rows are called by spelling, never by position. -/
def mainSrc : Src NativeOp := eff do
  let store ← Row.call (kv.op "Kv.make") unit
  Row.call (kv.op "get") (app "pair" [store, str "greeting"])

/-- The module with the key-value package. -/
def m0 : Module NativeOp := Package.install [kv] { main := mainSrc }

/-- A later installation of a second package into that module. -/
def mLater : Module NativeOp := Package.install [sql] m0

/-- Both packages in one call, the old one first. -/
def mOnce : Module NativeOp := Package.install [kv, sql] { main := mainSrc }

def elabOf (m : Module NativeOp) : Option NativeEff := (elaborateModule m).toOption

def answerOf (table : RowTable) (p : NativeEff) : Option Ty :=
  (typeOf (nativeSignature table) p).map EffTy.answer

-- The later install puts the second package's rows in front: `get` moves.
#guard m0.rowNames.lookup "get" = some 1
#guard mLater.rowNames.lookup "get" = some (Packages.sqliteBun.length + 1)
#guard mOnce.rowNames.lookup "get" = some 1

-- The same source elaborates to a different tree after the later install, and to the same
-- tree when both packages are installed at once, old one first.
#guard elabOf m0 ≠ elabOf mLater
#guard elabOf m0 = elabOf mOnce

-- The earlier tree, read against the later table, no longer types as it did.
#guard (elabOf m0).bind (answerOf m0.table) = some (.option .string)
#guard (elabOf m0).bind (answerOf mLater.table) ≠ (elabOf m0).bind (answerOf m0.table)
-- Against the appended table it types as before.
#guard (elabOf m0).bind (answerOf mOnce.table) = (elabOf m0).bind (answerOf m0.table)

/-! ## 3. `LawfulTable` under append (C6's shape) -/

#guard LawfulTable Packages.keyValueStoreMemory
#guard LawfulTable Packages.sqliteBun
#guard LawfulTable (Packages.keyValueStoreMemory ++ Packages.sqliteBun)
#guard !LawfulTable (Packages.keyValueStoreMemory ++ Packages.keyValueStoreMemory)

end Research.PedigreeVerify.Guards
