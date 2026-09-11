import Effect4.Program.Native

/-! DI-11: a stream kernel uses external rows and existing Scope/Eff constructors.
`pullRow` carries Option (List α); the binding additionally checks nonempty Some chunks.
No stream constructor, queue store, Done error, host closure, or operator AST is introduced.
Source: vendor/effect-4.0.0-rc.112/src/Stream.ts, toPull;
Test/contracts/foundation-wave2.contract.md, T-09 / T-12 amendment. -/
set_option autoImplicit false
namespace Effect4.Program.Stream
open Effect4 Effect4.Machine

def openRow (target : String) : Row where
  name := "streamOpen"
  spelling := "Host.open"
  kind := .async
  registration := .external
  request := .nat
  answer := .handle target
  cite := "vendor/effect-4.0.0-rc.112/src/Stream.ts:19200-19225"

def pullRow (target : String) (elem error : Ty) : Row where
  name := "streamPull"
  spelling := "Host.pull"
  kind := .async
  registration := .external
  request := .handle target
  answer := .option (.list elem)
  error := error
  cite := "vendor/effect-4.0.0-rc.112/src/Stream.ts:19200-19225"

def closeRow (target : String) : Row where
  name := "streamClose"
  spelling := "Host.close"
  kind := .async
  registration := .external
  request := .handle target
  answer := .unit
  cite := "vendor/effect-4.0.0-rc.112/src/Scope.ts:545-567"

def table (target : String) (elem error : Ty) : RowTable :=
  [openRow target, pullRow target elem error, closeRow target]

/-- Refine the generic row value at the stream binding: a clean end or a nonempty chunk.
Failure is a separate completion category. Empty host batches must be skipped before here. -/
def chunk? : Val → Option (Option (List Val))
  | .none => some none
  | .some (.list (head :: tail)) => some (some (head :: tail))
  | _ => none

/-- A bounded sequence of pulls in an existing environment. Pairing the answers preserves
both chunk boundaries and the clean-end marker; it makes no flattening claim. -/
def pulls (handleIndex envSize : Nat) : Nat → NativeEff
  | 0 => .succeed (.lit .unit)
  | n + 1 => .bind (.callback (.external 1) (.var handleIndex))
      (.bind (pulls handleIndex (envSize + 1) n)
        (.succeed (.app "pair" (.cons (.var envSize) (.cons (.var (envSize + 1)) .nil)))))

/-- The open/pull/close kernel as ordinary scoped Eff composition. -/
def scopedPulls (source count : Nat) : NativeEff :=
  .scoped (.bind
    (.acquireRelease (.callback (.external 0) (.lit (.nat source)))
      (.callback (.external 2) (.var 0)))
    (pulls 0 1 count))

end Effect4.Program.Stream
