import Test.Program.RunAdmissionControls
import Effect4.Tool.Exchange

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Program.Check Effect4.Store Effect4.Tool Effect4.Tool.Exchange
open Test.Program.RunAdmissionControls (app sketch)

private def prepare : Nat → Cas → State → Option (Ref SessionEntry) → Option (Cas × State × Ref SessionEntry)
  | 0, c, s, some h => some (c, s, h)
  | 0, _, _, none => none
  | n + 1, c, s, parent => do
    let a := Action.open_ "bench" app sketch
    let served := (serve Oracle.uncached s (.act a)).value
    if !served.2.result.isOk then none else do
    let pub := match parent with
      | none => Publish.create "bench"
      | some h => Publish.advance "bench" ⟨h.digest, s.transcript.length⟩
    let txn ← publication zeroDigest c s a served.1 pub
    let (_, next) ← (c.commit txn).toOption
    let root ← next.store.root? (rootName "bench")
    prepare n next served.1 (some ⟨root.head.digest⟩)

private def measureSessionLoad (n : Nat) : IO Unit := do
  let some (cas, state, head) := prepare n Cas.empty empty none | throw (IO.userError "prepare refused")
  let before ← IO.monoNanosNow
  let loaded := (load Oracle.uncached cas head).value
  let observed := loaded.toOption.map (·.transcript.length)
  if observed != some state.transcript.length then throw (IO.userError "load differs")
  let elapsed := (← IO.monoNanosNow) - before
  IO.println s!"actions={n} nodes={cas.store.nodes.length} loaded={observed} load_ns={elapsed}"

#eval do
  measureSessionLoad 1
  measureSessionLoad 10
  measureSessionLoad 50
  measureSessionLoad 100
