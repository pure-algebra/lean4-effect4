import ProbeView.Live

/-! The live step's stages, timed on the last request of a build. -/

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Retained Tools.View.Live

namespace Tools.View.StageBench
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let _ := size a
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000000)

def stages (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => pure ()
  | some reqs =>
  match reqs.getLast? with
  | none => pure ()
  | some r =>
    let st := (reqs.dropLast).foldl (fun st r => (step {} "t" st r).1) ({} : State)
    let ((tool, ans), tA) ← timed (fun _ => Tools.Session.answer st.tool r) (·.2.laws.length)
    match tool.session with
    | none => pure ()
    | some l =>
      let lit := if r.op == "open" then none else some r.path
      let (_, tL) ← timed (fun _ => Program.lines l.sketch.program) (·.length)
      let (_, tT) ← timed (fun _ => l.table.filterMap fun e => match e.result with
        | some (.ok t) => some (Tools.Code.effTyText t)
        | _ => none) (·.length)
      IO.println s!"{name}: lines fold {tL} ms, type texts {tT} ms"
      let (pg, tP) ← timed (fun _ => Program.sessionPage l lit "t" "" "" "") (·.lines.size)
      let holes := l.sketch.holes.map (·.name)
      let (code, tC) ← timed (fun _ => Program.codePanel l.sketch.program (l.app.withHoles l.sketch.holes).rows holes) fun c => (c.map (·.lines.size)).getD 0
      let pg := { pg with code }
      let (fl, tF1) ← timed (fun _ => Flow.ofProgram l.sketch.program) fun _ => 1
      let label (k : Key) : Option (String × String) := (pg.lines.toList.find? (·.key == k)).map fun l => (l.text, l.type)
      let (fl2, tF2) ← timed (fun _ => fl.relabel label) fun _ => 1
      let (laid, tF3) ← timed (fun _ => Flow.layout fl2) (·.placed.size)
      let pg := { pg with graph := some { title := "program", laid }, gutter := st.gutter, codeAt := st.codeAt }
      let ((cs, _), tK) ← timed (fun _ => Live.pageCalls {} 1280 pg st.cache) (·.1.length)
      let (sc, tS) ← timed (fun _ => Scene.of cs) (·.order.length)
      let (pt, tD) ← timed (fun _ => diff st.scene sc) (·.ops.length)
      let (rows, tR) ← timed (fun _ => patchRows 2 1 pt) (·.length)
      let _ := ans
      IO.println s!"{name} (last step, {pg.lines.size} lines, {laid.placed.size} placed): answer {tA}, page {tP}, code {tC}, flow fold {tF1}, relabel {tF2}, layout {tF3}, calls {tK}, scene {tS}, diff {tD}, rows {tR} ({rows.length} rows) ms"
end Tools.View.StageBench

open Tools.View.StageBench in
#eval show IO Unit from do
  stages "chain 12" (chain 12 0)
  stages "chain 18" (chain 18 0)
  stages "chain 24" (chain 24 0)
