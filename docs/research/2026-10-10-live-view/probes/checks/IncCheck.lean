import ProbeView.Inc

/-! The folds along an edit equal the fresh folds, at every step of every build. -/

open Effect4 Effect4.Program Tools.View Tools.View.Build

namespace Tools.View.IncCheck
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))
def forksInOrder : Nat → Nat → Nat → NativeEff
  | 0, L, k => awaits k 0 L
  | n + 1, L, k =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (forksInOrder n (L + 1) k)
where
  awaits : Nat → Nat → Nat → NativeEff
    | 0, _, _ => .succeed (.lit .unit)
    | j + 1, i, L => .bind (.awaitFiber (.var i) .awaitValue) (awaits j (i + 1) (L + 1))

def programs : List (String × NativeEff) :=
  Effect4.Program.Wire.Corpus.all ++ [("chain 6", chain 6 0), ("forksInOrder 4", forksInOrder 4 0 4)]

def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)

/-- At every step of a build: the incremental lines, waits and flow against the fresh ones. -/
def agrees (p : NativeEff) : Bool :=
  match requests p with
  | none => false
  | some reqs =>
    (reqs.foldl (fun (acc : Bool × Tools.Session.State × Inc.Memo) r =>
      let (ok, st, memo) := acc
      let (st', _) := Tools.Session.answer st r
      match st'.session with
      | none => (ok, st', memo)
      | some l =>
        let prog := l.sketch.program
        let edited := if r.op == "fill" || r.op == "omit" then some r.path else none
        let ls := Inc.lines memo edited prog
        let ws := Inc.waits memo edited prog
        let fl := Inc.flow memo edited prog ws
        (ok && ls.map (fun n => (n.path, n.depth, n.text)) == (Program.lines prog).map (fun n => (n.path, n.depth, n.text)) &&
          sameSet ws (Flow.waits prog) && fl == Flow.ofProgram prog,
          st', Inc.Memo.next ls ws)) (true, {}, {})).1

#guard programs.all fun (_, p) => agrees p

end Tools.View.IncCheck
