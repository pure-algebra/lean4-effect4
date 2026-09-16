/-! ## Acceptance guards for the generated authoring lifts

Appended verbatim by `--append tools/Effect4Gen/guards/authoring.lean` into
`src/Effect4/Program/Authoring/Lifts.lean`. One constructor of each binding shape, elaborated
by name and compared with the tree written by level; the full battery is
`Test/Program/AuthoringContract.lean`. -/

namespace Effect4.Program.AuthoringGuards

open Effect4.Program Effect4.Program.Authoring

#guard elaborate (bind "r" (succeed (nat 0)) (succeed (var "r")) : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 0))) (.succeed (.var 0)))

#guard elaborate (bind "r" (succeed (nat 0)) (succeed (var "q")) : Src NativeOp)
  = .error ⟨[1], .unbound "q"⟩

#guard elaborate (acquireRelease "a" "x" (succeed (nat 0)) (succeed (app "pair" [var "a", var "x"])) : Src NativeOp)
  = .ok (.acquireRelease (.succeed (.lit (.nat 0)))
          (.succeed (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))))

#guard elaborate (provideLayer (Layer.effectDiscard (succeed (var "r"))) false (succeed (nat 1)) : Src NativeOp)
  = .error ⟨[0, 0], .unbound "r"⟩

#guard elaborate (withFiber (Action.raceAll [succeed (nat 1), succeed (nat 2)]) : Src NativeOp)
  = .ok (.withFiber (.raceAll (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.lit (.nat 2))) .nil))))

end Effect4.Program.AuthoringGuards
