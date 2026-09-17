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

-- `select`: one lift per decision, the bound names first as every lift spells them; a name
-- bound after `o` is level 1 (variables are levels from the front of the environment)
#guard elaborate (selectOption "x" (var "o") (succeed (nat 0)) (succeed (var "x")) : Src NativeOp)
  = .error ⟨[], .unbound "o"⟩

#guard elaborate (bind "o" (succeed (nat 0)) (selectOption "x" (var "o") (succeed (nat 0)) (succeed (var "x"))) : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 0))) (.select (.var 0) .option (.succeed (.lit (.nat 0))) (.succeed (.var 1))))

#guard elaborate (bind "o" (succeed (nat 0)) (selectTag "p" "r" (var "o") "A" (succeed (var "p")) (succeed (var "r"))) : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 0))) (.select (.var 0) (.tag "A") (.succeed (.var 1)) (.succeed (.var 1))))

#guard elaborate (selectBool (bool true) (succeed (nat 1)) (succeed (nat 2)) : Src NativeOp)
  = .ok (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2))))

#guard elaborate (withFiber (Action.raceAll [succeed (nat 1), succeed (nat 2)]) : Src NativeOp)
  = .ok (.withFiber (.raceAll (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.lit (.nat 2))) .nil))))

end Effect4.Program.AuthoringGuards
