/-! ## Acceptance guards for the generated row wrappers

Appended verbatim by `--append tools/Effect4Gen/guards/rows.lean` into
`src/Effect4/Program/Authoring/Rows.lean`. One row of each request shape, elaborated by name
against the tree written by level. -/

namespace Effect4.Program.AuthoringRowsGuards

open Effect4.Program Effect4.Program.Authoring

#guard elaborate (Ref.make (nat 0)) = .ok (.perform .refMake (.lit (.nat 0)))
#guard elaborate (Ref.set (var "r") (nat 1)) = .error ⟨[], .unbound "r"⟩
#guard elaborate (bind "r" (Ref.make (nat 0)) (Ref.set (var "r") (nat 1)))
  = .ok (.bind (.perform .refMake (.lit (.nat 0)))
          (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil)))))
#guard elaborate (Ref.update .incr (nat 0)) = .ok (.perform (.refUpdate .incr) (.lit (.nat 0)))
-- An async row is the reader's image: a `callback`, never a `perform` (`Read.lean` `rowAnswer`).
#guard elaborate (Effect.sleep (nat 5)) = .ok (.callback .sleep (.lit (.nat 5)))
#guard elaborate Deferred.make = .ok (.perform .deferredMake (.lit .unit))

end Effect4.Program.AuthoringRowsGuards
