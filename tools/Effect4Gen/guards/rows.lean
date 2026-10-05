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
-- A term row elaborates its binder term under the name of the cell's current value: at the
-- root that name is level 0, and under one binder it is level 1, above the outer name.
#guard elaborate (Ref.update "a" (app "succ" [var "a"]) (nat 0))
  = .ok (.perform (.refUpdateWith (.app "succ" (.cons (.var 0) .nil))) (.lit (.nat 0)))
#guard elaborate (bind "r" (Ref.make (nat 0))
    (Ref.modify "a" (app "pair" [var "a", app "add" [var "a", var "r"]]) (var "r")))
  = .ok (.bind (.perform .refMake (.lit (.nat 0)))
          (.perform (.refModifyWith (.app "pair" (.cons (.var 1)
            (.cons (.app "add" (.cons (.var 1) (.cons (.var 0) .nil))) .nil)))) (.var 0)))
-- The current value's name is the term's alone: the request does not see it.
#guard elaborate (Ref.update "a" (var "a") (var "a")) = .error ⟨[], .unbound "a"⟩
-- An async row authors as the reader reads it: a `perform`, the one invocation form.
#guard elaborate (Effect.sleep (nat 5)) = .ok (.perform .sleep (.lit (.nat 5)))
-- `Deferred.make` takes its type arguments: the operation carries them (decisions row 42).
#guard elaborate (Deferred.make .nat .nat) = .ok (.perform (.deferredMakeOf .nat .nat) (.lit .unit))

end Effect4.Program.AuthoringRowsGuards
