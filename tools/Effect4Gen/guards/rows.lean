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
-- The hygienic term row mints the current value's name. So a caller's variable keeps its
-- reading inside the binder term: the caller's `s` is the outer binder, at level 0.
#guard elaborate (bind "s" (Ref.make (nat 0))
    (Ref.modifyWith (var "s") fun current => app "pair" [var "s", current]))
  = .ok (.bind (.perform .refMake (.lit (.nat 0)))
          (.perform (.refModifyWith (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))) (.var 0)))
-- Red control: under the fixed name `s` the caller's `s` reads the cell's current value.
#guard elaborate (bind "s" (Ref.make (nat 0))
    (Ref.modify "s" (app "pair" [var "s", var "s"]) (var "s")))
  = .ok (.bind (.perform .refMake (.lit (.nat 0)))
          (.perform (.refModifyWith (.app "pair" (.cons (.var 1) (.cons (.var 1) .nil)))) (.var 0)))
-- Where no name clashes, the two wrappers emit one node.
#guard elaborate (Ref.updateWith (nat 0) fun current => app "succ" [current])
  = elaborate (Ref.update "a" (app "succ" [var "a"]) (nat 0))
-- An async row authors as the reader reads it: a `perform`, the one invocation form.
#guard elaborate (Effect.sleep (nat 5)) = .ok (.perform .sleep (.lit (.nat 5)))
-- `Deferred.make` takes its type arguments: the operation carries them (decisions row 42).
#guard elaborate (Deferred.make .nat .nat) = .ok (.perform (.deferredMakeOf .nat .nat) (.lit .unit))

end Effect4.Program.AuthoringRowsGuards
