import Effect4.Algebra.Universal

/-!
# Handler composition
-/

namespace Effect4

/-- Collapse an implementation in `Program T` through a handler for `T`. -/
def Handler.through [Monad M]
    (upper : Handler S (Program T)) (lower : Handler T M) : Handler S M where
  handle operation := interpret lower (upper.handle operation)

theorem interpret_through [Monad M] [LawfulMonad M]
    (upper : Handler S (Program T)) (lower : Handler T M)
    (program : Program S A) :
    interpret lower (interpret upper program) =
      interpret (upper.through lower) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      calc
        interpret lower (interpret upper (Program.vis operation next)) =
            interpret lower
              ((upper.handle operation).bind fun answer =>
                interpret upper (next answer)) := rfl
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret lower (interpret upper (next answer)) :=
            interpret_bind lower (upper.handle operation) _
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret (upper.through lower) (next answer) :=
            bind_congr fun answer => ih answer
        _ = interpret (upper.through lower) (Program.vis operation next) := rfl

theorem interpret_through_of_equations [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (upper : Handler S (Program T)) (lower : Handler T M)
    (program : Program S A) :
    interpret lower (interpret upper program) =
      interpret (upper.through lower) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      calc
        interpret lower (interpret upper (Program.vis operation next)) =
            interpret lower
              ((upper.handle operation).bind fun answer =>
                interpret upper (next answer)) := rfl
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret lower (interpret upper (next answer)) :=
            interpret_bind_of_equations leftUnit assoc lower
              (upper.handle operation) _
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret (upper.through lower) (next answer) :=
            bind_congr fun answer => ih answer
        _ = interpret (upper.through lower) (Program.vis operation next) := rfl

end Effect4
