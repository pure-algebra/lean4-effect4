import Effects.Coalgebra.Bisim
import Effects.Lens

/-!
# Comodels: hosts

A comodel of a signature `S` is a host. From a state of its own, it answers each operation and
gives the next state, or gives `none` where it does not answer. Running a program against a host
(`Comodel.run`) is interpreting it in the state monad over `Option`: a comodel's `handler` is a
`Handler S (StateT σ Option)`, and `ofHandler` is the way back.

Hosts compose, each construction with one law about `run`:

* `route`: hosts for `S` and `T`, over their own states, make one host for `S ⊕ₛ T` over the
  product of the states (`run_route_inl`, `run_route_inr`);
* `share`: hosts for `S` and `T` over one state make one host for `S ⊕ₛ T` (`run_share_inl`,
  `run_share_inr`);
* `rename`: a host for `T` and a lens from `S` to `T` make a host for `S` (`run_rename`);
* `through`: a handler that implements `S` by programs over `T` and a host for `T` make a host for
  `S` (`run_through`). Program in, program out: the handler translates, the host answers;
* `guard`: a host that refuses the answers a test rejects (reply admission);
* `replies` and `record`: a host that answers from a list of replies (a reply tape), and a host
  that writes the replies it gives. What a recording host wrote, the reply host replays
  (`run_record_replies`).

`run_approx` reads the approximation order: an approximant that finishes against a host, finishes
the same way as what it approximates. `Effects.Coalgebra.Run` uses it to run systems.
-/

namespace Effects

universe uOp uAns uT

/-- **A comodel of `S`, a host**: from a state, an answer to each operation and the next state, or
`none` where it does not answer. -/
structure Comodel (S : Signature.{uOp, uAns}) (σ : Type uAns) where
  answer : (operation : S.Op) → σ → Option (S.Answer operation × σ)

namespace Comodel

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}} {σ τ : Type uAns}
  {A : Type uAns}

/-- The host as a handler into the state monad over `Option`. -/
def handler (host : Comodel S σ) : Handler S (StateT σ Option) where
  handle operation := fun state => host.answer operation state

/-- A handler into the state monad over `Option` as a host: the two are one thing. -/
def ofHandler (handler : Handler S (StateT σ Option)) : Comodel S σ where
  answer operation state := (handler.handle operation).run state

theorem handler_ofHandler (handler : Handler S (StateT σ Option)) :
    (ofHandler handler).handler = handler := rfl

theorem ofHandler_handler (host : Comodel S σ) : ofHandler host.handler = host := rfl

/-- **Run a program against a host**, from a state: the result and the final state, or `none`
where the host does not answer. -/
def run (host : Comodel S σ) (program : Program S A) (state : σ) : Option (A × σ) :=
  (interpret host.handler program).run state

/-- Running the host of a handler is interpreting by the handler. -/
theorem run_ofHandler (handler : Handler S (StateT σ Option)) (program : Program S A)
    (state : σ) : (ofHandler handler).run program state = (interpret handler program).run state :=
  rfl

theorem run_pure (host : Comodel S σ) (value : A) (state : σ) :
    host.run (.pure value) state = some (value, state) := rfl

theorem run_vis_none (host : Comodel S σ) {operation : S.Op}
    (next : S.Answer operation → Program S A) {state : σ}
    (h : host.answer operation state = none) : host.run (.vis operation next) state = none := by
  show (host.answer operation state).bind _ = none
  rw [h]
  rfl

theorem run_vis_some (host : Comodel S σ) {operation : S.Op}
    (next : S.Answer operation → Program S A) {state state' : σ} {answer : S.Answer operation}
    (h : host.answer operation state = some (answer, state')) :
    host.run (.vis operation next) state = host.run (next answer) state' := by
  show (host.answer operation state).bind _ = _
  rw [h]
  rfl

/-- Running a sequence is running its first part, then the rest from where it ended. -/
theorem run_bind {B : Type uAns} (host : Comodel S σ) (program : Program S A)
    (next : A → Program S B) (state : σ) :
    host.run (program.bind next) state =
      (host.run program state).bind fun result => host.run (next result.1) result.2 := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation rest ih =>
    rcases h : host.answer operation state with _ | ⟨answer, state'⟩
    · rw [show (Program.vis operation rest).bind next =
          .vis operation (fun answer => (rest answer).bind next) from rfl,
        run_vis_none host _ h, run_vis_none host _ h]
      rfl
    · rw [show (Program.vis operation rest).bind next =
          .vis operation (fun answer => (rest answer).bind next) from rfl,
        run_vis_some host _ h, run_vis_some host _ h, ih]

/-- A program read as an unfolding that is never cut runs as the program does. -/
theorem run_uncut (host : Comodel S σ) (program : Program S A) (state : σ) :
    host.run program.uncut state =
      (host.run program state).map fun result => (some result.1, result.2) := by
  rw [Program.uncut, run_bind]
  cases host.run program state with
  | none => rfl
  | some result => rfl

/-- **An approximant that finishes against a host finishes the same way as what it
approximates.** -/
theorem run_approx (host : Comodel S σ) {p q : Program S (Option A)} (h : Program.Approx p q)
    {state state' : σ} {value : A} (hp : host.run p state = some (some value, state')) :
    host.run q state = some (some value, state') := by
  induction h generalizing state with
  | cut _ =>
    rw [run_pure] at hp
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at hp
  | done _ => exact hp
  | vis operation _ ih =>
    rcases ha : host.answer operation state with _ | ⟨answer, state1⟩
    · rw [run_vis_none host _ ha] at hp
      simp only [reduceCtorEq] at hp
    · rw [run_vis_some host _ ha] at hp ⊢
      exact ih answer hp

/-! ## Routing: two hosts for a sum of signatures -/

/-- Route each side of a sum to its own host, over the product of their states. -/
def route (left : Comodel S σ) (right : Comodel T τ) : Comodel (S ⊕ₛ T) (σ × τ) where
  answer
    | .inl operation, state =>
      (left.answer operation state.1).map fun result => (result.1, (result.2, state.2))
    | .inr operation, state =>
      (right.answer operation state.2).map fun result => (result.1, (state.1, result.2))

theorem run_route_inl (left : Comodel S σ) (right : Comodel T τ) (program : Program S A)
    (state : σ) (other : τ) :
    (left.route right).run (Program.inl (T := T) program) (state, other) =
      (left.run program state).map fun result => (result.1, (result.2, other)) := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation next ih =>
    rcases h : left.answer operation state with _ | ⟨answer, state'⟩
    · have h' : (left.route right).answer (.inl operation) (state, other) = none := by
        simp only [route, h, Option.map_none]
      rw [show Program.inl (T := T) (Program.vis operation next) =
          .vis (.inl operation) (fun answer => Program.inl (T := T) (next answer)) from rfl,
        run_vis_none _ _ h', run_vis_none left _ h]
      rfl
    · have h' : (left.route right).answer (.inl operation) (state, other) =
          some (answer, (state', other)) := by
        show (left.answer operation state).map _ = _
        rw [h]
        rfl
      rw [show Program.inl (T := T) (Program.vis operation next) =
          .vis (.inl operation) (fun answer => Program.inl (T := T) (next answer)) from rfl,
        run_vis_some _ _ h', run_vis_some left _ h, ih]

theorem run_route_inr (left : Comodel S σ) (right : Comodel T τ) (program : Program T A)
    (other : σ) (state : τ) :
    (left.route right).run (Program.inr (S := S) program) (other, state) =
      (right.run program state).map fun result => (result.1, (other, result.2)) := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation next ih =>
    rcases h : right.answer operation state with _ | ⟨answer, state'⟩
    · have h' : (left.route right).answer (.inr operation) (other, state) = none := by
        simp only [route, h, Option.map_none]
      rw [show Program.inr (S := S) (Program.vis operation next) =
          .vis (.inr operation) (fun answer => Program.inr (S := S) (next answer)) from rfl,
        run_vis_none _ _ h', run_vis_none right _ h]
      rfl
    · have h' : (left.route right).answer (.inr operation) (other, state) =
          some (answer, (other, state')) := by
        show (right.answer operation state).map _ = _
        rw [h]
        rfl
      rw [show Program.inr (S := S) (Program.vis operation next) =
          .vis (.inr operation) (fun answer => Program.inr (S := S) (next answer)) from rfl,
        run_vis_some _ _ h', run_vis_some right _ h, ih]

/-- Two hosts over one state, one for each side of a sum. -/
def share (left : Comodel S σ) (right : Comodel T σ) : Comodel (S ⊕ₛ T) σ where
  answer
    | .inl operation => left.answer operation
    | .inr operation => right.answer operation

theorem run_share_inl (left : Comodel S σ) (right : Comodel T σ) (program : Program S A)
    (state : σ) : (left.share right).run (Program.inl (T := T) program) state =
      left.run program state := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation next ih =>
    rcases h : left.answer operation state with _ | ⟨answer, state'⟩
    · rw [show Program.inl (T := T) (Program.vis operation next) =
          .vis (.inl operation) (fun answer => Program.inl (T := T) (next answer)) from rfl,
        run_vis_none (left.share right) _
          ((show (left.share right).answer (.inl operation) state = left.answer operation state
            from rfl).trans h),
        run_vis_none left _ h]
    · rw [show Program.inl (T := T) (Program.vis operation next) =
          .vis (.inl operation) (fun answer => Program.inl (T := T) (next answer)) from rfl,
        run_vis_some (left.share right) _
          ((show (left.share right).answer (.inl operation) state = left.answer operation state
            from rfl).trans h),
        run_vis_some left _ h, ih]

theorem run_share_inr (left : Comodel S σ) (right : Comodel T σ) (program : Program T A)
    (state : σ) : (left.share right).run (Program.inr (S := S) program) state =
      right.run program state := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation next ih =>
    rcases h : right.answer operation state with _ | ⟨answer, state'⟩
    · rw [show Program.inr (S := S) (Program.vis operation next) =
          .vis (.inr operation) (fun answer => Program.inr (S := S) (next answer)) from rfl,
        run_vis_none (left.share right) _
          ((show (left.share right).answer (.inr operation) state = right.answer operation state
            from rfl).trans h),
        run_vis_none right _ h]
    · rw [show Program.inr (S := S) (Program.vis operation next) =
          .vis (.inr operation) (fun answer => Program.inr (S := S) (next answer)) from rfl,
        run_vis_some (left.share right) _
          ((show (left.share right).answer (.inr operation) state = right.answer operation state
            from rfl).trans h),
        run_vis_some right _ h, ih]

/-! ## Renaming and implementation -/

/-- A host for `T`, renamed along a lens from `S`: each operation is answered as its image,
and the answer pulled back. -/
def rename (f : Signature.Hom S T) (host : Comodel T σ) : Comodel S σ where
  answer operation state :=
    (host.answer (f.op operation) state).map fun result => (f.back operation result.1, result.2)

theorem run_rename (f : Signature.Hom S T) (host : Comodel T σ) (program : Program S A)
    (state : σ) : (host.rename f).run program state = host.run (program.map f) state := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation next ih =>
    rcases h : host.answer (f.op operation) state with _ | ⟨answer, state'⟩
    · have h' : (host.rename f).answer operation state = none := by
        simp only [rename, h, Option.map_none]
      rw [run_vis_none _ _ h',
        show (Program.vis operation next).map f =
          .vis (f.op operation) (fun answer => (next (f.back operation answer)).map f) from rfl,
        run_vis_none host _ h]
    · have h' : (host.rename f).answer operation state =
          some (f.back operation answer, state') := by
        simp only [rename, h, Option.map_some]
      rw [run_vis_some _ _ h', ih,
        show (Program.vis operation next).map f =
          .vis (f.op operation) (fun answer => (next (f.back operation answer)).map f) from rfl,
        run_vis_some host _ h]

/-- **Program in, program out.** A handler that implements each operation of `S` by a program
over `T`, and a host for `T`, make a host for `S`: an operation is answered by running its
implementation against the host. -/
def through (impl : Handler S (Program T)) (host : Comodel T σ) : Comodel S σ where
  answer operation state := host.run (impl.handle operation) state

/-- Running through an implementation is running the translated program against the host. -/
theorem run_through (impl : Handler S (Program T)) (host : Comodel T σ) (program : Program S A)
    (state : σ) : (host.through impl).run program state =
      host.run (interpret impl program) state := by
  induction program generalizing state with
  | pure value => rfl
  | vis operation next ih =>
    rw [interpret_vis, show (impl.handle operation >>= fun answer => interpret impl (next answer)) =
        (impl.handle operation).bind (fun answer => interpret impl (next answer)) from rfl,
      run_bind]
    rcases h : host.run (impl.handle operation) state with _ | ⟨answer, state'⟩
    · exact run_vis_none (host.through impl) _ h
    · rw [run_vis_some (host.through impl) _ h, ih]
      rfl

/-! ## Admission, replies and recording -/

/-- A host that refuses every answer `admit` rejects: reply admission as a host transformer. -/
def guard (admit : (operation : S.Op) → S.Answer operation → Bool) (host : Comodel S σ) :
    Comodel S σ where
  answer operation state := (host.answer operation state).filter fun result => admit operation result.1

/-- A host that answers from a list of replies, decoding each at the operation it answers: the
reply tape. An empty list, or a reply that does not decode, is no answer. -/
def replies {R : Type uAns} (decode : (operation : S.Op) → R → Option (S.Answer operation)) :
    Comodel S (List R) where
  answer operation
    | [] => none
    | reply :: rest => (decode operation reply).map fun answer => (answer, rest)

/-- A host that writes each answer it gives, encoded, after the replies already written. -/
def record {R : Type uAns} (encode : (operation : S.Op) → S.Answer operation → R)
    (host : Comodel S σ) : Comodel S (σ × List R) where
  answer operation state :=
    (host.answer operation state.1).map fun result =>
      (result.1, (result.2, state.2 ++ [encode operation result.1]))

/-- **What a recording host wrote, the reply host replays.** When encoding then decoding gives
back every answer, a run against the recording host that ends with the written list
`written ++ recorded` is, against the reply host from `recorded ++ rest`, the same result with
`rest` left. The transcript helper of the host-as-handler theorem. -/
theorem run_record_replies {R : Type uAns} (decode : (operation : S.Op) → R → Option (S.Answer operation))
    (encode : (operation : S.Op) → S.Answer operation → R)
    (round : ∀ operation answer, decode operation (encode operation answer) = some answer)
    (host : Comodel S σ) : ∀ (program : Program S A) (state : σ) (written : List R) {value : A}
      {state' : σ} {out : List R},
      (host.record encode).run program (state, written) = some (value, (state', out)) →
      ∃ recorded, out = written ++ recorded ∧
        ∀ rest, (replies decode).run program (recorded ++ rest) = some (value, rest)
  | .pure _, _, written, _, _, _, h => by
    rw [run_pure] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨[], (List.append_nil _).symm, fun rest => rfl⟩
  | .vis operation next, state, written, _, _, _, h => by
    rcases ha : host.answer operation state with _ | ⟨answer, state1⟩
    · have h' : (host.record encode).answer operation (state, written) = none := by
        simp only [record, ha, Option.map_none]
      rw [run_vis_none _ _ h'] at h
      simp only [reduceCtorEq] at h
    · have h' : (host.record encode).answer operation (state, written) =
          some (answer, (state1, written ++ [encode operation answer])) := by
        simp only [record, ha, Option.map_some]
      rw [run_vis_some _ _ h'] at h
      obtain ⟨recorded, hout, hreplay⟩ :=
        run_record_replies decode encode round host (next answer) state1 _ h
      refine ⟨encode operation answer :: recorded, ?_, fun rest => ?_⟩
      · rw [hout, List.append_assoc]
        rfl
      · have hr : (replies decode).answer operation
            (encode operation answer :: (recorded ++ rest)) = some (answer, recorded ++ rest) := by
          simp only [replies, round, Option.map_some]
        rw [List.cons_append, run_vis_some _ _ hr]
        exact hreplay rest

end Comodel

end Effects
