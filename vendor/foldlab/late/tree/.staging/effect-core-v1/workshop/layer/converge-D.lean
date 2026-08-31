import Cas
import Cas.Backend.Universal
open Cas.Lang

/-! CONVERGENCE PROBE (position D, convergence round).
    Question under test: does the SYNTHESIS carrier
      Layer := Prog LayerSig (Handler SvcSig (Prog LayerSig))
    at ONE service signature (E's move), with B's content-address memo
    fold living INSIDE the Prog build prefix, actually
      (1) elaborate,
      (2) give one acquisition for a shared diamond where the layer
          COMBINATOR gives two (so the memo does real work and no
          binder arm on SystemNode is needed),
      (3) carry composition by through_assoc + a liftL lemma,
      (4) support residual soundness as a Prop, not a Sig equation. -/

/-! ## 0. ONE service signature. No Sig computed from content. -/
abbrev SvcKey := String
inductive SvcE where | ask (key : SvcKey)
  deriving DecidableEq
abbrev SvcE.Ans : SvcE → Type | .ask _ => Nat
abbrev SvcSig : Sig := ⟨SvcE, SvcE.Ans⟩

inductive ScopeE where
  | acquire (tag : Nat)
  | ensuringExit (body onOk onErr : Nat)
abbrev ScopeE.Ans : ScopeE → Type
  | .acquire _ => Nat
  | .ensuringExit _ _ _ => Nat
abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

abbrev LayerSig : Sig := SvcSig ⊕ₛ ScopeSig
abbrev LHandler := Handler SvcSig (Prog LayerSig)

/-- THE CARRIER. A/D's build prefix over E's uniform signature. -/
abbrev Layer := Prog LayerSig LHandler

def injSvc : LHandler where
  handle op := Prog.op (S := LayerSig) (Sum.inl op)
def scopePass : Handler ScopeSig (Prog LayerSig) where
  handle op := Prog.op (S := LayerSig) (Sum.inr op)
def liftL (u : LHandler) : Handler LayerSig (Prog LayerSig) := Handler.sum u scopePass

def leafH (k : SvcKey) (body : Prog LayerSig Nat) : LHandler where
  handle | .ask k' => if k' = k then body else Prog.op (S := LayerSig) (Sum.inl (SvcE.ask k'))

/-- Merge OVERLAPS at one signature, so it takes the provides-set. -/
def mergeK (keys : List SvcKey) (l r : LHandler) : LHandler where
  handle | .ask k => if keys.contains k then l.handle (.ask k) else r.handle (.ask k)

/-! ## 1. COMBINATORS -/
def Layer.empty : Layer := pure injSvc
def Layer.ofHandler (h : LHandler) : Layer := pure h
def Layer.provide (L : Layer) {A : Type} (p : Prog LayerSig A) : Prog LayerSig A :=
  L >>= fun h => interpret (liftL h) p
def Layer.andThen (L M : Layer) : Layer :=
  M >>= fun g => interpret (liftL g) L >>= fun h => pure (Handler.through h (liftL g))
def Layer.merge (keys : List SvcKey) (L R : Layer) : Layer :=
  L >>= fun h => R >>= fun g => pure (mergeK keys h g)

/-! ## 2. liftL's two lemmas — E's, re-proved here. -/
theorem liftL_injSvc : liftL injSvc = idHandler (S := LayerSig) :=
  Handler.ext fun op => by cases op <;> rfl

theorem liftL_through (t u : LHandler) :
    liftL (Handler.through t (liftL u)) = Handler.through (liftL t) (liftL u) :=
  Handler.ext fun op => by
    cases op with
    | inl o => rfl
    | inr o =>
      show Prog.op (S := LayerSig) (Sum.inr o)
         = interpret (liftL u) (Prog.op (S := LayerSig) (Sum.inr o))
      show _ = interpret (liftL u) (Prog.vis (Sum.inr o) Prog.pure)
      simp [interpret, Handler.sum, scopePass, liftL, Prog.op, Prog.bind]

/-! ## 3. THE CONTENT PLANE — a first-order DAG, addressed children.
    (Model of Cas.Schema.SystemNode; nodes reached by address.) -/
abbrev NodeAddr := Nat
inductive LDesc where
  | empty
  | leafAcq (key : SvcKey) (tag : Nat)
  | merge   (l r : NodeAddr)
  | provide (inner outer : NodeAddr)
  | freshN  (inner : NodeAddr)
abbrev Table := NodeAddr → Option LDesc

/-- Residual calculus: PURE, outside Prog (R14a). EmitLayer.residualOf's shape. -/
def provides : Nat → Table → NodeAddr → List SvcKey
  | 0, _, _ => []
  | f+1, t, a => match t a with
    | none => []
    | some .empty => []
    | some (.leafAcq k _) => [k]
    | some (.merge l r) => provides f t l ++ provides f t r
    | some (.provide _ o) => provides f t o
    | some (.freshN i) => provides f t i

/-! ## 4. THE BRIDGE — B's memo fold, keyed by CONTENT ADDRESS, living
    INSIDE the Prog build prefix. This is the whole synthesis. -/
abbrev Memo := List (NodeAddr × LHandler)
def memoFind? : Memo → NodeAddr → Option LHandler
  | [], _ => none
  | (a, h) :: t, b => if a = b then some h else memoFind? t b

def denote : Nat → Table → Memo → NodeAddr → Prog LayerSig (Memo × LHandler)
  | 0, _, m, _ => pure (m, injSvc)
  | f+1, t, m, a =>
    match memoFind? m a with
    | some h => pure (m, h)                                  -- SHARING: one visit per address
    | none => match t a with
      | none => pure (m, injSvc)
      | some .empty => pure ((a, injSvc) :: m, injSvc)
      | some (.leafAcq k tag) =>
          Prog.op (S := LayerSig) (Sum.inr (ScopeE.acquire tag)) >>= fun i =>
            let h := leafH k (pure i)
            pure ((a, h) :: m, h)
      | some (.merge l r) =>
          denote f t m l >>= fun p =>
          denote f t p.1 r >>= fun q =>
            let h := mergeK (provides f t l) p.2 q.2
            pure ((a, h) :: q.1, h)
      | some (.provide i o) =>
          denote f t m i >>= fun p =>
          denote f t p.1 o >>= fun q =>
            let h := Handler.through q.2 (liftL p.2)
            pure ((a, h) :: q.1, h)
      | some (.freshN i) =>
          denote f t [] i >>= fun p =>                       -- EMPTY memo, NOT recorded: B's fresh
            pure (m, p.2)

/-- The same fold with the memo defeated — the separating control. -/
def denoteNoMemo : Nat → Table → NodeAddr → Prog LayerSig LHandler
  | 0, _, _ => pure injSvc
  | f+1, t, a => match t a with
    | none => pure injSvc
    | some .empty => pure injSvc
    | some (.leafAcq k tag) =>
        Prog.op (S := LayerSig) (Sum.inr (ScopeE.acquire tag)) >>= fun i => pure (leafH k (pure i))
    | some (.merge l r) =>
        denoteNoMemo f t l >>= fun hl => denoteNoMemo f t r >>= fun hr =>
          pure (mergeK (provides f t l) hl hr)
    | some (.provide i o) =>
        denoteNoMemo f t i >>= fun hi => denoteNoMemo f t o >>= fun ho =>
          pure (Handler.through ho (liftL hi))
    | some (.freshN i) => denoteNoMemo f t i

def layerOf (f : Nat) (t : Table) (a : NodeAddr) : Layer :=
  denote f t [] a >>= fun p => pure p.2

/-! ## 5. THE OBSERVATION — acquisitions, traced. -/
abbrev Obs := StateM (List Nat)
def obsH : Handler LayerSig Obs where
  handle
    | .inl (.ask _) => (fun s => (0, s) : Obs Nat)
    | .inr (.acquire tag) => (fun s => (tag, s ++ [tag]) : Obs Nat)
    | .inr (.ensuringExit b _ _) => (fun s => (b, s) : Obs Nat)

def buildTrace (L : Layer) : List Nat := (interpret obsH L []).2

/-! ## 6. THE WITNESS: a DIAMOND. Address 3 = merge(1,2);
    1 = provide(0, leafA); 2 = provide(0, leafB); 0 = the shared acquiring DB. -/
def tbl : Table
  | 0 => some (.leafAcq "Db" 100)
  | 1 => some (.leafAcq "A" 1)
  | 2 => some (.leafAcq "B" 2)
  | 3 => some (.merge 1 2)
  | 4 => some (.provide 0 3)      -- the diamond: Db provided to BOTH sides at once
  | 5 => some (.merge 0 0)        -- the same address twice
  | 6 => some (.freshN 0)
  | 7 => some (.merge 6 6)        -- fresh twice
  | _ => none

/-- SHARING: the same address twice acquires ONCE under the memo fold. -/
theorem shared_address_acquires_once : buildTrace (layerOf 8 tbl 5) = [100] := by rfl
/-- …and TWICE with the memo defeated. Non-vacuity. -/
theorem unmemoized_acquires_twice :
    (interpret obsH (denoteNoMemo 8 tbl 5) []).2 = [100, 100] := by rfl
/-- FRESHNESS is a property of the TRAVERSAL, not of the key (B, not E):
    `fresh` twice at ONE address acquires twice, with NO nonce anywhere. -/
theorem fresh_does_not_share : buildTrace (layerOf 8 tbl 7) = [100, 100] := by rfl
/-- The diamond builds its shared dependency once. -/
theorem diamond_shares : buildTrace (layerOf 8 tbl 4) = [100, 1, 2] := by rfl

/-- THE POINT AGAINST THE COMBINATOR: `Layer.merge L L` on the SAME
    layer VALUE still acquires twice. So the memo fold is doing work no
    layer combinator can do — and it does it with a Lean-level binder in
    `denote`, NOT with a `let`/`shared` ARM on the stored content. -/
theorem combinator_merge_acquires_twice :
    buildTrace (Layer.merge ["Db"] (layerOf 8 tbl 0) (layerOf 8 tbl 0)) = [100, 100] := by
  rfl
theorem memo_is_not_the_combinator :
    buildTrace (layerOf 8 tbl 5)
      ≠ buildTrace (Layer.merge ["Db"] (layerOf 8 tbl 0) (layerOf 8 tbl 0)) := by
  decide

/-! ## 7. RESIDUAL SOUNDNESS as a Prop — no Sig equation anywhere. -/
def Forwards (h : LHandler) (k : SvcKey) : Prop :=
  h.handle (.ask k) = Prog.op (S := LayerSig) (Sum.inl (SvcE.ask k))

/-- The shape of the owed theorem, at a witness: a key outside
    `provides` is forwarded by the built handler. -/
theorem residual_sound_at_a_witness :
    ∀ h, (interpret obsH (layerOf 8 tbl 4) []).1 = h → Forwards h "Zzz" := by
  intro h e; subst e; rfl

/-! ## 8. MY SALVAGE — the injection handler, absent from library/cas. -/
def injHandler : Handler S (Prog (S ⊕ₛ T)) where
  handle op := Prog.inl (Prog.op op)
theorem interpret_injHandler {S T : Sig} {A : Type} (p : Prog S A) :
    interpret (injHandler (S := S) (T := T)) p = Prog.inl p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    show Prog.bind (Prog.inl (Prog.op op)) _ = _
    simp only [Prog.op, Prog.inl, Prog.bind]
    exact congrArg (Prog.vis (Sum.inl op)) (funext fun a => ih a)

#print axioms shared_address_acquires_once
#print axioms unmemoized_acquires_twice
#print axioms fresh_does_not_share
#print axioms diamond_shares
#print axioms combinator_merge_acquires_twice
#print axioms memo_is_not_the_combinator
#print axioms liftL_injSvc
#print axioms liftL_through
#print axioms interpret_injHandler
#print axioms residual_sound_at_a_witness

/-! ## 9. COMPOSITION LAWS at the synthesis carrier. -/
theorem interpret_bind' [Monad M] [LawfulMonad M] (h : Handler S M)
    (p : Prog S A) (f : A → Prog S B) :
    interpret h (p >>= f) = interpret h p >>= fun a => interpret h (f a) :=
  interpret_bind h p f

theorem interpret_pure' [Monad M] (h : Handler S M) (a : A) :
    interpret h (pure a : Prog S A) = pure a := rfl

theorem andThen_empty_right (L : Layer) : Layer.andThen L Layer.empty = L := by
  simp only [Layer.andThen, Layer.empty, pure_bind, liftL_injSvc, interpret_id]
  have : (fun h : LHandler => (pure (Handler.through h (idHandler (S := LayerSig))) : Layer))
       = fun h => pure h := funext fun h => congrArg Prog.pure (through_id_right h)
  rw [this, bind_pure]

theorem andThen_empty_left (M : Layer) : Layer.andThen Layer.empty M = M := by
  simp only [Layer.andThen, Layer.empty]
  have : (fun g : LHandler =>
            interpret (liftL g) (pure injSvc : Layer)
              >>= fun h => (pure (Handler.through h (liftL g)) : Layer))
       = fun g => pure g := by
    funext g
    show (pure injSvc : Prog LayerSig LHandler) >>= _ = _
    rw [pure_bind]
    exact congrArg Prog.pure (Handler.ext fun op =>
      show interpret (liftL g) (Prog.op (S := LayerSig) (Sum.inl op)) = g.handle op from
        interpret_op (h := liftL g) (e := Sum.inl op))
  rw [this, bind_pure]

theorem andThen_assoc (L M N : Layer) :
    Layer.andThen (Layer.andThen L M) N = Layer.andThen L (Layer.andThen M N) := by
  simp only [Layer.andThen, interpret_bind', bind_assoc, pure_bind, interpret_pure',
             liftL_through, interpret_through,
             through_assoc leftUnit_of_lawful bindAssoc_of_lawful]

#print axioms andThen_empty_right
#print axioms andThen_empty_left
#print axioms andThen_assoc
