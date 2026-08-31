import Cas.Backend.Universal
import Cas.Lang.Tower

/-!
# THE MINIMAL LAYER — a deletion ledger, mechanized

Every element the five lanes converged on is put on trial here with ONE
question: *what breaks if I delete it?*  Everything that survives is below.
Everything that does not is named in the ledger with the deletion's proof.

WHAT SURVIVES.  One inductive with two constructors, and its `Sig` value.
Nothing else is minted — not a `Layer` type, not a `Scope` type, not a
`MemoMap`, not a `Runtime`, not an `HHandler`, not a `SystemNode` arm, not a
block table, not a `Sig.empty`, not a `sigOf`, not a signature-subsumption
relation, not a nonce.  `Layer` and the built context are `abbrev`s over
`Prog` and `Handler`; `provide` and `run` are `bind` + `interpret` +
`Handler.through`; the composition laws are `through_monoid`, which is
already on main.

THE DELETION LEDGER (each row is discharged in the section named).

  CUT  `merge`, `provideMerge`, `Handler.sum` at the layer, `mergeOn`,
       `mergeOn_unique`, `Handler.sum_unique` as a merge anchor
       -> §5.  A key the outer handler FORWARDS is answered by the inner.
          So `provide` on forwarding handlers IS merge, by `interpret_op`,
          in one line.  One operation, not three.
  CUT  the SECOND service signature, `Sig.sum` at the layer, `lift`/`liftL`,
       `liftL_through`, `liftL_injSvc`, `injSvc`, `scopePass`
       -> §1/§4.  Scope ops join the ONE layer signature as constructors.
          The built context becomes an ENDOMORPHISM handler, so
          `through_monoid` (Universal.lean:785) applies VERBATIM and the
          three composition laws are already proved on main.
  CUT  `memoize`, `MemoMap`, `MemoTable`, `Memo`, memo keys, `MemoOk`
       -> §8.  The store resolves children-first, so elaboration is a fold
          over a topologically ordered address list in which each address
          occurs ONCE.  The order IS the sharing; a memo table is a cache
          for a lookup that is never performed.
  CUT  `launch`, `never`, `SuspSig`
       -> §3.  `launch l = run l neverP`.  No lane claimed a law for it.
  CUT  `runtime`, `ManagedRuntime`
       -> §3.  A runtime is the bound variable `h` in `l >>= fun h => ...`.
  CUT  the `scoped` DELIMITER operation, the first-order BLOCK TABLE, the
       self-referential fuel-bounded floor, and with it the fuel-refusal
       pathology
       -> §9.  A Scope is the extent of a run.  One `ensuring` at the
          driver, a finalizer stack in the floor's state.  R18's four laws
          apply to ONE application of the ruled combinator.
  CUT  the `SystemNode.scoped` arm, the `fresh` nonce, and BOTH proposed
       address-moving events
       -> §9.  Acquisition lives inside the `CodeRef`'d constructor, which
          is where rc.112 puts it too (`Layer.effect(Tag,
          Effect.acquireRelease(..))`).  The content plane is UNCHANGED.
  CUT  `sigOf`, `SigEnv`, signature normalization/subsumption, `Sig.empty`,
       `DecidableEq Sig`
       -> §1.  No `Sig` is ever computed from content.
  CUT  `Layer.empty`, `Layer.shared`, `Layer.unwrap`, `Layer.build`,
       `restrictL`/`restrictR`, `Ctx`
       -> §3.  `pure idHandler`, `>>=`, `join`, `interpret`.  Names, not
          content.

  KEPT `LayerE` / `LSig` — the one mint.  R10's declared extension point,
       joining `CasSig`, `ByteSig`, `RootSig`, `WordSig`, `LlmSig`.
  KEPT the `Prog LSig (·)` BUILD PREFIX — §7 re-proves the field's settled
       falsifier at this exact carrier: without it, two uses cost two
       acquisitions.
  KEPT the `interpret hi outer` INSIDE `provide` — §11.  Delete it and the
       outer layer's BUILD can no longer use the inner's services, which is
       most of what `Layer.provide` is for.
  KEPT the finalizer stack in the floor's state and ONE `ensuring` — §9.

THE FINAL TYPE SET, in full:

    inductive LayerE | ask (key : String) | acquire (ctor : Nat)
    abbrev LSig  : Sig  := ⟨LayerE, fun _ => Addr32⟩
    abbrev H     : Type := Handler LSig (Prog LSig)     -- Effect's Context<R>
    abbrev Layer : Type := Prog LSig H                  -- a program whose value
                                                        -- is a handler (R12+1)

One inductive.  One `Sig` value.  Two abbrevs, both transparent.  Zero new
operations: `provide` is `bind`+`interpret`+`through`, `run` is
`bind`+`interpret`, `empty` is `pure idHandler`, and the three composition
laws are `through_monoid`, already on main.

CHECKED: `cd library/cas && lake env lean <this file>` -> exit 0, no errors,
no warnings, 38 `#print axioms` receipts, 21 axiom-free, ceiling
[propext, Quot.sound], no sorryAx, no Classical.choice, no native_decide.
-/

namespace Minimal

open Cas.Lang

/-! ## §1. THE ONE MINT

A layer language is a signature.  `Sig` is the estate's carrier and this is
a VALUE of it, exactly as `ByteSig` (`Tower.lean:52`) and `CasSig` are.

TWO constructors, and the deletion test for each:

* `ask` — delete it and there is no service language at all; a layer
  handler would have nothing to handle.
* `acquire` — delete it and a resource has no registration site, so no
  finalizer can be pushed and R18 has no subject.  It cannot be folded into
  `ask`, because `ask` is the USE site and acquisition must happen once at
  the BUILD (§7).

There is no third constructor.  In particular there is NO `scoped`
delimiter: §9 deletes it.

`Ans` is CONSTANT.  A type-indexed service set is not first-order content
(R7), so provides/requires are value-level keys and NO `Sig` is ever
computed from content.  That single fact deletes `sigOf`, `SigEnv`,
`Sig.empty`, signature subsumption, and the `DecidableEq Sig` obligation. -/

abbrev Key := String

/-- The layer language.  In the shipped form `ctor` is a `CodeRef` and the
answer is `Addr32`; `Nat` here keeps the probe self-contained. -/
inductive LayerE where
  | ask (key : Key)
  | acquire (ctor : Nat)
  deriving DecidableEq

abbrev LayerE.Ans : LayerE → Type
  | _ => Nat

abbrev LSig : Sig := ⟨LayerE, LayerE.Ans⟩

/-! ## §2. THE CARRIER — two abbrevs, no new type

`H` is the built context.  Effect calls it `Context<R>`; the estate already
has it and it is `Handler`.  Crucially it is an ENDOMORPHISM handler — same
signature above and below — which is what makes `through_monoid` apply.

`Layer` is a PROGRAM WHOSE VALUE IS A HANDLER.  That is R12 ("a service IS a
handler, and a handler CAN BE a program") read one notch further.  Both
names are pure readability: erasing them changes nothing, and §7 shows the
`Prog LSig (·)` prefix — not the name — is what is load-bearing. -/

abbrev H : Type := Handler LSig (Prog LSig)

abbrev Layer : Type := Prog LSig H

/-- Both abbrevs are transparent: no inductive, no eliminator, no new
equality, `LawfulMonad` inherited from `Prog`. -/
theorem carrier_is_transparent : Layer = Prog LSig (Handler LSig (Prog LSig)) := rfl

example : LawfulMonad (Prog LSig) := inferInstance

/-! ## §3. THE OPERATIONS — ZERO minted

Everything is `bind`, `interpret`, `Handler.through`, `idHandler`, `pure`.
Five operations, all already in `library/cas`.

DELETED HERE, with the reason:

* `Layer.empty` -> `pure idHandler`.  Written out below in every law.
* `Layer.build` -> `interpret floor l`.  It was never primitive.
* `Layer.shared c k` -> `c >>= k`, by `rfl` (`shared_is_bind`).
* `Layer.unwrap` -> `join`, by `rfl` (`unwrap_is_join`).
* `Layer.launch l s` -> `run l s`.  No lane claimed a law for it; its `never`
  is the target's own suspension, not the layer's.
* `runtime` -> the bound `h` in `l >>= fun h => ...`.  Running many programs
  against one runtime is one `bind` (`one_runtime_many_programs`).
* `Ctx` -> `Handler`.  A rename with zero content.

`provideL` and `runL` below are kept as NAMES ONLY, so the laws are legible.
-/

/-- The one composition.  `merge` and `provideMerge` are this same operation
(§5); Effect's requirement-hiding `provide` is NOT (§6). -/
def provideL (inner outer : Layer) : Layer :=
  inner >>= fun hi => interpret hi outer >>= fun ho => pure (ho.through hi)

/-- Consuming a layer — Effect's `Effect.provide`. -/
def runL (l : Layer) (p : Prog LSig A) : Prog LSig A :=
  l >>= fun h => interpret h p

theorem shared_is_bind (c : Layer) (k : H → Layer) :
    (c >>= k) = c.bind k := rfl

theorem unwrap_is_join (m : Prog LSig Layer) : (m >>= id) = m.bind id := rfl

theorem build_is_interpret [Monad M] (floor : Handler LSig M) (l : Layer) :
    interpret floor l = interpret floor l := rfl

/-- A runtime is a bound variable. -/
theorem one_runtime_many_programs (l : Layer) (p q : Prog LSig Nat) :
    (l >>= fun h => interpret h p >>= fun a => interpret h q >>= fun b => pure (a + b))
      = l.bind (fun h => (interpret h p).bind
          (fun a => (interpret h q).bind (fun b => Prog.pure (a + b)))) := rfl

/-! ## §4. THE LAWS — all discharged by theorems already on main

Because `H` is an ENDOMORPHISM handler, `through_monoid`
(`Cas/Backend/Universal.lean:785`) applies VERBATIM.  Four of the five lanes
wrote it off as the wrong anchor and the fifth claimed it at two different
signatures, where it does not typecheck.  At one signature it is exactly
right, and it is already proved. -/

/-- Bind congruence at `Prog`, so the tactic block never has to guess a
monad instance.  `congrArg` + `funext`; no content. -/
private theorem pcongr {A B : Type} {p : Prog LSig A} {f g : A → Prog LSig B}
    (h : ∀ a, f a = g a) : (p >>= f : Prog LSig B) = (p >>= g) :=
  congrArg (fun k => p >>= k) (funext h)

/-- `interpret_bind` (Handler.lean:53) restated at `>>=` so `simp` matches;
same proof term, zero new content. -/
private theorem ibind (h : H) {A B : Type} (p : Prog LSig A) (f : A → Prog LSig B) :
    interpret h (p >>= f) = (interpret h p >>= fun a => interpret h (f a)) :=
  interpret_bind h p f

private theorem ipure (h : H) {A : Type} (a : A) :
    interpret h (pure a : Prog LSig A) = pure a := rfl

theorem through_monoid_applies (t u v : H) :
    (t.through u).through v = t.through (u.through v)
      ∧ t.through (idHandler (S := LSig)) = t
      ∧ (idHandler (S := LSig)).through t = t :=
  through_monoid t u v

/-- ASSOCIATIVITY.  Discharged by `through_assoc` (Universal.lean:739) with
`interpret_through` (Tower.lean:71) and `interpret_bind` (Handler.lean:53).
Note the residue after the rewrites IS `through_assoc` and nothing else. -/
theorem provideL_assoc (a b c : Layer) :
    provideL (provideL a b) c = provideL a (provideL b c) := by
  simp only [provideL, ibind, ipure, interpret_through, bind_assoc, pure_bind]
  refine pcongr fun ha => ?_
  refine pcongr fun hb => ?_
  refine pcongr fun hc => ?_
  exact congrArg pure (through_monoid hc hb ha).1.symm

/-- LEFT UNIT.  `interpret_id` (Representation.lean:68) + `through_id_right`
(Universal.lean:757). -/
theorem provideL_empty_left (o : Layer) : provideL (pure idHandler) o = o := by
  have e : (fun ho : H => (pure (ho.through (idHandler (S := LSig))) : Layer)) = pure := by
    funext ho; rw [through_id_right]
  simp only [provideL, pure_bind, interpret_id, e, bind_pure]

/-- RIGHT UNIT.  `through_id_left` (Universal.lean:765) at
`rightUnit_of_lawful`. -/
theorem provideL_empty_right (i : Layer) : provideL i (pure idHandler) = i := by
  have e : (fun hi : H =>
      (interpret hi (pure idHandler) >>= fun ho => pure (ho.through hi) : Layer)) = pure := by
    funext hi
    show Prog.pure ((idHandler (S := LSig)).through hi) = Prog.pure hi
    exact congrArg Prog.pure (through_id_left rightUnit_of_lawful hi)
  simp only [provideL, e, bind_pure]

/-- CONSUMPTION distributes over composition — Effect's
`provide(p, provide(i,o)) = provide(provide(p,o), i)`.  `interpret_bind` +
`interpret_through`. -/
theorem runL_provideL (i o : Layer) (p : Prog LSig A) :
    runL (provideL i o) p = runL i (runL o p) := by
  simp only [runL, provideL, ibind, interpret_through, bind_assoc, pure_bind]

theorem runL_empty (p : Prog LSig A) : runL (pure idHandler) p = p := by
  show interpret (idHandler (S := LSig)) p = p
  exact interpret_id p

/-! ## §5. DELETION — `merge` IS `provide`

THE THEOREM.  A layer handler ANSWERS the keys it provides and FORWARDS
every other operation.  `Handler.through` on a forwarding key is the inner
handler's own clause — by `interpret_op` (Representation.lean:115) and
nothing else.  So the composite answers the union of both key sets: that is
merge, and it needs no operation of its own.

Consequently `Handler.sum` is not merge's anchor and `Handler.sum_unique` was
never about it — a point three lanes reached from three directions.  There is
no `mergeOn`, no `mergeOn_unique`, no overlap combinator: OVERLAP IS
SHADOWING, and the outer wins, which is `Context.add`'s last-wins and is
already proved on the content plane by `canonServices_last_wins`
(`Cas/Backend/Canon.lean:278`). -/

/-- A key the outer handler forwards is answered by the inner. THIS IS MERGE. -/
theorem through_forwards (hi ho : H) (k : Key)
    (fwd : ho.handle (.ask k) = Prog.op (LayerE.ask k)) :
    (ho.through hi).handle (.ask k) = hi.handle (.ask k) := by
  show interpret hi (ho.handle (.ask k)) = _
  rw [fwd, interpret_op]

/-- A key the outer handler answers, the outer keeps — the outer SHADOWS the
inner, matching `Context.add`. -/
theorem through_shadows (hi ho : H) (k : Key) :
    (ho.through hi).handle (.ask k) = interpret hi (ho.handle (.ask k)) := rfl

/-- A service leaf: answer one key, forward everything else. -/
def leafH (key : Key) (inst : Nat) : H where
  handle
    | .ask k => if k = key then Prog.pure inst else Prog.op (LayerE.ask k)
    | .acquire c => Prog.op (LayerE.acquire c)

/-- MERGE, EXHIBITED: `provideL` of two independent leaves answers BOTH keys
with each leaf's own instance.  No merge operation was used. -/
theorem provide_is_merge (i j : Nat) :
    ((leafH "b" j).through (leafH "a" i)).handle (.ask "a") = Prog.pure i
      ∧ ((leafH "b" j).through (leafH "a" i)).handle (.ask "b") = Prog.pure j := by
  constructor
  · exact through_forwards (leafH "a" i) (leafH "b" j) "a" rfl
  · rfl

/-! ## §6. THE RESIDUAL CALCULUS — pure, first-order, OUTSIDE `Prog` (R14a)

`residualOf` (`Cas/Backend/EmitLayer.lean:243`) already computes this on the
content plane; restated here at value-level keys so the ledger's claim is
checkable.

THE FINDING, and it is new.  Position E proved Effect's `provide` is NOT
associative on the residual, and it is right — but the non-associativity is
an artefact of HIDING (`.provide`'s arm keeps only `ro.provides`).  The
single operation this design keeps is `residualOf`'s `.provideMerge` arm
(EmitLayer.lean:257), which hides nothing, and it IS associative — proved in
general below.  So deleting `merge`/`provideMerge` in favour of one
non-hiding `provide` buys associativity on BOTH planes. -/

def without (xs ys : List Key) : List Key := xs.filter (fun x => !ys.contains x)

structure Res where
  provides : List Key
  requires : List Key
  deriving DecidableEq, Repr

/-- The kept arm: `residualOf`'s `.provideMerge`, verbatim at keys. -/
def resProvide (i o : Res) : Res :=
  { provides := i.provides ++ o.provides,
    requires := i.requires ++ without o.requires i.provides }

/-- Effect's requirement-HIDING `provide`: `residualOf`'s `.provide` arm. -/
def resHide (i o : Res) : Res :=
  { provides := o.provides,
    requires := i.requires ++ without o.requires i.provides }

theorem without_append (xs ys zs : List Key) :
    without xs (ys ++ zs) = without (without xs ys) zs := by
  simp only [without, List.filter_filter]
  refine List.filter_congr ?_
  intro x _
  simp [Bool.not_or, Bool.and_comm]

theorem without_distrib (xs ys zs : List Key) :
    without (xs ++ ys) zs = without xs zs ++ without ys zs := by
  simp [without, List.filter_append]

theorem without_comm (xs ys zs : List Key) :
    without (without xs ys) zs = without (without xs zs) ys := by
  simp only [without, List.filter_filter]
  exact List.filter_congr (fun x _ => Bool.and_comm _ _)

/-- THE KEPT OPERATION IS ASSOCIATIVE ON THE CONTENT PLANE TOO. -/
theorem resProvide_assoc (a b c : Res) :
    resProvide (resProvide a b) c = resProvide a (resProvide b c) := by
  simp only [resProvide, Res.mk.injEq]
  refine ⟨List.append_assoc _ _ _, ?_⟩
  rw [without_distrib, ← List.append_assoc, without_append, without_comm]

/-- AND THE HIDING ONE IS NOT — position E's witnesses, re-checked. -/
theorem resHide_not_assoc :
    resHide (resHide ⟨["A"], []⟩ ⟨["B"], ["A"]⟩) ⟨["C"], ["A"]⟩
      ≠ resHide ⟨["A"], []⟩ (resHide ⟨["B"], ["A"]⟩ ⟨["C"], ["A"]⟩) := by decide

/-! ## §7. WHAT CANNOT BE DELETED — the build prefix

The field's one settled result, re-proved at THIS carrier rather than cited.
Delete the `Prog LSig (·)` prefix — i.e. make a layer a bare `H` — and the
acquisition moves into the clause, where it is re-entered per use.  Two uses
then cost two acquisitions.  A connection pool, and every resource `Layer`
exists to own, becomes unrepresentable.

This is the deletion that FAILS, and it is why `Layer` is `Prog LSig H` and
not `H`. -/

/-- The floor.  `ask` at the floor is an unresolved service — a build
refusal.  `acquire` allocates an instance, records it, and PUSHES its
release onto the finalizer stack.  Registration is a STATE effect inside
`ExceptT`: R18's forced transformer ORDER. -/
abbrev St : Type := Nat × List Nat × List Nat

abbrev Tgt : Type → Type := ExceptT String (StateM St)

/-- The target is R18's ruled shape unfolded: state OUTSIDE error, so the
error branch still carries the state.  `EC1-CE045` does not reach it. -/
theorem Tgt_is_R18_order (A : Type) : Tgt A = (St → Except String A × St) := rfl

example : LawfulMonad Tgt := inferInstance

def floor : Handler LSig Tgt where
  handle
    | .ask _ => fun s => (.error "unresolved service", s)
    | .acquire c => fun s => (.ok s.1, (s.1 + 1, s.2.1 ++ [c], (c + 100) :: s.2.2))

/-- Acquisition in the BUILD prefix — the kept design. -/
def leafL (key : Key) (ctor : Nat) : Layer :=
  Prog.op (LayerE.acquire ctor) >>= fun i => Prog.pure (leafH key i)

/-- Acquisition in the CLAUSE — the deleted design (`Layer := H`). -/
def leafC (key : Key) (ctor : Nat) : H where
  handle
    | .ask k => if k = key then Prog.op (LayerE.acquire ctor) else Prog.op (LayerE.ask k)
    | .acquire c => Prog.op (LayerE.acquire c)

def useTwice (key : Key) : Prog LSig Nat :=
  Prog.op (LayerE.ask key) >>= fun a => Prog.op (LayerE.ask key) >>= fun b => Prog.pure (a + b)

def trace (t : Tgt A) : List Nat := (t (0, [], [])).2.2.1

theorem prefix_acquires_once :
    trace (interpret floor (runL (leafL "db" 7) (useTwice "db"))) = [7] := rfl

theorem clause_acquires_per_use :
    trace (interpret floor (runL (Prog.pure (leafC "db" 7)) (useTwice "db"))) = [7, 7] := rfl

theorem build_step_is_observable :
    trace (interpret floor (runL (leafL "db" 7) (useTwice "db")))
      ≠ trace (interpret floor (runL (Prog.pure (leafC "db" 7)) (useTwice "db"))) := by
  decide

/-! ## §8. DELETION — the memo table

`MemoMap` (rc.112), `Memo` (B), `MemoTable` (C) all exist to make one
address build once.  Under content addressing the store's `Resolved` table
is already CHILDREN-FIRST (`Cas/Backend/EmitLayer.lean:236`), so elaboration
is a fold over a topologically ordered address list in which each address
occurs EXACTLY ONCE.  The order IS the sharing.  A memo table is a cache for
a lookup that is never performed — performance wearing a semantics costume.

What remains is `Env`, which is a LET ENVIRONMENT, not a cache: it holds the
handler each address was bound to, and the binder is Lean's `>>=` at
elaboration time.  So the stored content needs NO `let`/`shared` arm either
(variables, alpha-equivalence and canonicalization inside a Merkle DAG all
delete with it), and `fresh` needs no nonce: freshness is re-elaboration,
a property of the traversal.

Sharing IS semantic — the trace separates — so this is a deletion of the
MECHANISM, not of the fact.

`SystemNode.fresh` KEEPS ITS ARM AND NEEDS NO NONCE.  Its meaning is: at
this child, elaborate by `elabTree` instead of by `envGet` — re-elaboration,
which acquires again.  The pair below is therefore also the `fresh` exhibit,
and it settles the B-vs-E collision on the nonce in B's favour without
adding anything: freshness is the traversal, not the key. -/

inductive Node where
  | leaf (key : Key) (ctor : Nat)
  | provide (inner outer : Nat)

abbrev Table := List (Nat × Node)
abbrev Env := List (Nat × H)

def nodeAt (t : Table) (a : Nat) : Node :=
  match t.find? (fun r => r.1 == a) with
  | some r => r.2
  | none => .leaf "?" 0

def envGet (e : Env) (a : Nat) : H :=
  match e.find? (fun r => r.1 == a) with
  | some r => r.2
  | none => idHandler

/-- The elaboration.  NO memo argument: `order` carries each address once. -/
def elabTopo (t : Table) : List Nat → Env → Prog LSig Env
  | [], e => Prog.pure e
  | a :: rest, e =>
    (match nodeAt t a with
      | .leaf key ctor => leafL key ctor
      | .provide i o => Prog.pure ((envGet e o).through (envGet e i)))
    >>= fun h => elabTopo t rest ((a, h) :: e)

def denote (t : Table) (order : List Nat) (root : Nat) : Layer :=
  elabTopo t order [] >>= fun e => Prog.pure (envGet e root)

/-- The control: re-elaborate from the root, ignoring shared addresses. -/
def elabTree (t : Table) : Nat → Nat → Layer
  | 0, _ => Prog.pure idHandler
  | f + 1, a =>
    match nodeAt t a with
    | .leaf key ctor => leafL key ctor
    | .provide i o => provideL (elabTree t f i) (elabTree t f o)

/-- A diamond: `db` at address 0 is referenced by BOTH 3 and 4. -/
def diamond : Table :=
  [(0, .leaf "db" 7), (1, .leaf "a" 1), (2, .leaf "b" 2),
   (3, .provide 0 1), (4, .provide 0 2), (5, .provide 3 4)]

theorem topological_order_shares :
    trace (interpret floor (denote diamond [0, 1, 2, 3, 4, 5] 5)) = [7, 1, 2] := rfl

theorem tree_elaboration_does_not :
    trace (interpret floor (elabTree diamond 8 5)) = [7, 1, 7, 2] := rfl

theorem sharing_is_the_order :
    trace (interpret floor (denote diamond [0, 1, 2, 3, 4, 5] 5))
      ≠ trace (interpret floor (elabTree diamond 8 5)) := by decide

/-! ## §9. SCOPE — deleted as a thing; kept as the extent of a run

THE QUESTION the brief asks: are Layer and Scope two concepts or one seen
twice?  Answer: neither.  A Scope is not a concept here at all — it is the
EXTENT OF A RUN, and an extent needs no representation.

So there is no `Scope` type, no `ScopeSig`, no `scoped` operation, no
`ensuringExit` operation, no block table, no `HHandler`, no self-referential
floor and hence no fuel bound (and none of the fuel-refusal-fires-finalizers
pathology a delimiter forces).  What is kept is the smallest thing that
discharges R18: a finalizer STACK in the floor's state, and ONE application
of the ruled `ensuring` combinator at the driver.

`ens` below is `EnsuringRepair.ensuringT` (`:547`) with `Word`, `Refusal`
and `Addr32` generalized; that file is unpromoted staging and cannot be
imported, so the laws are RE-PROVED here rather than cited.  Because there
is exactly one application, none of the nested-`ensuring` machinery is
reachable and none is claimed — which is the misattribution that killed a
LIFO claim elsewhere in this packet.  LIFO here is a property of the STACK,
and it is exhibited on a two-resource run.

WHAT THIS DELETES ON THE CONTENT PLANE.  `SystemNode` is UNCHANGED — no
`scoped` arm, no nonce, no address-moving event, no risk to
`#guard SystemNode.schemaCode.discriminated` (`System.lean:225`).
Acquisition lives inside the `CodeRef`'d constructor, which is exactly where
rc.112 puts it (`Layer.effect(Tag, Effect.acquireRelease(acq, rel))`). -/

def ens (body : Tgt A) (fin : Tgt Unit) : Tgt A := fun s =>
  match body s with
  | (.ok a, s₁) =>
    match fin s₁ with
    | (.ok _, s₂) => (.ok a, s₂)
    | (.error e, s₂) => (.error e, s₂)
  | (.error e, s₁) => (.error e, (fin s₁).2)

/-- Pop the whole stack, innermost first. -/
def closeAll : Tgt Unit := fun s => (.ok (), (s.1, s.2.1 ++ s.2.2, []))

/-- THE DRIVER.  This, and nothing else, is the scope. -/
def drive (l : Layer) (p : Prog LSig A) : Tgt A :=
  ens (interpret floor (runL l p)) closeAll

/-- R18, law 1: the finalizer runs after the body on success. -/
theorem ens_runs_on_success (body : Tgt A) (fin : Tgt Unit) (s s₁ s₂ : St) (a : A)
    (hb : body s = (.ok a, s₁)) (hf : fin s₁ = (.ok (), s₂)) :
    ens body fin s = (.ok a, s₂) := by
  simp [ens, hb, hf]

/-- R18, law 2: the finalizer runs on FAILURE, with NO premise on it, and
its state SURVIVES the error branch.  This is exactly the half a target
discarding state on error cannot state (`EC1-CE045`). -/
theorem ens_runs_on_failure (body : Tgt A) (fin : Tgt Unit) (s s₁ : St) (e : String)
    (hb : body s = (.error e, s₁)) :
    ens body fin s = (.error e, (fin s₁).2) := by
  simp [ens, hb]

/-- R18, law 3: the finalizer never replaces the refusal. -/
theorem ens_never_replaces (body : Tgt A) (fin : Tgt Unit) (s s₁ : St) (e : String)
    (hb : body s = (.error e, s₁)) :
    (ens body fin s).1 = .error e := by
  simp [ens, hb]

/-- NON-VACUITY: two finalizers leaving different states are separated on a
failing body — the pair a word-forgetting target identifies. -/
theorem ens_separates_finalizers :
    trace (ens (A := Nat) (fun s => (.error "boom", s))
            (fun s => (.ok (), (s.1, s.2.1 ++ [1], s.2.2))))
      ≠ trace (ens (A := Nat) (fun s => (.error "boom", s))
            (fun s => (.ok (), (s.1, s.2.1 ++ [2], s.2.2)))) := by decide

/-- ONE resource: acquired at the build, released at the end of the run. -/
theorem drive_releases : (drive (leafL "db" 7) (useTwice "db")) (0, [], [])
    = (.ok 0, (1, [7, 107], [])) := rfl

/-- Without the driver's `ens` the resource is NEVER released — the deletion
that fails, and the reason `drive` is kept. -/
theorem undriven_never_releases :
    trace (interpret floor (runL (leafL "db" 7) (useTwice "db"))) = [7] := rfl

/-- LIFO, and it is a property of the STACK, not of nested `ensuring`.
Acquire 1, acquire 2, release 2, release 1. -/
theorem release_is_lifo :
    (drive (provideL (leafL "a" 1) (leafL "b" 2)) (Prog.op (LayerE.ask "a"))) (0, [], [])
      = (.ok 0, (2, [1, 2, 102, 101], [])) := rfl

/-- FAILURE: an unresolved service refuses the build; both finalizers still
run, the state survives, and the refusal is reported unchanged. -/
theorem release_on_refusal :
    (drive (provideL (provideL (leafL "a" 1) (leafL "b" 2))
        (Prog.op (LayerE.ask "missing") >>= fun _ => Prog.pure (idHandler (S := LSig))))
      (Prog.op (LayerE.ask "a"))) (0, [], [])
      = (.error "unresolved service", (2, [1, 2, 102, 101], [])) := rfl

/-! ## §10. THE LAST DELETION TEST — inside `provide` itself

`provideL i o` builds the outer UNDER the inner: `interpret hi outer`.  Can
that `interpret` be deleted, leaving `liftM2 Handler.through` — build both
independently, compose the handlers?

NO, and this is the second deletion that fails.  Deleting it means the outer
layer's BUILD cannot use the inner's services, which is most of what
`Layer.provide` is for (a client layer whose constructor needs the config
layer).  Exhibited: the same pair of layers succeeds under `provideL` and
REFUSES under the naive version — and note the finalizer still runs and the
state still survives on the refusal path, so R18 is discharged on both. -/

def provideNaive (i o : Layer) : Layer :=
  i >>= fun hi => o >>= fun ho => pure (ho.through hi)

/-- A layer whose BUILD asks for a service. -/
def needsAtBuild (dep out : Key) : Layer :=
  Prog.op (LayerE.ask dep) >>= fun i => Prog.pure (leafH out i)

theorem build_runs_under_the_inner :
    (drive (provideL (leafL "db" 7) (needsAtBuild "db" "app"))
      (Prog.op (LayerE.ask "app"))) (0, [], []) = (.ok 0, (1, [7, 107], [])) := rfl

theorem naive_provide_cannot_build :
    (drive (provideNaive (leafL "db" 7) (needsAtBuild "db" "app"))
      (Prog.op (LayerE.ask "app"))) (0, [], [])
      = (.error "unresolved service", (1, [7, 107], [])) := rfl

/-- Did the build succeed? -/
def built (t : Tgt A) : Bool := match (t (0, [], [])).1 with | .ok _ => true | .error _ => false

theorem interpret_in_provide_is_load_bearing :
    built (drive (provideL (leafL "db" 7) (needsAtBuild "db" "app"))
        (Prog.op (LayerE.ask "app")))
      ≠ built (drive (provideNaive (leafL "db" 7) (needsAtBuild "db" "app"))
        (Prog.op (LayerE.ask "app"))) := by decide

/-! ## §11. RECEIPTS -/

#print axioms carrier_is_transparent
#print axioms shared_is_bind
#print axioms unwrap_is_join
#print axioms one_runtime_many_programs
#print axioms pcongr
#print axioms ibind
#print axioms through_monoid_applies
#print axioms provideL_assoc
#print axioms provideL_empty_left
#print axioms provideL_empty_right
#print axioms runL_provideL
#print axioms runL_empty
#print axioms through_forwards
#print axioms through_shadows
#print axioms provide_is_merge
#print axioms without_append
#print axioms without_comm
#print axioms without_distrib
#print axioms resProvide_assoc
#print axioms resHide_not_assoc
#print axioms Tgt_is_R18_order
#print axioms prefix_acquires_once
#print axioms clause_acquires_per_use
#print axioms build_step_is_observable
#print axioms topological_order_shares
#print axioms tree_elaboration_does_not
#print axioms sharing_is_the_order
#print axioms ens_runs_on_success
#print axioms ens_runs_on_failure
#print axioms ens_never_replaces
#print axioms ens_separates_finalizers
#print axioms drive_releases
#print axioms undriven_never_releases
#print axioms release_is_lifo
#print axioms release_on_refusal
#print axioms build_runs_under_the_inner
#print axioms naive_provide_cannot_build
#print axioms interpret_in_provide_is_load_bearing

end Minimal
