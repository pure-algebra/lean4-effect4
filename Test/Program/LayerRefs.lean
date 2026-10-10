import Effect4.Laws.Program.Typed.Assembly
import Test.Program.TypedSplit

/-!
# Test.Program.LayerRefs — M5 for programs with layer references (decisions row 153 (b))

`E4-TYPED-CE-019`. The checker certifies a program with layer references as its expansion
(`typeOfProgram`, `Program/Typing.lean:61-64`) and refuses a reference as written
(`Program/Checker.lean:259`), while `loadR` loads the program as written and the run reaches a
reference's target by redirect (`Laws/Program/DenoteR.lean`, the `.ref` arm of
`denoteLayerWith`). Before row 153 the typed state checked a point's node as written
(`PointTyped`), so the root point of such a program was typed at no type and M5's reduction to
the denotation lemma (`load_typed_of_denotesTyped`) carried a reference-free premise. That is
kept below as history over a local copy of the old point typing (`OldPointTyped`,
`old_root_untyped`). Since row 153 the typed state checks a node through the rounds of the
program's expansion (`Eff.expandIn`, `Laws/Program/ReferenceTyping.lean`), the corpus's
`layer.ref` program's root point is typed at the checker's type (`root_typed`), and the
reduction applies to it with no such premise (`loadsTyped`).

The run is the program's, not the expansion's. A reference's build memoizes at its target's path
(the redirect, `denoteLayer_ref_redirect`), the key two references share, while the expansion's
copy at the site would memoize at the site's own path (`memo_keys_differ`, at a program whose
target is memoized). So the agreement is the redirect, with the typing read through the
expansion, not an equality of the program's and the expansion's denotations.

`DenotesTyped` is M5's denotation lemma (`denotesTyped`, proved at every source by
`denotesTyped`, `Laws/Program/Typed/LayerArm.lean`); `loadsTyped` here is the reduction from it at
this program, as `load_typed_of_denotesTyped` is. Its premise that the references are well
formed (decisions row 170) holds here (`wellFormed`), and the reduction discharges it from the
checker's verdict (`checked`, `layerRefsWF_of_typeOf`). The finite facts (`checked`,
`wellFormed`, `site`, the memo keys) are computed by the kernel.
-/

set_option autoImplicit false
namespace Test.Program.LayerRefs
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-- The typed corpus's `layer.ref` program (`Test/Program/TypedCorpus.lean:76`), as
`Test/Program/TypedSplit.lean` spells it: a layer, then a reference to it at a second site. -/
abbrev layerRef : NativeEff := Test.Program.TypedSplit.layerRef
abbrev key : ServiceKey := Test.Program.TypedSplit.key

def src : ProgramSource := layerRef

/-- The type the checker gives the program's expansion. -/
def rootTy : EffTy := EffTy.pure .nat

theorem checked : Program.typeOfProgram src.signature src.program = some rootTy := by
  decide +kernel

theorem wellFormed : layerRef.layerRefsWF = true := by decide +kernel

theorem site : ([1, 0], [0, 0]) ∈ layerRef.refSites [] := by decide +kernel

theorem has_reference : layerRef.refSites [] ≠ [] := by decide +kernel

/-- The checker refuses the program as written: at its reference. -/
theorem check_refuses (ty : EffTy) : Checker.check src.signature [] [] layerRef ≠ .ok ty := by
  intro h
  have refused : (match Checker.check src.signature [] [] layerRef with
      | .ok _ => false
      | .error _ => true) = true := by decide +kernel
  rw [h] at refused
  exact Bool.noConfusion refused

/-- The checker types the expansion at `rootTy`. -/
theorem check_expansion :
    Checker.check src.signature [] [] (Eff.expandIn layerRef layerRef) = .ok rootTy := by
  decide +kernel

/-! ## Red, history: the root point as written is not the checker's object -/

/-- History: `PointTyped` before decisions row 153, which checked a node as written. -/
def OldPointTyped (src : ProgramSource) (w : W) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check src.signature env point.path e = .ok ty ∧
    EnvTyped w env point.env

/-- **Red, history** (`E4-TYPED-CE-019`'s witness): before row 153 the root point of the corpus's
`layer.ref` program was typed at no type at any world and fuel, so `DenotesTyped` said nothing
about its loaded code, and the reduction's reference-free premise excluded it
(`has_reference`). -/
theorem old_root_untyped (w : W) (fuel : Nat) (ty : EffTy) :
    ¬ OldPointTyped src w (rootPoint fuel) ty := by
  rintro ⟨e, env, hat, hcheck, henv⟩
  change some (Node.eff layerRef) = some (.eff e) at hat
  cases hat
  have hlen : env.length = 0 := henv.1
  have hnil : env = [] := List.eq_nil_of_length_eq_zero hlen
  subst hnil
  exact check_refuses ty hcheck

/-! ## The flip: the root point typed through the expansion, and M5 through the reduction -/

/-- **The flip** (proved): the root point is typed at the checker's type at every world and fuel,
its node read through the expansion's rounds. -/
theorem root_typed (w : W) (fuel : Nat) : PointTyped src w (rootPoint fuel) rootTy :=
  ⟨layerRef, [], rfl, check_expansion, envTyped_nil w, (fun _ h => nomatch h), stackTyped_nil _ _ _⟩

/-- The loaded head is not a race marker, at every compile budget. -/
theorem noMarker (cf : Nat) :
    raceRegistrationR (denoteR layerRef layerRef (rootPoint cf)) = none := by
  cases cf with
  | zero =>
    rw [denoteR_zero layerRef layerRef (rootPoint 0) rfl]
    rfl
  | succ k =>
    show raceRegistrationR (denoteR layerRef (.bind
      (.provideLayer (.succeed key (.nat 7)) false (.service key))
      (.provideLayer (.ref [0, 0]) false (.service key))) (rootPoint (k + 1))) = none
    rw [denoteR_bind layerRef _ _ (rootPoint (k + 1)) (Nat.succ_ne_zero k)]
    rfl

/-- **M5 at the corpus's `layer.ref` program, through the reduction** (proved from M5's open
denotation lemma `DenotesTyped`): the program loads into `J` at every fuel. Before row 153 the
reduction's reference-free premise excluded it; row 170's well-formedness premise is the
checker's (`layerRefsWF_of_typeOf`). -/
theorem loadsTyped (denotes : DenotesTyped src) (fuel cf : Nat) : LoadsTyped src rootTy fuel cf :=
  fun _ checked _ => load_typed_of_denotesTyped src rootTy fuel cf denotes (noMarker cf) checked

/-! ## The redirect at the program's reference -/

/-- **The redirect agreement at this program's one reference** (proved): the build at the site
is the target's term built at the redirected point. -/
theorem site_redirect (q : Point) (m : MemoMapId) (scope k : Nat) (hf : q.fuel = k + 1) :
    denoteLayer layerRef (.ref [0, 0]) q m scope =
      denoteLayer layerRef (.succeed key (.nat 7)) (q.redirect [0, 0]) m scope := by
  rw [denoteLayer_ref_redirect layerRef wellFormed site q m scope hf]
  rfl

/-- The expansion holds the target's term at the site: what the checker types there is what the
redirected run builds (a finite check at this program; the general fact is owed, seat D1's
receipt). -/
theorem expansion_site_is_target :
    (Node.eff layerRef.expandRefs).layerAt [1, 0] = (Node.eff layerRef.expandRefs).layerAt [0, 0] ∧
      (Node.eff layerRef.expandRefs).layerAt [0, 0] = some (.succeed key (.nat 7)) := by
  decide +kernel

/-! ## The run is not the expansion's: memo keys -/

/-- A program whose reference's target is memoized (`Layer.effect`). -/
def effectRef : NativeEff :=
  .bind (.provideLayer (.effect key (.succeed (.lit (.nat 7)))) false (.service key))
    (.provideLayer (.ref [0, 0]) false (.service key))

theorem effectRef_wellFormed : effectRef.layerRefsWF = true := by decide +kernel

/-- The expansion's copy at the reference site is the target's term. -/
theorem effectRef_expanded_site :
    (Node.eff effectRef.expandRefs).layerAt [1, 0] =
      some (.effect key (.succeed (.lit (.nat 7)))) := by
  decide +kernel

/-- The first memo key a build reads, along one answer per operation: a scope handle for a store
row, the closing marker's exit, `unit` for a counted suspend. -/
def firstMemoKey : Nat → RProgram → Option (List Nat)
  | 0, _ => none
  | _ + 1, .vis (.inl (.memoGet layer _)) _ => some layer
  | n + 1, .vis (.inl _) k => firstMemoKey n (k (Val.scopeHandle 5))
  | n + 1, .vis (.inr (.guard_ _)) k => firstMemoKey n (k none)
  | n + 1, .vis (.inr (.unguard ex)) k => firstMemoKey n (k ex)
  | n + 1, .vis (.inr (.suspend _)) k => firstMemoKey n (k Val.unit)
  | _ + 1, _ => none

/-- The reference site's build point. -/
def siteQ : Point := { rootPoint 10 with path := [1, 0] }

/-- The program as written builds the site through its target: the memo key is the target's. -/
theorem run_key : firstMemoKey 20 (denoteLayer effectRef (.ref [0, 0]) siteQ ⟨0⟩ 0) = some [0, 0] := by
  decide +kernel

/-- The expansion's copy at the site would key the memo on the site's own path. -/
theorem expansion_key :
    firstMemoKey 20 (denoteLayer effectRef.expandRefs (.effect key (.succeed (.lit (.nat 7))))
      siteQ ⟨0⟩ 0) = some [1, 0] := by
  decide +kernel

/-- **Red** (proved): the run's build at a reference site is not the expansion's build at the same
point, at a memoized target: the redirect is what makes two references share one memo entry, so
row 153's agreement is the redirect (`denoteLayer_ref_redirect`) with the typing read through the
expansion, not an equality of denotations. -/
theorem memo_keys_differ :
    denoteLayer effectRef (.ref [0, 0]) siteQ ⟨0⟩ 0 ≠
      denoteLayer effectRef.expandRefs (.effect key (.succeed (.lit (.nat 7)))) siteQ ⟨0⟩ 0 := by
  intro h
  have keys := congrArg (firstMemoKey 20) h
  rw [run_key, expansion_key] at keys
  cases keys

end Test.Program.LayerRefs
