import Test.Program.ProtocolCertificates

/-!
# The protocol layer's right lift, conservativity and order: controls

Controls for the laws seat E landed in `src/Effect4/Laws/Effects/Protocol.lean` on 2026-10-01:
the right lift `Typed.inr` (formal pass, algebra note A5, probe `P6ProtocolLaws.lean`), the
conservativity of both injections `Typed.inl_iff`/`Typed.inr_iff` (model probe, pedigree seat,
`Conservativity.lean`), and monotonicity in the protocol order `Typed.refine` along
`Protocol.Le` (P6). The red controls show that each half of the order is needed: a protocol that
promises less (`promise_needed`, the pedigree's `post_refinement_needed`) or demands more
(`demand_needed`, its verifier's `pre_refinement_needed`) loses a typing the order would carry.
The fixtures are the certificate battery's (`Test/Program/ProtocolCertificates.lean`).
-/

set_option autoImplicit false
namespace Test.Program.ProtocolLaws
open _root_.Effects Effect4.Laws.Effects Test.Program.ProtocolCertificates

/-- One right operation answering its certificate. -/
abbrev rightRequest : Program rightSig Nat := .vis (7 : Nat) .pure

theorem right_typed : Typed order rightProtocol 0 (fun _ answer => answer = (7 : Nat))
    rightRequest :=
  .vis (7 : Nat) rfl (fun _ _ _ post => .pure post)

/-- The right lift: typed for its own protocol, typed for the sum once injected. -/
theorem right_lift : Typed order (leftProtocol.sum rightProtocol) 0
    (fun _ answer => answer = (7 : Nat)) (rightRequest.inr (S := leftSig)) :=
  Typed.inr right_typed

/-- Conservativity, both sides: the sum's typing of an injected program gives back its own. -/
theorem left_reflects : Typed order leftProtocol 0 (fun _ answer => answer = true) request :=
  (Typed.inl_iff request 0).mp sum_left

theorem right_reflects : Typed order rightProtocol 0 (fun _ answer => answer = (7 : Nat))
    rightRequest :=
  (Typed.inr_iff rightRequest 0).mp right_lift

/-- A refusal on one side is a refusal in the sum: the exchanged certificate stays refused
after injection, by the reflection half of `Typed.inl_iff`. -/
theorem exchanged_certificate_refused_in_sum :
    ¬ Typed order (leftProtocol.sum rightProtocol) 0 (fun _ answer => answer = false)
      request.inl :=
  fun typed => exchanged_certificate_refused ((Typed.inl_iff request 0).mp typed)

/-! ## The protocol order -/

/-- Demands nothing, promises what `leftProtocol` promises. -/
def leftLoose : Protocol Nat leftSig where
  Cert _ := Bool
  pre _ _ _ := True
  post _ _ cert answer := answer = cert

/-- `leftProtocol ≤ leftLoose`: the same certificates, a weaker demand, the same promise. -/
def leftBelowLoose : leftProtocol.Le leftLoose :=
  ⟨fun _ cert => cert, fun _ _ _ _ => trivial, fun _ _ _ _ post => post⟩

theorem refined : Typed order leftLoose 0 (fun _ answer => answer = true) request :=
  Typed.refine leftBelowLoose chosen_certificate

/-- Promises nothing about the answer. -/
def leftSilent : Protocol Nat leftSig where
  Cert _ := Bool
  pre _ _ cert := cert = true
  post _ _ _ _ := True

/-- Demands what no world gives. -/
def leftStrict : Protocol Nat leftSig where
  Cert _ := Bool
  pre _ _ _ := False
  post _ _ cert answer := answer = cert

/-- **Red control: the order's promise half is needed.** `leftSilent` promises less than
`leftProtocol`, and the typing at `answer = true` does not carry over. -/
theorem promise_needed :
    (¬ ∀ answer, leftSilent.post 0 () true answer → leftProtocol.post 0 () true answer) ∧
    Typed order leftProtocol 0 (fun _ answer => answer = true) request ∧
    ¬ Typed order leftSilent 0 (fun _ answer => answer = true) request := by
  refine ⟨fun promise => ?_, chosen_certificate, fun typed => ?_⟩
  · have impossible : false = true := promise false trivial
    cases impossible
  · cases typed with
    | vis cert _ next =>
      have impossible : false = true :=
        Typed.pure_inv (Q := fun (_ : Nat) answer => answer = true)
          (next 0 (Nat.le_refl 0) false trivial)
      cases impossible

/-- **Red control: the order's demand half is needed.** `leftStrict` demands more than
`leftProtocol`, and the typing does not carry over. -/
theorem demand_needed :
    (¬ ∀ cert, leftProtocol.pre 0 () cert → leftStrict.pre 0 () cert) ∧
    Typed order leftProtocol 0 (fun _ answer => answer = true) request ∧
    ¬ Typed order leftStrict 0 (fun _ answer => answer = true) request := by
  refine ⟨fun demand => demand true rfl, chosen_certificate, fun typed => ?_⟩
  cases typed with
  | vis _ pre _ => exact pre

/-! **Red control: the order refuses a weaker promise.** The identity certificate map cannot
place `leftSilent` above `leftProtocol`: its promise (`True`) does not give back `answer = cert`. -/

/--
error: Type mismatch
  promise
has type
  leftSilent.post x✝³ x✝² x✝¹ x✝
but is expected to have type
  leftProtocol.post x✝³ x✝² x✝¹ x✝
-/
#guard_msgs (error) in
example : leftProtocol.Le leftSilent :=
  ⟨fun _ cert => cert, fun _ _ _ demand => demand, fun _ _ _ _ promise => promise⟩

#print axioms right_lift
#print axioms left_reflects
#print axioms right_reflects
#print axioms exchanged_certificate_refused_in_sum
#print axioms refined
#print axioms promise_needed
#print axioms demand_needed
end Test.Program.ProtocolLaws
