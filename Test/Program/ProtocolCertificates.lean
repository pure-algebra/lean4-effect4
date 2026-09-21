import Effect4.Laws.Effects.ProtocolObligations

/-! D12 controls use two different certificate families. These are judgments on the
existing free Program; certificates are proof data, not a runtime representation. -/
set_option autoImplicit false
namespace Test.Program.ProtocolCertificates
open _root_.Effects Effect4.Laws.Effects

def order : WorldOrder Nat := ⟨Nat.le, Nat.le_refl, Nat.le_trans⟩
abbrev leftSig : Signature := ⟨Unit, fun _ => Bool⟩
abbrev rightSig : Signature := ⟨Nat, fun _ => Nat⟩

def leftProtocol : Protocol Nat leftSig where
  Cert _ := Bool
  pre _ _ cert := cert = true
  post _ _ cert answer := answer = cert

def rightProtocol : Protocol Nat rightSig where
  Cert _ := Nat
  pre _ op cert := cert = op
  post _ _ cert answer := answer = cert

def request : Program leftSig Bool := .vis () .pure

theorem chosen_certificate : Typed order leftProtocol 0 (fun _ answer => answer = true) request :=
  .vis true rfl (fun _ _ _ post => .pure post)

theorem certificate_pre_refuses : ¬ leftProtocol.pre 0 () false := by
  change ¬ (false = true)
  decide
theorem certificate_post_refuses : ¬ leftProtocol.post 0 () true false := by
  change ¬ (false = true)
  decide

/-- The continuation cannot exchange the precondition's certificate for a different one. -/
theorem exchanged_certificate_refused :
    ¬ Typed order leftProtocol 0 (fun _ answer => answer = false) request := by
  intro typed
  cases typed with
  | vis cert pre continuation =>
    have result : cert = false := Typed.pure_inv (Q := fun (_ : Nat) answer => answer = false)
      (continuation 0 (Nat.le_refl _) cert rfl)
    have impossible : true = false := pre.symm.trans result
    cases impossible

theorem monotone_request : Typed order leftProtocol 12 (fun _ answer => answer = true) request :=
  Typed.mono (fun _ _ _ _ _ h => h) (fun _ _ _ _ h => h) (Nat.zero_le _) chosen_certificate

theorem sequencing : Typed order leftProtocol 0 (fun _ value => value = (7 : Nat))
    (request.bind fun _ => .pure 7) :=
  Typed.bind chosen_certificate (fun _ _ _ => .pure rfl)

theorem widening : Typed order leftProtocol 0 (fun _ _ => True) request :=
  Typed.widen chosen_certificate (fun _ _ _ => True.intro)

theorem sum_left : Typed order (leftProtocol.sum rightProtocol) 0
    (fun _ answer => answer = true) request.inl := Typed.inl chosen_certificate

theorem sum_left_recovers : ∃ cert : Bool, cert = true ∧
    ∀ world, order.le 0 world → ∀ answer, answer = cert →
      Typed order (leftProtocol.sum rightProtocol) world (fun _ a => a = true) (.pure answer) :=
  Typed.inl_inv sum_left

theorem sum_right : Typed order (leftProtocol.sum rightProtocol) 0
    (fun _ answer => answer = (7 : Nat)) (.vis (.inr 7) .pure) :=
  .vis (7 : Nat) rfl (fun _ _ _ post => .pure post)

theorem sum_right_recovers : ∃ cert : Nat, cert = 7 ∧
    ∀ world, order.le 0 world → ∀ answer, answer = cert →
      Typed order (leftProtocol.sum rightProtocol) world (fun _ a => a = 7) (.pure answer) :=
  Typed.inr_inv sum_right

/-- The coproduct's right certificate really is Nat, not the left Bool certificate. -/
example : (leftProtocol.sum rightProtocol).Cert (.inr 7) = Nat := rfl

def plainPre (_ : Nat) (_ : leftSig.Op) : Prop := True
def plainPost (_ : Nat) (_ : leftSig.Op) (answer : Bool) : Prop := answer = true

theorem original_rules : PlainTyped order plainPre plainPost 0
    (fun _ answer => answer = true) request :=
  .vis True.intro (fun _ _ _ post => .pure post)

theorem plain_compatibility : Typed order (Protocol.plain plainPre plainPost) 0
    (fun _ answer => answer = true) request :=
  (Typed.plain_iff _ _ _ _ _ _).mpr original_rules

theorem plain_roundtrip : PlainTyped order plainPre plainPost 0
    (fun _ answer => answer = true) request :=
  (Typed.plain_iff _ _ _ _ _ _).mp plain_compatibility

#print axioms exchanged_certificate_refused
#print axioms monotone_request
#print axioms sum_left_recovers
#print axioms sum_right_recovers
#print axioms plain_roundtrip
end Test.Program.ProtocolCertificates
