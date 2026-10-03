import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Auto.Obligations

/-! D12's declaration-backed proof ledger for D12's laws of `Laws/Effects/Protocol.lean` (the
protocol-typed predicate's original obligations; the generic laws seat E landed there on
2026-10-01, `Typed.inr`, `Typed.inl_iff`, `Typed.inr_iff` and `Typed.refine`, are proved outside
this ledger and owe their consumer, C4 for `TypedProg`, under decisions row 148). The
registrations sit here, beside the ledger's users, so the generic Protocol module and its
area import only the pinned `Effects` (moved from `Laws/Effects/` on 2026-09-23). -/
set_option autoImplicit false
namespace Effect4.Laws.Effects.D12
open _root_.Effects
universe u v w
variable {W : Type w} {S : Signature.{u, v}} {A : Type v}

end Effect4.Laws.Effects.D12
