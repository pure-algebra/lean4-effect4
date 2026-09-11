import Effect4.Laws.Api.HostSession

#print axioms Effect4.Api.HostSession.start
#print axioms Effect4.Api.HostSession.bindCall
#print axioms Effect4.Api.HostSession.preflight
#print axioms Effect4.Api.HostSession.submit
#print axioms Effect4.Api.HostSession.applyPending
#print axioms Effect4.Api.HostSession.advance
#print axioms Effect4.Api.HostSession.inspect
#print axioms Effect4.Api.HostSession.preflight_envelope
#print axioms Effect4.Api.HostSession.submit_refusal_retains
#print axioms Effect4.Api.HostSession.applyPending_zero
#print axioms Effect4.Api.HostSession.applied_guard_absent
#print axioms Effect4.Api.HostSession.applied_reply_refused
#print axioms Effect4.Api.HostSession.advance_answer_refuses

#print axioms Effect4.Api.HostSession.reply_commute
#print axioms Effect4.Api.HostSession.readReply_store_other
#print axioms Effect4.Api.HostSession.submit_machine
#print axioms Effect4.Api.HostSession.applyReply_conforms
#print axioms Effect4.Api.HostProtocol.hostProtocol

#print axioms Effect4.Api.HostSession.submit_duplicate
#print axioms Effect4.Api.HostSession.submit_key_independence
#print axioms Effect4.Api.HostSession.advance_conforms
#print axioms Effect4.Program.Ty.result
#print axioms Effect4.Program.hasTy_sub
