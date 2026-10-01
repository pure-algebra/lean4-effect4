import Effect4.Api
namespace AuditR11
open Effect4 Effect4.Machine Effect4.Program
def blockedCleanup : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.perform .deferredMake (.lit .unit))
      (.scoped (.bind
        (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))
        (.acquireRelease (.succeed (.lit .unit)) (.exit (.perform .deferredAwait (.var 1)))))))
#guard (Api.typeOf blockedCleanup).isSome
#guard (Api.run blockedCleanup 500).outcome = .frontier
#guard (Api.run blockedCleanup 500).machine.state.refs = [Val.nat 0]
#guard (Api.run blockedCleanup 500).machine.state.scopes.entries.any (fun e => e.scope.isClosed)
end AuditR11
