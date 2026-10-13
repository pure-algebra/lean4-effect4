module

/-!
# The cache's independent model

The Lean model of the banked cache (decisions row 378 (6); the block is
`src/Effect4/Library/Ref/Cache.lean`). It is a definition over the cached value and storage's
answers. It imports no program, no step and no machine, as `Ref.Model`
(`src/Effect4/Library/Ref/Model.lean`) does not.

* `make` leaves the cache empty.
* `read` reads through the cache against a tape of storage's answers. A held value is the answer,
  and the read takes no answer from the tape. An empty cache takes the tape's first answer. A
  loaded value is held and answered. A failure is answered, and the cache stays empty. An empty
  tape is the frontier `none`: storage has not answered.
* `invalidate` empties the cache.

The model observes each answer, the cached value after the step, and the tape it leaves unread.
A cache has no waiter, so the wake order is empty.

It transcribes no Effect module. Latest's `Effect.cachedInvalidateWithTTL`
(`vendor/effect-4.0.1/src/internal/effect.ts:4424`, `makeCachedUnsafe` at `:4458`) differs in
three ways. It caches the exit, a failure too. It shares one forked run among concurrent
callers. It takes its loader once, at construction. This cache holds successes only, runs the
loader on the caller's fiber, and takes it at each read, because a stored function waits
(decisions row 340 (2)).

Placement: concept `translation-simulation`, registry claim `ref-cache-agrees`, requirement R10.
The consumer is `cache_agrees` (`src/Effect4/Laws/Library/Ref/Cache.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Ref.Cache.Model

/-- The cache as `make` leaves it: empty. The allocation supplies the cell's identity. -/
def make {L : Type} : Option L := none

/-- **One read through the cache**, at the cached value and a tape of storage's answers: the
answer, the cached value after the read, and the unread tape. A held value reads no answer. An
empty cache reads one: a loaded value is held, and a failure leaves the cache empty. An empty
tape is the frontier `none`. -/
def read {ε L : Type} : Option L → List (Except ε L) →
    Option ((Except ε L × Option L) × List (Except ε L))
  | some held, answers => some ((.ok held, some held), answers)
  | none, [] => none
  | none, .ok loaded :: rest => some ((.ok loaded, some loaded), rest)
  | none, .error e :: rest => some ((.error e, none), rest)

/-- An invalidation empties the cache, whatever it held. -/
def invalidate {L : Type} (_cached : Option L) : Option L := none

end Effect4.Ref.Cache.Model
