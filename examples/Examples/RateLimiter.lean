import Effect4.Author
import Effect4.Library.Semaphore.Ops
import Effect4.Program.Authoring.Application

/-!
# A rate limiter: at most two quote requests in flight, and a request over the limit is refused

The limiter is the library's Semaphore (`Effect4.Semaphore`) with two permits. A request holds
one permit while it waits on the clock and asks the quote service, and gives it back at every
exit. A request that finds no free permit does not wait: it answers no quote. `quotes(a, b, c)`
sends three requests at once and answers the three results.
-/

set_option autoImplicit false

namespace Examples.RateLimiter

open Effect4 Effect4.Program Effect4.Program.Authoring

/-! ## The quote service -/

eff_failure QuoteError message

/-- The quote service's key. -/
def quotesKey : ServiceKey := ⟨⟨33⟩, ⟨6⟩⟩

eff_rows Quotes key quotesKey error QuoteError.ty cite "the rate limiter" where
  fetch(.string) : .nat

/-! ## The limiter -/

/-- The permits of the limiter. -/
def limit : Nat := 2

/-- One request through the limiter: with a permit, wait 10 ms and ask for the symbol's quote;
without one, answer none. -/
def limited (limiter symbol : TermSrc) : Src NativeOp :=
  Semaphore.withPermitsIfAvailable limiter (nat 1)
    (andThen (Effect.sleep (nat 10)) (Quotes.fetch symbol))

/-- `quotes(a, b, c)`: three requests at once through one limiter. -/
def quotes (a b c : TermSrc) : Src NativeOp := eff do
  let limiter ← Semaphore.make limit
  let first ← fork (limited limiter a)
  let second ← fork (limited limiter b)
  let third ← fork (limited limiter c)
  let x ← join first
  let y ← join second
  let z ← join third
  return tuple [x, y, z]

/-! ## The application -/

/-- The limited quote service: the quote row and one entry. -/
def application : Application NativeOp :=
  { name := "rateLimiter"
    rows := Quotes.rows
    entries :=
      [ { name := "quotes", params := [("a", .string), ("b", .string), ("c", .string)]
          body := quotes (var "a") (var "b") (var "c") } ] }

end Examples.RateLimiter
