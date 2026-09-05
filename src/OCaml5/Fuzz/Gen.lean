/-!
# OCaml5.Fuzz.Gen

**What it is.** The pure pseudo-random source every generator of `OCaml5.Fuzz` draws from: `Rng`,
a linear congruential state seeded by `rngOf`, and `Gen`, the state monad over it with `pick` and
`pickOf`. Everything a fuzz lane writes is a function of a seed through this module, so the files
under `fuzz/` are a cache, not a source.

**Depends on.** Nothing outside `Init`.

**Properties.**
* **Deterministic.** The same seed replays the same draws — *by construction* (a pure `StateM`).
* **In range.** `pick n` is below `n`; `pickOf xs dflt` is an element of `xs` or `dflt` — *by
  construction*.
-/

namespace OCaml5.Fuzz

/-! ## A pure PRNG

xorshift64, seeded through a SplitMix-style scramble so that consecutive seeds do not produce
correlated streams. -/

structure Rng where
  s : UInt64
deriving Repr

/-- A stream from a seed. The state is forced non-zero, which xorshift requires. -/
def rngOf (seed : Nat) : Rng :=
  let x := seed.toUInt64 ^^^ 0x9e3779b97f4a7c15
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  ⟨(x ^^^ (x >>> 31)) ||| 1⟩

def Rng.bump (r : Rng) : Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  ⟨x ^^^ (x <<< 17)⟩

abbrev Gen := StateM Rng

/-- A uniform-enough `Nat` below `n`; `pick 0 = 0`. -/
def pick (n : Nat) : Gen Nat := fun r =>
  let r' := r.bump
  (if n == 0 then 0 else (r'.s >>> 17).toNat % n, r')

/-- One element of a list, or a default. -/
def pickOf (xs : List Nat) (dflt : Nat) : Gen Nat := do
  if xs.isEmpty then return dflt
  let i ← pick xs.length
  return (xs.getD i dflt)

end OCaml5.Fuzz
