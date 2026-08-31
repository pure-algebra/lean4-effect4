import Cas.Codec.Nat32
import Cas.Core.Node

/-!
# SHA-256 — the executable FIPS 180-4 specification

Pure `BitVec`-valued mathematics that reads as the standard, so the
digest the vector lane runs is a transcription, not an invention. The
per-block pipeline (Boolean functions, sigmas, constants, schedule,
compression) is transcribed from lambdaclass/concrete
`Concrete/Proof/Sha256Spec.lean` (Apache-2.0, commit `28a25a4e2`),
itself a FIPS 180-4 § 4–6 transcription; the padding and multi-block
`hash` are completed here per § 5.1.1/§ 6.2, and the byte views reuse
this package's proved `nat32`/`nat64` encoders.

Nothing here is proved beyond the output width (which `Addr32`
requires); the known-answer guards at the bottom run the NIST vectors
at build time through the interpreter. Refinement proofs against this
spec are future work, exactly as in the source's proof ladder.
-/

namespace Cas.Sha256

/-- A SHA-256 word. -/
abbrev W := BitVec 32

/-! ## Boolean functions and sigmas (FIPS 180-4 § 4.1.2) -/

def ch (x y z : W) : W := (x &&& y) ^^^ ((~~~x) &&& z)

def maj (x y z : W) : W := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Circular right rotation by `n` (`0 < n < 32`). -/
def rotr (x : W) (n : Nat) : W := (x >>> n) ||| (x <<< (32 - n))

def bigSigma0 (x : W) : W := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bigSigma1 (x : W) : W := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def smallSigma0 (x : W) : W := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def smallSigma1 (x : W) : W := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-! ## Constants (FIPS 180-4 § 4.2.2, § 5.3.3) -/

/-- Round constants K[0..63]. -/
def k : List W :=
  [0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
   0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
   0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
   0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
   0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
   0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
   0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
   0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
   0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
   0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
   0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
   0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
   0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
   0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
   0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
   0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32]

/-- The working state: eight words. -/
structure St where
  a : W
  b : W
  c : W
  d : W
  e : W
  f : W
  g : W
  h : W

/-- Initial hash value H(0). -/
def initSt : St :=
  ⟨0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
   0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32⟩

/-! ## Padding and block structure (FIPS 180-4 § 5.1.1, § 5.2.1) -/

/-- Pad: append `0x80`, zeros to 56 mod 64, and the 64-bit bit length. -/
def pad (msg : Bytes) : Bytes :=
  msg ++ (0x80 :: List.replicate ((119 - (msg.length % 64)) % 64) 0)
    ++ nat64 (8 * msg.length)

/-- Split into 64-byte blocks. Total on every input; called on padded
input only, where the split is exact. -/
def toBlocks (b : Bytes) : List Bytes :=
  if h : b = [] then []
  else
    have : b.length - 64 < b.length := by
      have : 0 < b.length := List.length_pos_iff.mpr h
      omega
    b.take 64 :: toBlocks (b.drop 64)
termination_by b.length
decreasing_by simpa [List.length_drop] using this

/-- Big-endian words of one block (§ 6.2.2 step 1). -/
def toWords (b : Bytes) : List W :=
  if h : b = [] then []
  else
    have : b.length - 4 < b.length := by
      have : 0 < b.length := List.length_pos_iff.mpr h
      omega
    BitVec.ofNat 32
      ((b.getD 0 0).toNat * 0x1000000 + (b.getD 1 0).toNat * 0x10000
        + (b.getD 2 0).toNat * 0x100 + (b.getD 3 0).toNat)
      :: toWords (b.drop 4)
termination_by b.length
decreasing_by simpa [List.length_drop] using this

/-- Message-schedule expansion W[0..63] (§ 6.2.2 step 1). -/
def schedule (ws : List W) : Array W := Id.run do
  let mut arr : Array W := #[]
  for i in [0:64] do
    arr :=
      if i < 16 then arr.push (ws.getD i 0)
      else arr.push (smallSigma1 (arr.getD (i - 2) 0) + arr.getD (i - 7) 0
        + smallSigma0 (arr.getD (i - 15) 0) + arr.getD (i - 16) 0)
  return arr

/-- One compression round (§ 6.2.2 step 3). -/
def round (st : St) (ki wi : W) : St :=
  let t1 := st.h + bigSigma1 st.e + ch st.e st.f st.g + ki + wi
  let t2 := bigSigma0 st.a + maj st.a st.b st.c
  ⟨t1 + t2, st.a, st.b, st.c, st.d + t1, st.e, st.f, st.g⟩

/-- Compress one block into the state (§ 6.2.2 steps 1–4). -/
def compress (st : St) (block : Bytes) : St :=
  let ws := schedule (toWords block)
  let f := (List.range 64).foldl
    (fun s i => round s (k.getD i 0) (ws.getD i 0)) st
  ⟨st.a + f.a, st.b + f.b, st.c + f.c, st.d + f.d,
   st.e + f.e, st.f + f.f, st.g + f.g, st.h + f.h⟩

/-- SHA-256 of a byte string: 32 digest bytes. -/
def sha256 (msg : Bytes) : Bytes :=
  let fin := (toBlocks (pad msg)).foldl compress initSt
  nat32 fin.a.toNat ++ nat32 fin.b.toNat ++ nat32 fin.c.toNat
    ++ nat32 fin.d.toNat ++ nat32 fin.e.toNat ++ nat32 fin.f.toNat
    ++ nat32 fin.g.toNat ++ nat32 fin.h.toNat

theorem sha256_length (msg : Bytes) : (sha256 msg).length = 32 := by
  simp [sha256, nat32]

end Cas.Sha256

namespace Cas

/-- The production address function: scheme-0 SHA-256 over the
canonical pre-image — the digest the vector lane runs. -/
def sha256Addr (pre : Bytes) : Addr32 :=
  ⟨Sha256.sha256 pre, Sha256.sha256_length pre⟩

end Cas

namespace Cas.Sha256

/-! ## Known-answer guards — NIST FIPS 180-4 example vectors, run at
build time through the interpreter (kernel reduction is not asked to
evaluate a digest). -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (bs : Bytes) : String :=
  String.ofList (bs.flatMap fun b =>
    [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def kat (input expected : String) : IO Unit := do
  let got := hex (sha256 input.toUTF8.toList)
  unless got == expected do
    throw (IO.userError s!"SHA-256 KAT failed on {repr input}: {got}")

#eval do
  kat "abc"
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  kat ""
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  kat "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

end Cas.Sha256
