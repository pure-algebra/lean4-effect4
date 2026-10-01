"""Extract the shared definitions block of the membership probes, or check that every probe
carries the same block. The block runs from the `abbrev W` docstring through the line `/-! End of the shared block. -/`."""
import sys, hashlib
START = "/-- The typed world (`Laws/Program/Typed/World.lean:52`). -/\n"
END = "/-! End of the shared block. -/\n"
def block(path):
    s = open(path).read()
    i = s.index(START); j = s.index(END) + len(END)
    return s[i:j]
if sys.argv[1] == "extract":
    sys.stdout.write(block(sys.argv[2]))
elif sys.argv[1] == "check":
    digests = {p: hashlib.sha256(block(p).encode()).hexdigest() for p in sys.argv[2:]}
    for p, d in digests.items(): print(d[:16], p)
    ok = len(set(digests.values())) == 1
    print("prelude identical:", ok)
    sys.exit(0 if ok else 1)
