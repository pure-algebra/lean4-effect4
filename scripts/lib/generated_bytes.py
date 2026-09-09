"""Compare complete projections, excluding only the informational stamp revision."""

import re
import sys
from pathlib import Path

STAMP = re.compile(
    rb"(?m)^(?P<prefix>// |-- |\(\* |<!-- |)?cut-from: rev=[^\s]+"
    rb"(?P<rest> toolchain=[^\r\n]+ inputs=[0-9a-f]{64})(?P<suffix> \*\)| -->)?$"
)


def comparable(data: bytes) -> bytes:
    return STAMP.sub(lambda m: (m["prefix"] or b"") + b"cut-from: rev=<informational>"
                     + m["rest"] + (m["suffix"] or b""), data)


if __name__ == "__main__":
    left, right = (Path(p).read_bytes() for p in sys.argv[1:])
    raise SystemExit(0 if comparable(left) == comparable(right) else 1)
