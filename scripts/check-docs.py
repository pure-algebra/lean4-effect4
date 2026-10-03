#!/usr/bin/env python3
"""check-docs: every path, link, citation and make target the authority documents name resolves.

The documents are every tracked Markdown file outside docs/research/ and vendor/. One line per
stale reference, `file:line: kind text (hint)`, exit 1; or a PASS line. `make check-docs` runs it,
keyed on the documents, the Makefile and the tracked-path inventory (scripts/lib/doc_refs.py).
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "lib"))

from doc_refs import doc_files, stale_references  # noqa: E402


def main() -> int:
    stale = stale_references(ROOT)
    documents = len(doc_files(ROOT))
    if stale:
        files = len({s.file for s in stale})
        print(f"FAIL check-docs: {len(stale)} stale reference(s) in {files} of {documents} documents:")
        for item in stale:
            print("  " + item.render())
        return 1
    print(f"PASS check-docs: every path, link, citation and make target in {documents} documents resolves")
    return 0


if __name__ == "__main__":
    sys.exit(main())
