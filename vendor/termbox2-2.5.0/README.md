# termbox2 2.5.0, vendored

The terminal library of the view's console output (decisions row 336, point 5; the owner's yes of
2026-10-09). One header: define `TB_IMPL` in exactly one C file before including it.

- source: `https://github.com/termbox/termbox2`, tag `v2.5.0`, commit
  `9b5a5da862c06c554148c14fd38d2f796be22d57` (released 2024-12-28)
- files: `termbox2.h` and `LICENSE`, byte for byte at that tag; each file's git blob hash matched
  the tag's on 2026-10-09 (`termbox2.h` `93ec31530bfe6ede0da160cecf8f94f3467c3018`, `LICENSE`
  `0212b7ca7d6a6c5ff7b98e6713f9eefbaf9eb665`)
- licence: MIT (`LICENSE`)
- SHA-256 of each file: `SHA256SUMS` (`shasum -a 256 -c SHA256SUMS`)

Why it fits: it takes cells and answers events as data, and it lays nothing out. The view's page is
already a grid of cells in the data face (`tools/Tools/View/Page.lean`).
