# HarfBuzz 14.6.0, vendored by pin

The text shaper of the view's player (decisions row 336, point 5; row 380 (1); the visual
pipeline note, section 6). With FreeType it replaces pango, so the window needs no glib.

- source: `https://github.com/harfbuzz/harfbuzz`, release `14.6.0` (2026-10-05), asset
  `harfbuzz-14.6.0.tar.xz`, 20,295,260 bytes
- SHA-256: `SHA256SUMS`. It was taken from the download of 2026-10-14 and equals the asset digest
  GitHub publishes for the release. HarfBuzz signs no release.
- licence: the "Old MIT" licence (`COPYING`, copied from the tarball)

**Why by pin.** The source is 4,047 files, and it holds its own `AGENTS.md` and `CLAUDE.md`. Inside
this checkout those files would read as instructions to an agent. So the tree keeps the pin and
`fetch.sh`, which downloads the tarball and refuses it unless the SHA-256 holds. A build extracts
the tarball in a temporary folder, keeps the built library, and removes the source.

**The build** is owed: HarfBuzz builds with Meson. It lands with the player's first use of shaped
text.

Why it fits: it turns a string and a font into positioned glyphs; it lays nothing out.
