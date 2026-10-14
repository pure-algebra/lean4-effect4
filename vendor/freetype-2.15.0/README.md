# FreeType 2.15.0, vendored by pin

The glyph rasterizer of the view's player (decisions row 336, point 5; row 380 (1); the visual
pipeline note, section 6). HarfBuzz shapes; FreeType loads the font and draws each glyph.

- source: `https://download.savannah.gnu.org/releases/freetype/`, `freetype-2.15.0.tar.xz`,
  2,716,928 bytes
- SHA-256: `SHA256SUMS`
- signature: one, by Werner Lemberg, checked on 2026-10-14 against the key in `keys/`:
  RSA `E306 7470 7856 409F F194 8010 BE6C 3AAC 63AD 8E3F`, fetched by fingerprint from
  `keyserver.ubuntu.com`
- licence: dual, the FreeType License or GPLv2 (`LICENSE.TXT`, `docs/FTL.TXT`,
  `docs/GPLv2.TXT`, copied from the tarball). This tree takes the FreeType License, whose
  clause asks that the product's documentation credit the FreeType project.

**Why by pin.** The source is 975 files. The tree keeps the pin, the key and `fetch.sh`, which
downloads the tarball and refuses it unless the SHA-256 and the signature hold. A build extracts
the tarball in a temporary folder, keeps the built library, and removes the source.

**The build** is owed: FreeType builds with CMake, which is installed. It lands with the
player's first use of shaped text.

The keyring of `fetch.sh` stands in a short path under `/tmp`: gpg's agent socket refuses a long
one (found 2026-10-09 for SDL3).

Why it fits: it turns a glyph of a font into an outline or a coverage mask; it lays nothing out.
