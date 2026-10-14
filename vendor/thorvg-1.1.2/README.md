# ThorVG 1.1.2, vendored by pin

The vector renderer of the view's player (decisions row 336, point 5; row 380 (1); the visual
pipeline note, section 6). It plays the SVG the view writes and Lottie exports, through its C
interface.

- source: `https://github.com/thorvg/thorvg`, release `v1.1.2` (2026-09-18), asset
  `thorvg-1.1.2.tar.xz`, 2,949,132 bytes
- SHA-256: `SHA256SUMS`. It was taken from the download of 2026-10-14 and equals the asset digest
  GitHub publishes for the release. ThorVG signs no release.
- licence: MIT (`LICENSE`, copied from the tarball)

**Why by pin.** The source is 890 files. The tree keeps the pin and `fetch.sh`, which downloads
the tarball and refuses it unless the SHA-256 holds. A build extracts the tarball in a temporary
folder, keeps the built library, and removes the source.

**The build** is owed: ThorVG builds with Meson. It lands with the player's first SVG playback.

Why it fits: it draws paths, fills, strokes and their animation from a scene it is given; it lays
nothing out.
