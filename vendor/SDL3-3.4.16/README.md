# SDL3 3.4.16, vendored by pin

The window and input library of the view's player (decisions row 336, point 5; the owner's yes of
2026-10-09). It replaces the SDL2 of the system once it builds here.

- source: `https://github.com/libsdl-org/SDL`, release `release-3.4.16` (2026-09-02; revision
  `release-3.4.16-0-gfa2c02bb6`), asset `SDL3-3.4.16.tar.gz`, 15,640,667 bytes
- SHA-256: `SHA256SUMS`
- signatures: two, both by Sam Lantinga, checked on 2026-10-09 against the keys in `keys/`:
  DSA `1528 635D 8053 A57F 77D1 E086 30A5 9377 A776 3BE6` and
  RSA `0900 1043 63B4 C9D4 223D E149 D913 FE7D 4B61 D39B`, fetched by fingerprint from
  `keyserver.ubuntu.com`
- licence: zlib (`LICENSE.txt`, copied from the tarball)

**Why by pin.** The source is 52 MB in 2,183 files, and it holds its own `AGENTS.md` and
`CLAUDE.md`. Inside this checkout those files would read as instructions to an agent. So the tree
keeps the pin, the keys and `fetch.sh`, which downloads the tarball and refuses it unless the
SHA-256 and both signatures hold. A build extracts the tarball in a temporary folder, keeps the
built library, and removes the source.

**What a build needs.** SDL3 builds with CMake or with its Xcode project. This machine has
neither (2026-10-09), so the build waits for the owner's choice of a build tool.

Why it fits: it answers input as events and presents a picture; it lays nothing out.
