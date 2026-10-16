/* fixture.h -- the frames that the repository's committed fixtures hold in hexadecimal.

   What it is: a scanner over text files: every token of a non-comment line that is lowercase
   hexadecimal, of even length and at least nine bytes long, is one frame. The fixtures are
   Lean's: ocaml/engine/test/modeled/modeled.txt, ocaml/engine/test/todo/todo-host.txt and
   the .hex files of ocaml/goldens/eff/, each written by a Lean producer that
   docs/GENERATED.md names.
   Depends on: e4val.

   Properties:
   F1  A token that is no frame candidate (a word, a boolean, a short hex word) is skipped, never
       read as a frame.                                             by construction */

#ifndef FIXTURE_H
#define FIXTURE_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
  uint8_t *ptr;
  size_t len;
  char origin[96];   /* file:line */
} fixture_frame;

extern fixture_frame *fixture_frames;
extern size_t fixture_count;

/* Appends the frames of one file; returns how many, or -1 when it cannot be opened. */
long fixture_load(const char *path);
void fixture_free(void);

#endif
