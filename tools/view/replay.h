/* replay.h: replay a stream of device calls onto a new image surface, and decide nothing.
 *
 * The stream is the lowest form of a picture that Lean writes (tools/Tools/View/Picture.lean,
 * `stream`). One row is one call of paint.h; a row that draws ends with the key of its object:
 *
 *   P width height ratio paper hue   the target: logical pixels and the ratio, in thousandths
 *   F role value x0 y0 x1 y1 key     a fill of whole device pixels
 *   C x baseline max scale text key  a text of the data face in a room of cells
 *   T face x baseline max scale text key  a text of another face in a room of pixels
 *   K x y w h                        a cut to a box, until the next `k`
 *   k                                the end of the cut
 *   H key x0 y0 x1 y1                the device box that answers a pointer with a key; not drawn
 *
 * This header holds no layout, no rule of a page and no meaning of a role beyond the tokens.
 * Its users: draw.c (a picture to PNG, the key under a pixel) and play.c (a window).
 */
#ifndef EFFECT4_REPLAY_H
#define EFFECT4_REPLAY_H

#include <cairo.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "paint.h"

/* Split a row at its tabs, in place: at most `most` fields. */
static inline int replay_fields(char *line, char **f, int most) {
  int n = 0;
  f[n++] = line;
  for (char *c = line; *c && n < most; c++) if (*c == '\t') { *c = 0; f[n++] = c + 1; }
  return n;
}

/* A field in thousandths, as a number. */
static inline double replay_milli(const char *s) { return (double)atol(s) / 1000.0; }

/* The target of a stream: its first row, `P width height ratio paper hue`. Answers 1 and sets
 * the logical size and the ratio, or 0 when the file does not open or its first row is no
 * target. */
static inline int replay_target(const char *path, double *W, double *H, double *ratio) {
  FILE *fp = fopen(path, "r");
  if (!fp) return 0;
  char *line = NULL; size_t cap = 0; ssize_t len = getline(&line, &cap, fp);
  int ok = 0;
  if (len > 0 && line[0] == 'P') {
    char *f[8]; int n = replay_fields(line, f, 8);
    if (n >= 4) { *W = replay_milli(f[1]); *H = replay_milli(f[2]); *ratio = replay_milli(f[3]); ok = 1; }
  }
  free(line); fclose(fp);
  return ok;
}

/* Paint the stream at `path` on a new image surface of its target's device size. Answers the
 * surface, or NULL when the file does not open or has no target row. `*bad` counts the rows
 * that are no call and the cuts that stay open. The caller destroys the surface. */
static inline cairo_surface_t *replay_stream(const char *path, const PaintFaces *faces, int *bad) {
  *bad = 0;
  FILE *fp = fopen(path, "r");
  if (!fp) return NULL;
  cairo_surface_t *surface = NULL; cairo_t *cr = NULL; Paint p; memset(&p, 0, sizeof p);
  int cuts = 0;
  char *line = NULL; size_t cap = 0; ssize_t len;
  while ((len = getline(&line, &cap, fp)) > 0) {
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
    if (!len) continue;
    char *f[13]; int n = replay_fields(line, f, 13);
    char k = f[0][0];
    if (k == 'P' && n >= 6 && !cr) {
      double W = replay_milli(f[1]), H = replay_milli(f[2]), ratio = replay_milli(f[3]);
      surface = cairo_image_surface_create(CAIRO_FORMAT_ARGB32, (int)(ratio * W), (int)(ratio * H));
      cr = cairo_create(surface);
      paint_open(&p, cr, ratio, atoi(f[4]) ? &PAINT_PAPER : &PAINT_DARK, faces, atoi(f[5]));
    } else if (!cr) (*bad)++;
    else if (k == 'H') { /* a pointer box: not drawn */ }
    else if (k == 'F' && n >= 7) paint_device_fill(&p, paint_tone((PaintRole)atoi(f[1]), replay_milli(f[2])), atol(f[3]), atol(f[4]), atol(f[5]), atol(f[6]));
    else if (k == 'B' && n >= 11) {
      long pt[8];
      for (int i = 0; i < 8; i++) pt[i] = atol(f[3 + i]);
      paint_device_curve(&p, paint_tone((PaintRole)atoi(f[1]), 1.0), atol(f[2]), pt);
    }
    else if (k == 'C' && n >= 6) paint_cells(&p, replay_milli(f[1]), replay_milli(f[2]), f[5], atoi(f[3]), replay_milli(f[4]));
    else if (k == 'T' && n >= 7) paint_text(&p, (PaintFace)atoi(f[1]), replay_milli(f[2]), replay_milli(f[3]), f[6], replay_milli(f[4]), replay_milli(f[5]));
    else if (k == 'K' && n >= 5) { paint_cut(&p, replay_milli(f[1]), replay_milli(f[2]), replay_milli(f[3]), replay_milli(f[4])); cuts++; }
    else if (k == 'k' && cuts > 0) { paint_uncut(&p); cuts--; }
    else (*bad)++;
  }
  free(line); fclose(fp);
  if (cr) { paint_close(&p); cairo_destroy(cr); }
  *bad += cuts;
  return surface;
}

#endif
