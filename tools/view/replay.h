/* replay.h: replay a stream of device calls onto a new image surface, and decide nothing.
 *
 * The stream is the lowest form of a picture that Lean writes (tools/Tools/View/Output.lean,
 * `stream`). It opens with its target and its look; then one row is one call of paint.h, and a
 * row that draws ends with the key of its object:
 *
 *   P width height ratio light hue step   the target: logical pixels and the ratio, in
 *                                    thousandths; whether the look is light; whether an agent
 *                                    takes its hue; the milliseconds of one step of motion
 *   R role rrggbb                    the colour of a role in the look
 *   Y face size weight italic families   a face of the look; its size in thousandths of a
 *                                    logical pixel (the data face's is measured from the cell)
 *   F role value x0 y0 x1 y1 key     a fill of whole device pixels
 *   B role weight x0 y0 x1 y1 x2 y2 x3 y3 key   a stroke along a cubic segment
 *   C x baseline max scale text key  a text of the data face in a room of cells
 *   T face x baseline max scale text key  a text of another face in a room of pixels
 *   K x y w h                        a cut to a box, until the next `k`
 *   k                                the end of the cut
 *   H key x0 y0 x1 y1                the device box that answers a pointer with a key; not drawn
 *
 * This header holds no layout, no rule of a page, no colour and no face: the look is the
 * stream's. Its users: draw.c (a picture to PNG, the key under a pixel) and play.c (a window).
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

/* What a replay keeps from one picture to the next: the look's colours and faces. The faces are
 * opened again only when a stream names other faces, since opening them measures the data face. */
typedef struct Replay {
  PaintTokens tokens;
  PaintFaceSpec spec[PAINT_FACE_COUNT];
  PaintFaces faces;
  int open;      /* whether `faces` are open for `spec` */
  int hue;       /* the hue of the last target */
  double step;   /* the milliseconds of one step of motion, from the last target */
} Replay;

/* Close what a replay opened. */
static inline void replay_close(Replay *rp) {
  if (rp->open) paint_faces_close(&rp->faces);
  memset(rp, 0, sizeof *rp);
}

/* A colour from six hexadecimal digits. */
static inline uint32_t replay_hex(const char *s) { return (uint32_t)strtoul(s, NULL, 16); }

/* Take a look's row, `R` or `Y`, into the replay. Answers 0 when the row is malformed. */
static inline int replay_look_row(Replay *rp, PaintFaceSpec *spec, char **f, int n) {
  if (f[0][0] == 'R' && n >= 3) {
    const uint32_t c = replay_hex(f[2]);
    switch (atoi(f[1])) {
    case PAINT_GROUND: rp->tokens.ground = c; break;
    case PAINT_INK: rp->tokens.ink = c; break;
    case PAINT_RULE: rp->tokens.rule = c; break;
    case PAINT_HOST: rp->tokens.host = c; break;
    case PAINT_FAILURE: rp->tokens.failure = c; break;
    case PAINT_RESOURCE: rp->tokens.resource = c; break;
    default: return 0;
    }
    return 1;
  }
  if (f[0][0] == 'Y' && n >= 6) {
    const int face = atoi(f[1]);
    if (face < 0 || face >= PAINT_FACE_COUNT) return 0;
    PaintFaceSpec *sp = &spec[face];
    sp->px = replay_milli(f[2]);
    sp->weight = atoi(f[3]);
    sp->italic = atoi(f[4]);
    snprintf(sp->family, sizeof sp->family, "%s", f[5]);
    return 1;
  }
  return 0;
}

/* Paint the stream at `path` on a new image surface of its target's device size, in the look its
 * rows name. Answers the surface, or NULL when the file does not open, has no target row, or its
 * faces do not open. `*bad` counts the rows that are no call and the cuts that stay open. The
 * caller destroys the surface, and closes the replay when it is done with every picture. */
static inline cairo_surface_t *replay_stream(const char *path, Replay *rp, int *bad) {
  *bad = 0;
  FILE *fp = fopen(path, "r");
  if (!fp) return NULL;
  cairo_surface_t *surface = NULL; cairo_t *cr = NULL; Paint p; memset(&p, 0, sizeof p);
  PaintFaceSpec spec[PAINT_FACE_COUNT];
  memcpy(spec, rp->spec, sizeof spec);
  int cuts = 0, painting = 0, failed = 0;
  double ratio = 1;
  char *line = NULL; size_t cap = 0; ssize_t len;
  while ((len = getline(&line, &cap, fp)) > 0) {
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
    if (!len) continue;
    char *f[13]; int n = replay_fields(line, f, 13);
    char k = f[0][0];
    if (k == 'P' && n >= 6 && !cr) {
      double W = replay_milli(f[1]), H = replay_milli(f[2]);
      ratio = replay_milli(f[3]);
      rp->hue = atoi(f[5]);
      rp->step = n >= 7 ? atof(f[6]) : 0.0;
      surface = cairo_image_surface_create(CAIRO_FORMAT_ARGB32, (int)(ratio * W), (int)(ratio * H));
      cr = cairo_create(surface);
      continue;
    }
    if (!cr) { (*bad)++; continue; }
    if (k == 'R' || k == 'Y') {
      if (painting || !replay_look_row(rp, spec, f, n)) (*bad)++;
      continue;
    }
    if (!painting) {   /* the first call that draws: the look is whole */
      if (!rp->open || memcmp(spec, rp->spec, sizeof spec)) {
        if (rp->open) paint_faces_close(&rp->faces);
        memcpy(rp->spec, spec, sizeof spec);
        rp->open = paint_faces_open(&rp->faces, rp->spec);
        if (!rp->open) { failed = 1; break; }
      }
      paint_open(&p, cr, ratio, &rp->tokens, &rp->faces, rp->hue);
      painting = 1;
    }
    if (k == 'H') { /* a pointer box: not drawn */ }
    else if (k == 'F' && n >= 7) paint_device_fill(&p, paint_tone((PaintRole)atoi(f[1]), replay_milli(f[2])), atol(f[3]), atol(f[4]), atol(f[5]), atol(f[6]));
    else if (k == 'B' && n >= 11) {
      long pt[8];
      for (int i = 0; i < 8; i++) pt[i] = atol(f[3 + i]);
      paint_device_curve(&p, paint_tone((PaintRole)atoi(f[1]), 1.0), atol(f[2]), pt);
    }
    else if (k == 'S' && n >= 5) paint_device_shape(&p, paint_tone((PaintRole)atoi(f[1]), replay_milli(f[2])), n - 4, &f[3]);
    else if (k == 'C' && n >= 6) paint_cells(&p, replay_milli(f[1]), replay_milli(f[2]), f[5], atoi(f[3]), replay_milli(f[4]));
    else if (k == 'T' && n >= 7) paint_text(&p, (PaintFace)atoi(f[1]), replay_milli(f[2]), replay_milli(f[3]), f[6], replay_milli(f[4]), replay_milli(f[5]));
    else if (k == 'K' && n >= 5) { paint_cut(&p, replay_milli(f[1]), replay_milli(f[2]), replay_milli(f[3]), replay_milli(f[4])); cuts++; }
    else if (k == 'k' && cuts > 0) { paint_uncut(&p); cuts--; }
    else (*bad)++;
  }
  free(line); fclose(fp);
  if (painting) paint_close(&p);
  if (cr) cairo_destroy(cr);
  if (failed && surface) { cairo_surface_destroy(surface); surface = NULL; }
  *bad += cuts;
  return surface;
}

#endif
