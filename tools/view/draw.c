/* draw.c: replay a stream of drawing calls, and decide nothing (tools/view, from the native view
 * probe of 2026-10-07; docs/research/2026-10-09-visual-pipeline.md).
 *
 * The stream is the lowest form of a page that Lean writes (tools/Tools/View/Picture.lean,
 * `stream`). One row is one call of paint.h; a row that draws ends with the key of its object:
 *
 *   P width height ratio paper hue   the target: logical pixels and the ratio, in thousandths
 *   F role value x0 y0 x1 y1         a fill of whole device pixels
 *   C x baseline max scale text      a text of the data face in a room of cells
 *   T face x baseline max scale text a text of another face in a room of pixels
 *   K x y w h                        a cut to a box, until the next `k`
 *   k                                the end of the cut
 *   H key x0 y0 x1 y1                the device box that answers a pointer with a key; not drawn
 *
 * This program holds no layout, no rule of a page and no meaning of a role beyond the tokens.
 * It answers 0 when every row is a call that it knows and every cut is closed.
 *
 *   draw STREAM --png FILE           paint the stream
 *   draw STREAM --pick X Y           the key under a device pixel, by the stream's `H` rows
 *   draw STREAM --picks FILE         the key under each device pixel of a file of points
 *   draw STREAM --count              the rows of each kind
 */
#define _GNU_SOURCE
#include <cairo.h>
#include <pango/pangocairo.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "paint.h"

static int fields(char *line, char **f, int most) {
  int n = 0;
  f[n++] = line;
  for (char *c = line; *c && n < most; c++) if (*c == '\t') { *c = 0; f[n++] = c + 1; }
  return n;
}
static double milli(const char *s) { return (double)atol(s) / 1000.0; }

int main(int argc, char **argv) {
  const char *png = NULL, *picks = NULL; int count = 0, pick = 0; long px = 0, py = 0;
  if (argc < 3) { fprintf(stderr, "usage: draw STREAM (--png FILE | --pick X Y | --count)\n"); return 2; }
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--png") && i + 1 < argc) png = argv[++i];
    else if (!strcmp(argv[i], "--pick") && i + 2 < argc) { pick = 1; px = atol(argv[++i]); py = atol(argv[++i]); }
    else if (!strcmp(argv[i], "--count")) count = 1;
    else if (!strcmp(argv[i], "--picks") && i + 1 < argc) picks = argv[++i];
    else { fprintf(stderr, "draw: no flag %s\n", argv[i]); return 2; }
  }
  if (picks) {                           /* a file of device pixels: the key under each */
    FILE *pf = fopen(picks, "r"); long x, y;
    if (!pf) { perror(picks); return 1; }
    while (fscanf(pf, "%ld %ld", &x, &y) == 2) {
      FILE *sf = fopen(argv[1], "r"); char *row = NULL; size_t rcap = 0; ssize_t rlen; char key[256] = "";
      if (!sf) { perror(argv[1]); return 1; }
      while ((rlen = getline(&row, &rcap, sf)) > 0) {
        if (row[0] != 'H') continue;
        while (rlen > 0 && (row[rlen - 1] == '\n' || row[rlen - 1] == '\r')) row[--rlen] = 0;
        char *f[8]; int n = fields(row, f, 8);
        if (n >= 6 && x >= atol(f[2]) && x < atol(f[4]) && y >= atol(f[3]) && y < atol(f[5])) snprintf(key, sizeof key, "%s", f[1]);
      }
      free(row); fclose(sf);
      printf("%s\n", key);
    }
    fclose(pf);
    return 0;
  }
  FILE *fp = fopen(argv[1], "r");
  if (!fp) { perror(argv[1]); return 1; }

  PaintFaces faces; Paint p; memset(&p, 0, sizeof p);
  cairo_surface_t *surface = NULL; cairo_t *cr = NULL;
  long kinds[128] = {0}; int cuts = 0, open = 0, bad = 0;
  char picked[256] = "";
  char *line = NULL; size_t cap = 0; ssize_t len;
  while ((len = getline(&line, &cap, fp)) > 0) {
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
    if (!len) continue;
    char *f[8]; int n = fields(line, f, 8);
    char k = f[0][0];
    kinds[(unsigned char)k & 127]++;
    if (k == 'P' && n >= 6 && !open) {
      double W = milli(f[1]), H = milli(f[2]), ratio = milli(f[3]);
      if (!pick && !count) {
        if (!paint_faces_open(&faces)) { fprintf(stderr, "draw: a face does not open\n"); return 1; }
        surface = cairo_image_surface_create(CAIRO_FORMAT_ARGB32, (int)(ratio * W), (int)(ratio * H));
        cr = cairo_create(surface);
        paint_open(&p, cr, ratio, atoi(f[4]) ? &PAINT_PAPER : &PAINT_DARK, &faces, atoi(f[5]));
      }
      open = 1;
    } else if (!open) bad++;
    else if (k == 'H' && n >= 6) {              /* the last box that holds the pixel answers */
      if (pick && px >= atol(f[2]) && px < atol(f[4]) && py >= atol(f[3]) && py < atol(f[5])) snprintf(picked, sizeof picked, "%s", f[1]);
    } else if (pick || count) {
      if (k == 'K') cuts++; else if (k == 'k') cuts--;
      else if (!strchr("FCT", k)) bad++;
    }
    else if (k == 'F' && n >= 7) paint_device_fill(&p, paint_tone((PaintRole)atoi(f[1]), milli(f[2])), atol(f[3]), atol(f[4]), atol(f[5]), atol(f[6]));
    else if (k == 'C' && n >= 6) paint_cells(&p, milli(f[1]), milli(f[2]), f[5], atoi(f[3]), milli(f[4]));
    else if (k == 'T' && n >= 7) paint_text(&p, (PaintFace)atoi(f[1]), milli(f[2]), milli(f[3]), f[6], milli(f[4]), milli(f[5]));
    else if (k == 'K' && n >= 5) { paint_cut(&p, milli(f[1]), milli(f[2]), milli(f[3]), milli(f[4])); cuts++; }
    else if (k == 'k' && cuts > 0) { paint_uncut(&p); cuts--; }
    else bad++;
  }
  free(line); fclose(fp);
  if (cr) {
    paint_close(&p);
    cairo_destroy(cr);
    if (png) cairo_surface_write_to_png(surface, png);
    cairo_surface_destroy(surface);
    paint_faces_close(&faces);
  }
  if (pick) printf("%s\n", picked);
  if (count) printf("fills %ld  data texts %ld  other texts %ld  cuts %ld  pointer boxes %ld\n", kinds['F'], kinds['C'], kinds['T'], kinds['K'], kinds['H']);
  if (bad || cuts) { fprintf(stderr, "draw: %d rows are no call, %d cuts stay open\n", bad, cuts); return 1; }
  return 0;
}
