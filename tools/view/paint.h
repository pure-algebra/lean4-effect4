/* paint.h: the painter of the native view (details seat, 2026-10-07; landed in tools/view by
 * slice V0 of docs/research/2026-10-09-visual-pipeline.md).
 *
 * One header over cairo and pangocairo. It has no SDL, no global and no state of its own: each
 * function works on the `Paint` that it is handed. Its pixel checks (`paint_test.c`) stand in
 * docs/research/2026-10-07-native-view-details/, and are not yet in the tree.
 *
 * The painter draws in LOGICAL PIXELS. A camera, a page layout and the rows are the caller's:
 * the caller maps its world to logical pixels, and the painter puts the result on device pixels.
 *
 * Properties. Each one names the check of paint_test.c that reads it back from the pixels.
 *
 *   P1 pixels    `ratio` device pixels make one logical pixel. An edge at the logical
 *                coordinate v stands on the device boundary floor(v * ratio + 1/2): paint_px,
 *                the one snapping rule, used by every primitive.
 *   P2 weights   A weight w is max(1, floor(w * ratio + 1/2)) device pixels: whole, at least
 *                one, and a function of w and the ratio only. A rule is placed by one edge,
 *                and its other edge is that edge plus the weight. So a rule is as thick
 *                wherever it stands, and the four sides of a frame are equal.
 *                (check `P1 P2 box and weight`)
 *   P3 coverage  A rule, a frame, a fill, a band, a connector and a dotted rule cover whole
 *                device pixels: a pixel is covered fully, or not at all (check `P3 crisp`).
 *                The dots of a dotted rule are equal and stand at one pitch (check `rhythm`).
 *   P4 joins     Rules that meet take the same snapped coordinate, and a frame or a connector
 *                paints no pixel twice. So a join has no gap, and a tone below full value
 *                shows no darker corner. (checks `P4 join`, `P4 once`)
 *   P5 zoom      A position is the caller's, already scaled. A weight is not scaled: a rule
 *                stays one logical pixel at every zoom.
 *   P6 text      The origin and the baseline of a text stand on device pixels, by the rule of
 *                P1 (check `P6 baseline`). A glyph follows the same rule. Cairo's image
 *                surface places a glyph at floor(v + 1/8) and gives it no place between pixels
 *                on this machine (`specimen --metrics`, section 8): so a baseline that is not
 *                snapped first can land one pixel above a rule at the same v, and a glyph one
 *                pixel left of its cell's edge. The painter snaps the baseline, and it moves a
 *                text right by 3/8 of a device pixel where cairo floors (PaintFaces.glyph_bias).
 *                A text is drawn in the ink, at full value: no function takes a tone for it.
 *   P7 cells     A text of the data face advances one cell for each character, whatever face
 *                draws the glyph, and each glyph stands on the device pixel that P1 gives its
 *                cell's left edge (checks `P7 cells`, `P7 foreign`). A text of n characters in
 *                a room of m cells is drawn whole when n <= m. Else m - 1 characters are drawn
 *                and the last cell holds an ellipsis. The cut is by count, never by a measured
 *                width, so no rounding cuts a text of whole cells (check `P7 cut`).
 *   P8 guard     A text of a proportional face is fitted by pango into its room plus half a
 *                logical pixel. So a text whose advance equals its room is not cut, and a text
 *                more than half a pixel wider is cut (check `P8 guard`).
 *   P9 hue       The base is black and white. With `hue` off, each role of an agent resolves
 *                to the ink, in one place: paint__source (check `P9 M9 hue`).
 *
 * What the caller owes:
 *   - `ratio` is positive, and every coordinate is finite. The checks cover the ratios 1, 2,
 *     3 and 1.5.
 *   - After paint_open the user space may be moved by whole device pixels only: cairo_translate
 *     by a whole number of logical pixels, at a whole ratio. No rotation, no further scale.
 *   - Sizes and weights are not negative.
 *   - A text is UTF-8, left to right, one code point for one cell in the data face.
 *   - On a vector surface (SVG, PDF) the ratio is 1: an edge then stands on a whole unit.
 */
#ifndef EFFECT4_PAINT_H
#define EFFECT4_PAINT_H

#include <stdio.h>

#include <pango/pangocairo.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* ---------- 1. the grid: one base unit by three ---------- */

#define PAINT_CELL 8.0      /* a cell's width, in logical pixels: the advance of the data face */
#define PAINT_ROW 24.0      /* a row's height: three cells' widths */
#define PAINT_BASE 16.0     /* a row's baseline, below its top: two thirds of the row */
#define PAINT_MIN_TEXT 6.5  /* a text is drawn where the data face has this many pixels or more */

/* ---------- 2. the tokens: a ground, the base, three agents ---------- */

typedef struct PaintTokens {
  uint32_t ground, ink, rule;        /* the base, as 0xRRGGBB */
  uint32_t host, failure, resource;  /* one hue for each agent; drawn only with `hue` on */
  double band;                       /* the value of the rule's tone in a band behind a row */
  double span;                       /* the same, in a span inside a line */
} PaintTokens;

/* The painter holds no palette of its own: a look's colours come from Lean, one `R` row of the
 * stream for each role (tools/Tools/View/Look.lean, `Look`; replay.h). */

typedef enum PaintRole { PAINT_GROUND, PAINT_INK, PAINT_RULE, PAINT_HOST, PAINT_FAILURE, PAINT_RESOURCE } PaintRole;

/* A tone: a role of the palette at a value from 0 to 1. Value is for an ordered state. */
typedef struct PaintTone { PaintRole role; double value; } PaintTone;

/* The tone of a role at a value. */
static inline PaintTone paint_tone(PaintRole role, double value) {
  PaintTone tone = {role, value};
  return tone;
}

/* ---------- 3. the faces ---------- */

typedef enum PaintFace {
  PAINT_DATA,   /* the monospace face: every text that is data; one cell for each character */
  PAINT_NAME,   /* the display face: a name */
  PAINT_LABEL,  /* its italic: a label or a remark */
  PAINT_TITLE,  /* the display face, larger: the title of a page */
  PAINT_FACE_COUNT
} PaintFace;

/* A face as a look names it: its families as one pango list, its size in logical pixels (the
 * data face's is measured from the cell), its weight (100 to 900) and whether it is italic. */
typedef struct PaintFaceSpec {
  char family[256];
  double px;
  int weight;
  int italic;
} PaintFaceSpec;

typedef struct PaintFaces {
  PangoFontDescription *face[PAINT_FACE_COUNT];
  double px[PAINT_FACE_COUNT];  /* each face's size in logical pixels, as pango holds it */
  int data_advance;             /* the advance of the data face at zoom 1, in pango units */
  double glyph_bias;            /* device pixels that a text is moved right by on an image surface, so
                                   that cairo places each glyph by the rule of P1: 3/8 where cairo
                                   floors a glyph's origin, 0 where it places a glyph between pixels */
} PaintFaces;

/* A layout with the options that every text of the painter is shaped and measured under:
 * no hinting of metrics, no hint style, no rounding of glyph positions. A text measured under
 * other options has another advance. Anti-aliasing is cairo's default, as in view.c: on this
 * machine that is the system's font smoothing, which draws a heavier glyph than
 * CAIRO_ANTIALIAS_GRAY does (`specimen --metrics`, section 14; the receipt's question 6). */
static inline PangoLayout *paint__layout(cairo_t *cr) {
  PangoLayout *layout = pango_cairo_create_layout(cr);
  PangoContext *context = pango_layout_get_context(layout);
  cairo_font_options_t *options = cairo_font_options_create();
  cairo_font_options_set_hint_metrics(options, CAIRO_HINT_METRICS_OFF);
  cairo_font_options_set_hint_style(options, CAIRO_HINT_STYLE_NONE);
  pango_cairo_context_set_font_options(context, options);
  cairo_font_options_destroy(options);
  pango_context_set_round_glyph_positions(context, FALSE);
  pango_layout_set_single_paragraph_mode(layout, TRUE);
  return layout;
}

#define PAINT__PROBE 64   /* the glyphs of the text that sizes the data face */

/* The advance of PAINT__PROBE glyphs of a description at a size, both in pango units. */
static inline int paint__advance(PangoLayout *layout, PangoFontDescription *face, int size) {
  char zeros[PAINT__PROBE + 1];
  int width = 0, height = 0;
  memset(zeros, '0', PAINT__PROBE);
  zeros[PAINT__PROBE] = 0;
  pango_font_description_set_absolute_size(face, (double)size);
  pango_layout_set_font_description(layout, face);
  pango_layout_set_text(layout, zeros, PAINT__PROBE);
  pango_layout_get_size(layout, &width, &height);
  return width;
}

/* Whether cairo's image surface draws a glyph at an origin of half a pixel as it draws it at
 * the whole pixel before: 1 when the two rasters are equal, so a glyph has no place between
 * pixels. */
static inline int paint__glyphs_floor(cairo_surface_t *surface, cairo_t *cr, PangoLayout *layout, const PangoFontDescription *face) {
  enum { SIDE = 32 };
  unsigned char first[SIDE * SIDE];
  int same = 1;
  pango_layout_set_font_description(layout, face);
  pango_layout_set_text(layout, "l", 1);
  for (int pass = 0; pass < 2; pass++) {
    cairo_set_operator(cr, CAIRO_OPERATOR_CLEAR);
    cairo_paint(cr);
    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);
    cairo_set_source_rgba(cr, 1, 1, 1, 1);
    cairo_move_to(cr, 8 + 0.5 * pass, 24);
    pango_cairo_show_layout_line(cr, pango_layout_get_line_readonly(layout, 0));
    cairo_surface_flush(surface);
    const unsigned char *bytes = cairo_image_surface_get_data(surface);
    const int stride = cairo_image_surface_get_stride(surface);
    for (int y = 0; y < SIDE; y++) {
      if (pass == 0) memcpy(first + y * SIDE, bytes + y * stride, SIDE);
      else same &= !memcmp(first + y * SIDE, bytes + y * stride, SIDE);
    }
  }
  return same;
}

/* Free the faces. Safe on a zeroed or a half-opened set. */
static inline void paint_faces_close(PaintFaces *faces) {
  for (int i = 0; i < PAINT_FACE_COUNT; i++)
    if (faces->face[i]) pango_font_description_free(faces->face[i]);
  memset(faces, 0, sizeof *faces);
}

/* Open the four faces of a look. The data face takes the size whose advance is one cell,
 * measured under the painter's own options and then confirmed at that size: its own size in
 * the spec is not read. Answers 1, or 0 when a description does not parse. The caller closes
 * the faces. */
static inline int paint_faces_open(PaintFaces *faces, const PaintFaceSpec spec[PAINT_FACE_COUNT]) {
  const int cell = (int)(PAINT_CELL * PANGO_SCALE);
  memset(faces, 0, sizeof *faces);
  for (int i = 0; i < PAINT_FACE_COUNT; i++) {
    faces->face[i] = pango_font_description_from_string(spec[i].family);
    if (!faces->face[i]) { paint_faces_close(faces); return 0; }
    pango_font_description_set_style(faces->face[i], spec[i].italic ? PANGO_STYLE_ITALIC : PANGO_STYLE_NORMAL);
    pango_font_description_set_weight(faces->face[i], (PangoWeight)spec[i].weight);
    faces->px[i] = i == PAINT_DATA ? 0.0 : spec[i].px;
    if (faces->px[i] > 0) pango_font_description_set_absolute_size(faces->face[i], faces->px[i] * PANGO_SCALE);
  }
  cairo_surface_t *surface = cairo_image_surface_create(CAIRO_FORMAT_A8, 32, 32);
  cairo_t *cr = cairo_create(surface);
  PangoLayout *layout = paint__layout(cr);
  const int probe = 128 * PANGO_SCALE;
  const int wide = paint__advance(layout, faces->face[PAINT_DATA], probe);
  const int size = wide > 0 ? (int)floor((double)cell * PAINT__PROBE * probe / wide + 0.5) : 13 * PANGO_SCALE;
  int best = size, miss = INT32_MAX;
  for (int d = -2; d <= 2; d++) {   /* a pango size is a whole number of units: take the nearest that hits the cell */
    const int off = abs(paint__advance(layout, faces->face[PAINT_DATA], size + d) - cell * PAINT__PROBE);
    if (off < miss || (off == miss && abs(d) < abs(best - size))) { miss = off; best = size + d; }
  }
  faces->data_advance = paint__advance(layout, faces->face[PAINT_DATA], best) / PAINT__PROBE;
  faces->px[PAINT_DATA] = (double)best / PANGO_SCALE;
  faces->glyph_bias = paint__glyphs_floor(surface, cr, layout, faces->face[PAINT_DATA]) ? 0.375 : 0.0;
  g_object_unref(layout);
  cairo_destroy(cr);
  cairo_surface_destroy(surface);
  return 1;
}

/* ---------- 4. the target ---------- */

typedef struct Paint {
  cairo_t *cr;                /* borrowed: paint_open saves and scales it, paint_close restores it */
  PangoLayout *layout;        /* owned */
  double ratio;               /* device pixels for one logical pixel */
  const PaintTokens *tokens;  /* borrowed */
  const PaintFaces *faces;    /* borrowed */
  int hue;                    /* 0: black and white. 1: an agent's marks take its hue */
  double bias;                /* P6: logical pixels that a text is moved right by; 0 off an image surface */
  /* The faces at one zoom other than 1. A zoom changes seldom, so one size for each face is kept. */
  PangoFontDescription *scaled[PAINT_FACE_COUNT];
  double scaled_at[PAINT_FACE_COUNT];
} Paint;

/* Start to paint on `cr`. One logical pixel is `ratio` device pixels from here to paint_close. */
static inline void paint_open(Paint *p, cairo_t *cr, double ratio, const PaintTokens *tokens, const PaintFaces *faces, int hue) {
  memset(p, 0, sizeof *p);
  p->cr = cr;
  p->ratio = ratio;
  p->tokens = tokens;
  p->faces = faces;
  p->hue = hue;
  p->bias = cairo_surface_get_type(cairo_get_target(cr)) == CAIRO_SURFACE_TYPE_IMAGE ? faces->glyph_bias / ratio : 0.0;
  cairo_save(cr);
  cairo_scale(cr, ratio, ratio);
  p->layout = paint__layout(cr);
}

/* End: free what paint_open made, and give the context back as it was. */
static inline void paint_close(Paint *p) {
  for (int i = 0; i < PAINT_FACE_COUNT; i++)
    if (p->scaled[i]) pango_font_description_free(p->scaled[i]);
  if (p->layout) g_object_unref(p->layout);
  if (p->cr) cairo_restore(p->cr);
  memset(p, 0, sizeof *p);
}

/* P9: the one place where a role becomes a colour. */
static inline void paint__source(const Paint *p, PaintTone tone) {
  const PaintTokens *k = p->tokens;
  uint32_t hex = k->ink;
  switch (tone.role) {
  case PAINT_GROUND: hex = k->ground; break;
  case PAINT_INK: hex = k->ink; break;
  case PAINT_RULE: hex = k->rule; break;
  case PAINT_HOST: hex = p->hue ? k->host : k->ink; break;
  case PAINT_FAILURE: hex = p->hue ? k->failure : k->ink; break;
  case PAINT_RESOURCE: hex = p->hue ? k->resource : k->ink; break;
  }
  cairo_set_source_rgba(p->cr, ((hex >> 16) & 255u) / 255.0, ((hex >> 8) & 255u) / 255.0, (hex & 255u) / 255.0, tone.value);
}

/* ---------- the stream: every call that reaches the target, as one row of text ----------
 *
 * With a file set here, the painter writes one row for each call that reaches the target:
 *   F role value x0 y0 x1 y1         a fill of whole device pixels; the value in thousandths
 *   B role weight x0 y0 x1 y1 x2 y2 x3 y3   a stroke along a cubic segment; device pixels
 *   C x baseline max scale text      a text of the data face; logical pixels in thousandths
 *   T face x baseline max scale text a text of another face
 *   K x y w h                        a cut to a box, until the next `k`
 *   k                                the end of the cut
 * draw.c replays such a stream through the same functions. */
static FILE *paint_stream;
static inline long paint__milli(double v) { return (long)floor(v * 1000.0 + 0.5); }

/* ---------- 5. device pixels: the snapping policy, stated once ---------- */

/* P1: the device boundary of a logical coordinate. floor(x + 1/2) commutes with a move by a
 * whole pixel on both sides of zero; C's round() does not. */
static inline long paint_px(const Paint *p, double v) { return (long)floor(v * p->ratio + 0.5); }

/* The logical coordinate of the same boundary. */
static inline double paint_snap(const Paint *p, double v) { return (double)paint_px(p, v) / p->ratio; }

/* P2: the device pixels of a weight. */
static inline long paint_weight(const Paint *p, double w) {
  const long n = (long)floor(w * p->ratio + 0.5);
  return n < 1 ? 1 : n;
}

/* P3: fill the device pixels [x0, x1) by [y0, y1). An empty box paints nothing. Every other
 * primitive below ends here. */
static inline void paint_device_fill(const Paint *p, PaintTone tone, long x0, long y0, long x1, long y1) {
  if (x1 <= x0 || y1 <= y0) return;
  if (paint_stream) fprintf(paint_stream, "F\t%d\t%ld\t%ld\t%ld\t%ld\t%ld\n", (int)tone.role, paint__milli(tone.value), x0, y0, x1, y1);
  paint__source(p, tone);
  cairo_rectangle(p->cr, (double)x0 / p->ratio, (double)y0 / p->ratio, (double)(x1 - x0) / p->ratio, (double)(y1 - y0) / p->ratio);
  cairo_fill(p->cr);
}

/* A stroke of `weight` device pixels along the cubic segment with device points `pt`: start, two
 * controls, end. An odd weight is centred on pixel centres, so a straight vertical or horizontal
 * piece covers whole pixels, as a rule does. Segments that meet end to end with one tangent join
 * without a seam: the caps are butt. */
static inline void paint_device_curve(const Paint *p, PaintTone tone, long weight, const long pt[8]) {
  if (weight < 1) return;
  if (paint_stream) fprintf(paint_stream, "B\t%d\t%ld\t%ld\t%ld\t%ld\t%ld\t%ld\t%ld\t%ld\t%ld\n", (int)tone.role, weight,
                            pt[0], pt[1], pt[2], pt[3], pt[4], pt[5], pt[6], pt[7]);
  paint__source(p, tone);
  const double r = p->ratio, h = (weight % 2) ? 0.5 : 0.0;
  cairo_set_line_width(p->cr, (double)weight / r);
  cairo_set_line_cap(p->cr, CAIRO_LINE_CAP_BUTT);
  cairo_move_to(p->cr, ((double)pt[0] + h) / r, ((double)pt[1] + h) / r);
  cairo_curve_to(p->cr, ((double)pt[2] + h) / r, ((double)pt[3] + h) / r, ((double)pt[4] + h) / r,
                 ((double)pt[5] + h) / r, ((double)pt[6] + h) / r, ((double)pt[7] + h) / r);
  cairo_stroke(p->cr);
}

/* A fill of closed paths by the even-odd rule, so a path inside another makes a hole. Each path is
 * a text of numbers in thousandths of a device pixel, separated by spaces: its start, then each
 * cubic segment's two controls and its end. A path with a malformed count of numbers is skipped. */
static inline void paint_device_shape(const Paint *p, PaintTone tone, int npaths, char *const *paths) {
  if (paint_stream) {
    fprintf(paint_stream, "S\t%d\t%ld", (int)tone.role, paint__milli(tone.value));
    for (int i = 0; i < npaths; i++) fprintf(paint_stream, "\t%s", paths[i]);
    fprintf(paint_stream, "\n");
  }
  paint__source(p, tone);
  const double k = 1000.0 * p->ratio;
  cairo_new_path(p->cr);
  for (int i = 0; i < npaths; i++) {
    double v[2 + 6 * 256];
    int n = 0;
    const char *c = paths[i];
    char *end;
    while (n < (int)(sizeof v / sizeof v[0])) {
      const long x = strtol(c, &end, 10);
      if (end == c) break;
      v[n++] = (double)x / k;
      c = end;
    }
    if (n < 8 || (n - 2) % 6 != 0) continue;
    cairo_move_to(p->cr, v[0], v[1]);
    for (int j = 2; j + 5 < n; j += 6) cairo_curve_to(p->cr, v[j], v[j + 1], v[j + 2], v[j + 3], v[j + 4], v[j + 5]);
    cairo_close_path(p->cr);
  }
  cairo_set_fill_rule(p->cr, CAIRO_FILL_RULE_EVEN_ODD);
  cairo_fill(p->cr);
  cairo_set_fill_rule(p->cr, CAIRO_FILL_RULE_WINDING);
}

/* P2, P4: a frame one `weight` thick inside the device box: four sides that share no pixel.
 * A box too small for a hole is filled. */
static inline void paint_device_frame(const Paint *p, PaintTone tone, long x0, long y0, long x1, long y1, long weight) {
  if (x1 - x0 <= 2 * weight || y1 - y0 <= 2 * weight) { paint_device_fill(p, tone, x0, y0, x1, y1); return; }
  paint_device_fill(p, tone, x0, y0, x1, y0 + weight);
  paint_device_fill(p, tone, x0, y1 - weight, x1, y1);
  paint_device_fill(p, tone, x0, y0 + weight, x0 + weight, y1 - weight);
  paint_device_fill(p, tone, x1 - weight, y0 + weight, x1, y1 - weight);
}

/* A dotted rule in the device span [a, b): dots `dot` pixels square at one `pitch`, centred in
 * the span. Every dot is equal and every gap between two dots is equal. The gaps at the two
 * ends differ by one pixel at most. A span shorter than a dot is filled. */
static inline void paint_device_dots(const Paint *p, PaintTone tone, long a, long b, long top, long dot, long pitch) {
  if (b - a < dot) { paint_device_fill(p, tone, a, top, b, top + dot); return; }
  if (pitch <= dot) pitch = dot + 1;
  const long n = (b - a - dot) / pitch + 1;
  const long first = a + (b - a - (dot + (n - 1) * pitch)) / 2;
  for (long i = 0; i < n; i++) paint_device_fill(p, tone, first + i * pitch, top, first + i * pitch + dot, top + dot);
}

/* ---------- 6. rules, frames, fills and bands ---------- */

/* A filled box. Each edge is snapped by itself, so two fills that share an edge share it on
 * the device too. A fill never vanishes: it keeps one device pixel in each direction. */
static inline void paint_fill(const Paint *p, PaintTone tone, double x, double y, double w, double h) {
  const long x0 = paint_px(p, x), y0 = paint_px(p, y);
  long x1 = paint_px(p, x + w), y1 = paint_px(p, y + h);
  if (x1 <= x0) x1 = x0 + 1;
  if (y1 <= y0) y1 = y0 + 1;
  paint_device_fill(p, tone, x0, y0, x1, y1);
}

/* A horizontal rule from x0 to x1. Its top edge stands at y, and it is `weight` thick below. */
static inline void paint_hrule(const Paint *p, PaintTone tone, double x0, double x1, double y, double weight) {
  const long a = paint_px(p, x0 < x1 ? x0 : x1), top = paint_px(p, y);
  long b = paint_px(p, x0 < x1 ? x1 : x0);
  if (b <= a) b = a + 1;
  paint_device_fill(p, tone, a, top, b, top + paint_weight(p, weight));
}

/* A vertical rule from y0 to y1. Its left edge stands at x, and it is `weight` thick at the right. */
static inline void paint_vrule(const Paint *p, PaintTone tone, double x, double y0, double y1, double weight) {
  const long a = paint_px(p, y0 < y1 ? y0 : y1), left = paint_px(p, x);
  long b = paint_px(p, y0 < y1 ? y1 : y0);
  if (b <= a) b = a + 1;
  paint_device_fill(p, tone, left, a, left + paint_weight(p, weight), b);
}

/* A frame inside the box x, y, w, h. Its outer edges are the edges of paint_fill of that box. */
static inline void paint_frame(const Paint *p, PaintTone tone, double x, double y, double w, double h, double weight) {
  const long x0 = paint_px(p, x), y0 = paint_px(p, y);
  long x1 = paint_px(p, x + w), y1 = paint_px(p, y + h);
  if (x1 <= x0) x1 = x0 + 1;
  if (y1 <= y0) y1 = y0 + 1;
  paint_device_frame(p, tone, x0, y0, x1, y1, paint_weight(p, weight));
}

/* A dotted horizontal rule from x0 to x1, its top edge at y: dots one `weight` square, at a
 * pitch of `pitch` weights. */
static inline void paint_hdots(const Paint *p, PaintTone tone, double x0, double x1, double y, double weight, int pitch) {
  const long dot = paint_weight(p, weight);
  paint_device_dots(p, tone, paint_px(p, x0), paint_px(p, x1), paint_px(p, y), dot, dot * pitch);
}

/* The band behind a lit row, and the band behind a lit span of a line. */
static inline void paint_band(const Paint *p, double x, double y, double w, double h) {
  paint_fill(p, paint_tone(PAINT_RULE, p->tokens->band), x, y, w, h);
}
static inline void paint_span(const Paint *p, double x, double y, double w, double h) {
  paint_fill(p, paint_tone(PAINT_RULE, p->tokens->span), x, y, w, h);
}

/* A cut: what is painted until paint_uncut stays inside the box. Cuts nest. */
static inline void paint_cut(const Paint *p, double x, double y, double w, double h) {
  if (paint_stream) fprintf(paint_stream, "K\t%ld\t%ld\t%ld\t%ld\n", paint__milli(x), paint__milli(y), paint__milli(w), paint__milli(h));
  cairo_save(p->cr);
  cairo_rectangle(p->cr, x, y, w, h);
  cairo_clip(p->cr);
}
static inline void paint_uncut(const Paint *p) {
  if (paint_stream) fprintf(paint_stream, "k\n");
  cairo_restore(p->cr);
}

/* ---------- 7. connectors ---------- */

/* An edge of a tree whose children stand below: a stem down from (x0, y0) to the bar at
 * `ybar`, the bar across to x1, and a stem down to y1. x0 and x1 are the left edges of the two
 * stems. P4: the three parts share no pixel, and each corner is square. With x0 = x1 the edge
 * is one straight rule. Edges of one parent overlap on its stem and bar: give them a full value. */
static inline void paint_tree_edge(const Paint *p, PaintTone tone, double x0, double y0, double ybar, double x1, double y1, double weight) {
  const long w = paint_weight(p, weight);
  const long a = paint_px(p, x0), b = paint_px(p, x1), top = paint_px(p, y0), bar = paint_px(p, ybar), foot = paint_px(p, y1);
  paint_device_fill(p, tone, a, top, a + w, bar);
  paint_device_fill(p, tone, a < b ? a : b, bar, (a < b ? b : a) + w, bar + w);
  paint_device_fill(p, tone, b, bar + w, b + w, foot);
}

/* An elbow: a stem down from (x0, y0) to `yturn`, then a rule across to x1. x0 is the left edge
 * of the stem. P4: the corner pixel belongs to the rule, so the two parts share no pixel. */
static inline void paint_elbow(const Paint *p, PaintTone tone, double x0, double y0, double yturn, double x1, double weight) {
  const long w = paint_weight(p, weight);
  const long a = paint_px(p, x0), b = paint_px(p, x1), top = paint_px(p, y0), turn = paint_px(p, yturn);
  paint_device_fill(p, tone, a, top, a + w, turn);
  paint_device_fill(p, tone, b < a ? b : a, turn, b > a + w ? b : a + w, turn + w);
}

/* ---------- 8. text ---------- */

/* The characters of a UTF-8 text: the cells that it takes in the data face. */
static inline int paint_utf8_cells(const char *s) {
  int n = 0;
  for (; *s; s++) n += ((unsigned char)*s & 0xC0) != 0x80;
  return n;
}

/* The bytes of the first `n` characters of a UTF-8 text. */
static inline int paint__utf8_bytes(const char *s, int n) {
  const char *c = s;
  while (*c && n > 0) {
    c++;
    while (((unsigned char)*c & 0xC0) == 0x80) c++;
    n--;
  }
  return (int)(c - s);
}

/* A face at a zoom. */
static inline const PangoFontDescription *paint__face(Paint *p, PaintFace face, double scale) {
  if (scale == 1.0) return p->faces->face[face];
  if (!p->scaled[face] || p->scaled_at[face] != scale) {
    if (p->scaled[face]) pango_font_description_free(p->scaled[face]);
    p->scaled[face] = pango_font_description_copy(p->faces->face[face]);
    pango_font_description_set_absolute_size(p->scaled[face], floor(p->faces->px[face] * scale * PANGO_SCALE + 0.5));
    p->scaled_at[face] = scale;
  }
  return p->scaled[face];
}

/* Whether a text of the data face can be read at a zoom: view.c's rule for drawing a text. */
static inline int paint_readable(const Paint *p, double scale) { return p->faces->px[PAINT_DATA] * scale >= PAINT_MIN_TEXT; }

/* The left edge of cell k of a run at a zoom, in pango units from the run's origin. */
static inline int paint__cell_units(double scale, int k) { return (int)floor(k * PAINT_CELL * scale * PANGO_SCALE + 0.5); }

/* P7: give each character of the shaped line one cell. A glyph whose own advance is the cell's
 * keeps its place in the cell. A glyph of another advance comes from a face that pango took in
 * the data face's place: its ink is centred in its cell. */
static inline void paint__to_cells(PangoLayoutLine *line, const char *text, double scale) {
  int cell = 0;
  for (GSList *r = line->runs; r; r = r->next) {
    PangoGlyphItem *run = r->data;
    PangoGlyphString *glyphs = run->glyphs;
    const char *bytes = text + run->item->offset;
    if (run->item->analysis.level & 1) { cell += run->item->num_chars; continue; }   /* right to left: left as pango shaped it */
    for (int i = 0; i < glyphs->num_glyphs; i++) {
      PangoGlyphGeometry *g = &glyphs->glyphs[i].geometry;
      if (i > 0 && glyphs->log_clusters[i] == glyphs->log_clusters[i - 1]) { g->width = 0; continue; }
      int next = i + 1, chars = 0;
      while (next < glyphs->num_glyphs && glyphs->log_clusters[next] == glyphs->log_clusters[i]) next++;
      const int end = next < glyphs->num_glyphs ? glyphs->log_clusters[next] : run->item->length;
      for (int b = glyphs->log_clusters[i]; b < end; b++) chars += ((unsigned char)bytes[b] & 0xC0) != 0x80;
      const int width = paint__cell_units(scale, cell + chars) - paint__cell_units(scale, cell);
      const int slack = width / 512 > 2 ? width / 512 : 2;
      if (abs(g->width - width) > slack) {
        PangoRectangle ink;
        pango_font_get_glyph_extents(run->item->analysis.font, glyphs->glyphs[i].glyph, &ink, NULL);
        g->x_offset += (width - ink.width) / 2 - ink.x;
      }
      g->width = width;
      cell += chars;
    }
  }
}

/* P6, P7: a text of the data face in a room of `max_cells` cells. `x` is the left edge of the
 * first cell and `baseline` the baseline, in logical pixels. `scale` is the zoom: a cell is
 * PAINT_CELL * scale wide. Answers the cells drawn. */
static inline int paint_cells(Paint *p, double x, double baseline, const char *utf8, int max_cells, double scale) {
  if (!utf8 || !*utf8 || max_cells <= 0) return 0;
  if (paint_stream) fprintf(paint_stream, "C\t%ld\t%ld\t%d\t%ld\t%s\n", paint__milli(x), paint__milli(baseline), max_cells, paint__milli(scale), utf8);
  const int n = paint_utf8_cells(utf8);
  const int shown = n <= max_cells ? n : max_cells - 1;
  const double left = paint_snap(p, x) + p->bias, base = paint_snap(p, baseline);
  paint__source(p, paint_tone(PAINT_INK, 1.0));
  pango_layout_set_font_description(p->layout, paint__face(p, PAINT_DATA, scale));
  pango_layout_set_width(p->layout, -1);
  pango_layout_set_ellipsize(p->layout, PANGO_ELLIPSIZE_NONE);
  if (shown > 0) {
    pango_layout_set_text(p->layout, utf8, paint__utf8_bytes(utf8, shown));
    PangoLayoutLine *line = pango_layout_get_line(p->layout, 0);
    paint__to_cells(line, pango_layout_get_text(p->layout), scale);
    cairo_move_to(p->cr, left, base);
    pango_cairo_show_layout_line(p->cr, line);
  }
  if (n > max_cells) {
    pango_layout_set_text(p->layout, "\xE2\x80\xA6", -1);   /* the ellipsis, in the room's last cell */
    PangoLayoutLine *line = pango_layout_get_line(p->layout, 0);
    paint__to_cells(line, pango_layout_get_text(p->layout), scale);
    cairo_move_to(p->cr, left + (max_cells - 1) * PAINT_CELL * scale, base);
    pango_cairo_show_layout_line(p->cr, line);
  }
  return n <= max_cells ? n : max_cells;
}

/* The advance of a text of a proportional face at a zoom, in logical pixels. */
static inline double paint_text_width(Paint *p, PaintFace face, const char *utf8, double scale) {
  int width = 0, height = 0;
  if (!utf8 || !*utf8) return 0.0;
  pango_layout_set_font_description(p->layout, paint__face(p, face, scale));
  pango_layout_set_width(p->layout, -1);
  pango_layout_set_ellipsize(p->layout, PANGO_ELLIPSIZE_NONE);
  pango_layout_set_text(p->layout, utf8, -1);
  pango_layout_get_size(p->layout, &width, &height);
  return (double)width / PANGO_SCALE;
}

/* P6, P8: a text of a face in a room of `max_width` logical pixels; a room of 0 or less is no
 * limit. Pango cuts a text that does not fit and ends it in an ellipsis. Answers 1 when the
 * text is cut. For the data face use paint_cells: this function keeps no cell. */
static inline int paint_text(Paint *p, PaintFace face, double x, double baseline, const char *utf8, double max_width, double scale) {
  if (!utf8 || !*utf8) return 0;
  if (paint_stream) fprintf(paint_stream, "T\t%d\t%ld\t%ld\t%ld\t%ld\t%s\n", (int)face, paint__milli(x), paint__milli(baseline), paint__milli(max_width), paint__milli(scale), utf8);
  paint__source(p, paint_tone(PAINT_INK, 1.0));
  pango_layout_set_font_description(p->layout, paint__face(p, face, scale));
  pango_layout_set_ellipsize(p->layout, PANGO_ELLIPSIZE_END);
  pango_layout_set_width(p->layout, max_width > 0 ? (int)((max_width + 0.5) * PANGO_SCALE) : -1);
  pango_layout_set_text(p->layout, utf8, -1);
  cairo_move_to(p->cr, paint_snap(p, x) + p->bias, paint_snap(p, baseline));
  pango_cairo_show_layout_line(p->cr, pango_layout_get_line_readonly(p->layout, 0));
  return pango_layout_is_ellipsized(p->layout);
}

#endif
