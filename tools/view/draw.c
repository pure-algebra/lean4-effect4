/* draw.c: replay a stream of drawing calls, and decide nothing (tools/view, from the native view
 * probe of 2026-10-07; docs/research/2026-10-09-visual-pipeline.md). The stream's rows are
 * replay.h's.
 *
 *   draw STREAM --png FILE           paint the stream
 *   draw STREAM --pick X Y           the key under a device pixel, by the stream's `H` rows
 *   draw STREAM --picks FILE         the key under each device pixel of a file of points
 *   draw STREAM --count              the rows of each kind
 *
 * It answers 0 when every row is a call that it knows and every cut is closed. The last pointer
 * box that holds a pixel answers it, as `pick` does in Lean (`pick_append`).
 */
#define _GNU_SOURCE
#include "replay.h"

/* The key under the device pixel (x, y): the last `H` row whose box holds it. */
static void pick_at(const char *path, long x, long y, char *key, size_t room) {
  key[0] = 0;
  FILE *fp = fopen(path, "r");
  if (!fp) return;
  char *row = NULL; size_t cap = 0; ssize_t len;
  while ((len = getline(&row, &cap, fp)) > 0) {
    if (row[0] != 'H') continue;
    while (len > 0 && (row[len - 1] == '\n' || row[len - 1] == '\r')) row[--len] = 0;
    char *f[8]; int n = replay_fields(row, f, 8);
    if (n >= 6 && x >= atol(f[2]) && x < atol(f[4]) && y >= atol(f[3]) && y < atol(f[5]))
      snprintf(key, room, "%s", f[1]);
  }
  free(row); fclose(fp);
}

/* The rows of each kind, and whether every row is a call and every cut is closed. */
static int count(const char *path) {
  FILE *fp = fopen(path, "r");
  if (!fp) { perror(path); return 1; }
  long kinds[128] = {0}; int cuts = 0, bad = 0;
  char *row = NULL; size_t cap = 0; ssize_t len;
  while ((len = getline(&row, &cap, fp)) > 0) {
    char k = row[0];
    kinds[(unsigned char)k & 127]++;
    if (k == 'K') cuts++;
    else if (k == 'k') cuts--;
    else if (!strchr("PFCTH\n", k)) bad++;
  }
  free(row); fclose(fp);
  printf("fills %ld  data texts %ld  other texts %ld  cuts %ld  pointer boxes %ld\n", kinds['F'], kinds['C'], kinds['T'], kinds['K'], kinds['H']);
  if (bad || cuts) { fprintf(stderr, "draw: %d rows are no call, %d cuts stay open\n", bad, cuts); return 1; }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: draw STREAM (--png FILE | --pick X Y | --picks FILE | --count)\n"); return 2; }
  const char *stream = argv[1];
  if (!strcmp(argv[2], "--count")) return count(stream);
  if (!strcmp(argv[2], "--pick") && argc >= 5) {
    char key[256]; pick_at(stream, atol(argv[3]), atol(argv[4]), key, sizeof key);
    printf("%s\n", key);
    return 0;
  }
  if (!strcmp(argv[2], "--picks") && argc >= 4) {
    FILE *pf = fopen(argv[3], "r"); long x, y; char key[256];
    if (!pf) { perror(argv[3]); return 1; }
    while (fscanf(pf, "%ld %ld", &x, &y) == 2) { pick_at(stream, x, y, key, sizeof key); printf("%s\n", key); }
    fclose(pf);
    return 0;
  }
  if (!strcmp(argv[2], "--png") && argc >= 4) {
    PaintFaces faces;
    if (!paint_faces_open(&faces)) { fprintf(stderr, "draw: a face does not open\n"); return 1; }
    int bad = 0;
    cairo_surface_t *surface = replay_stream(stream, &faces, &bad);
    if (!surface) { fprintf(stderr, "draw: %s has no target row\n", stream); paint_faces_close(&faces); return 1; }
    cairo_surface_write_to_png(surface, argv[3]);
    cairo_surface_destroy(surface);
    paint_faces_close(&faces);
    if (bad) { fprintf(stderr, "draw: %d rows are no call or cuts stay open\n", bad); return 1; }
    return 0;
  }
  fprintf(stderr, "draw: no flag %s\n", argv[2]);
  return 2;
}
