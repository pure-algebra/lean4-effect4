/* draw.c: replay a stream of drawing calls, and decide nothing (tools/view, from the native view
 * probe of 2026-10-07; docs/research/2026-10-09-visual-pipeline.md). The stream's rows are
 * replay.h's.
 *
 *   draw STREAM --png FILE           paint the stream
 *   draw STREAM --kitty [COLUMNS]    paint the stream into the terminal, by the kitty graphics
 *                                    protocol (Ghostty, kitty), COLUMNS cells wide (the terminal's
 *                                    width by default)
 *   draw STREAM --pick X Y           the key under a device pixel, by the stream's `H` rows
 *   draw STREAM --picks FILE         the key under each device pixel of a file of points
 *   draw STREAM --count              the rows of each kind
 *
 * It answers 0 when every row is a call that it knows and every cut is closed. The last pointer
 * box that holds a pixel answers it, as `pick` does in Lean (`pick_append`).
 */
#define _GNU_SOURCE
#include "replay.h"
#include <sys/ioctl.h>
#include <unistd.h>

/* A growable buffer for the PNG that cairo writes. */
typedef struct { unsigned char *data; size_t len, cap; } Bytes;

static cairo_status_t bytes_write(void *closure, const unsigned char *data, unsigned int length) {
  Bytes *b = closure;
  if (b->len + length > b->cap) {
    size_t cap = b->cap ? b->cap : 65536;
    while (cap < b->len + length) cap *= 2;
    unsigned char *grown = realloc(b->data, cap);
    if (!grown) return CAIRO_STATUS_NO_MEMORY;
    b->data = grown; b->cap = cap;
  }
  memcpy(b->data + b->len, data, length);
  b->len += length;
  return CAIRO_STATUS_SUCCESS;
}

/* The terminal's width in cells, or 0 when standard output is no terminal. */
static long terminal_columns(void) {
  struct winsize w;
  if (isatty(STDOUT_FILENO) && ioctl(STDOUT_FILENO, TIOCGWINSZ, &w) == 0) return (long)w.ws_col;
  return 0;
}

/* A PNG in the kitty graphics protocol: transmit and show (`a=T`) a PNG (`f=100`) quietly
 * (`q=2`), in base64 chunks of 4096 bytes, the last with `m=0`; `c` cells wide when `columns` is
 * positive, the height kept in proportion. */
static void kitty_png(const Bytes *png, long columns) {
  static const char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  char chunk[4096];
  size_t i = 0;
  int first = 1;
  while (i < png->len) {
    size_t n = 0;
    while (n < sizeof chunk && i < png->len) {
      unsigned v = (unsigned)png->data[i] << 16;
      if (i + 1 < png->len) v |= (unsigned)png->data[i + 1] << 8;
      if (i + 2 < png->len) v |= (unsigned)png->data[i + 2];
      chunk[n++] = b64[(v >> 18) & 63];
      chunk[n++] = b64[(v >> 12) & 63];
      chunk[n++] = i + 1 < png->len ? b64[(v >> 6) & 63] : '=';
      chunk[n++] = i + 2 < png->len ? b64[v & 63] : '=';
      i += 3;
    }
    int more = i < png->len;
    if (first && columns > 0) printf("\033_Gf=100,a=T,q=2,c=%ld,m=%d;", columns, more);
    else if (first) printf("\033_Gf=100,a=T,q=2,m=%d;", more);
    else printf("\033_Gm=%d;", more);
    first = 0;
    fwrite(chunk, 1, n, stdout);
    fputs("\033\\", stdout);
  }
  putchar('\n');
}

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
    else if (!strchr("PRYFBCTHS\n", k)) bad++;
  }
  free(row); fclose(fp);
  printf("fills %ld  curves %ld  shapes %ld  data texts %ld  other texts %ld  cuts %ld  pointer boxes %ld\n", kinds['F'], kinds['B'], kinds['S'], kinds['C'], kinds['T'], kinds['K'], kinds['H']);
  if (bad || cuts) { fprintf(stderr, "draw: %d rows are no call, %d cuts stay open\n", bad, cuts); return 1; }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: draw STREAM (--png FILE | --kitty [COLUMNS] | --pick X Y | --picks FILE | --count)\n"); return 2; }
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
    Replay rp; memset(&rp, 0, sizeof rp);
    int bad = 0;
    cairo_surface_t *surface = replay_stream(stream, &rp, &bad);
    if (!surface) { fprintf(stderr, "draw: %s has no target row, or its faces do not open\n", stream); replay_close(&rp); return 1; }
    cairo_surface_write_to_png(surface, argv[3]);
    cairo_surface_destroy(surface);
    replay_close(&rp);
    if (bad) { fprintf(stderr, "draw: %d rows are no call or cuts stay open\n", bad); return 1; }
    return 0;
  }
  if (!strcmp(argv[2], "--kitty")) {
    Replay rp; memset(&rp, 0, sizeof rp);
    int bad = 0;
    cairo_surface_t *surface = replay_stream(stream, &rp, &bad);
    if (!surface) { fprintf(stderr, "draw: %s has no target row, or its faces do not open\n", stream); replay_close(&rp); return 1; }
    Bytes png = { NULL, 0, 0 };
    cairo_status_t status = cairo_surface_write_to_png_stream(surface, bytes_write, &png);
    cairo_surface_destroy(surface);
    replay_close(&rp);
    if (status != CAIRO_STATUS_SUCCESS) { fprintf(stderr, "draw: %s\n", cairo_status_to_string(status)); free(png.data); return 1; }
    kitty_png(&png, argc >= 4 ? atol(argv[3]) : terminal_columns());
    free(png.data);
    if (bad) { fprintf(stderr, "draw: %d rows are no call or cuts stay open\n", bad); return 1; }
    return 0;
  }
  fprintf(stderr, "draw: no flag %s\n", argv[2]);
  return 2;
}
