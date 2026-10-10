/* scene_test: apply each DIR/NNN.patch in order to one retained scene (scene.h), flatten it after
 * each patch, and compare the stream with DIR/NNN.draw, the full stream Lean wrote for the same
 * page, byte for byte.
 *
 *   scene_test DIR...     answers 0 when every frame of every DIR agrees
 */
#include <dirent.h>
#include "scene.h"

static int by_name(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

/* The whole file at `path`, NUL-terminated, or NULL. */
static char *slurp(const char *path, size_t *len) {
  FILE *fp = fopen(path, "rb");
  if (!fp) return NULL;
  fseek(fp, 0, SEEK_END); long n = ftell(fp); fseek(fp, 0, SEEK_SET);
  char *buf = (char *)malloc((size_t)n + 1);
  if (buf && fread(buf, 1, (size_t)n, fp) != (size_t)n) { free(buf); buf = NULL; }
  fclose(fp);
  if (buf) { buf[n] = 0; *len = (size_t)n; }
  return buf;
}

/* The first line where two texts differ, from 1; 0 when they are equal. */
static long first_difference(const char *a, const char *b) {
  long line = 1;
  for (; *a && *a == *b; a++, b++) if (*a == '\n') line++;
  return *a == *b ? 0 : line;
}

static int run_dir(const char *dir, long *frames, long *bytes_patch, long *bytes_full) {
  DIR *d = opendir(dir);
  if (!d) { perror(dir); return 0; }
  char *names[4096]; int count = 0;
  struct dirent *e;
  while ((e = readdir(d)) && count < 4096) {
    size_t n = strlen(e->d_name);
    if (n > 6 && !strcmp(e->d_name + n - 6, ".patch")) names[count++] = scene_dup(e->d_name);
  }
  closedir(d);
  qsort(names, (size_t)count, sizeof *names, by_name);
  Scene sc;
  if (!scene_init(&sc)) return 0;
  int ok = 1;
  for (int i = 0; i < count && ok; i++) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", dir, names[i]);
    size_t plen = 0; char *patch = slurp(path, &plen);
    if (!patch) { fprintf(stderr, "%s: cannot read\n", path); ok = 0; break; }
    *bytes_patch += (long)plen;
    for (char *line = patch, *nl; *line; line = nl + 1) {
      nl = strchr(line, '\n');
      if (!nl) nl = line + strlen(line) - 1;
      char saved = *nl; *nl = 0;
      if (*line && !scene_apply_row(&sc, line)) { fprintf(stderr, "%s: bad row: %.80s\n", path, line); ok = 0; }
      *nl = saved;
      if (!saved) break;
    }
    free(patch);
    char *flat = NULL; size_t flen = 0;
    FILE *out = open_memstream(&flat, &flen);
    scene_flatten(&sc, out);
    fclose(out);
    snprintf(path, sizeof path, "%s/%.*s.draw", dir, (int)(strlen(names[i]) - 6), names[i]);
    size_t elen = 0; char *expected = slurp(path, &elen);
    *bytes_full += (long)elen;
    long diff = expected ? first_difference(flat, expected) : -1;
    if (diff) { fprintf(stderr, "%s: differs at line %ld\n", path, diff); ok = 0; }
    (*frames)++;
    free(flat); free(expected);
  }
  for (int i = 0; i < count; i++) free(names[i]);
  scene_free(&sc);
  return ok;
}

int main(int argc, char **argv) {
  int ok = 1;
  for (int a = 1; a < argc; a++) {
    long frames = 0, bp = 0, bf = 0;
    int good = run_dir(argv[a], &frames, &bp, &bf);
    printf("%s: %ld frames %s; patches %ld bytes, full streams %ld bytes\n", argv[a], frames,
           good ? "agree" : "DIFFER", bp, bf);
    ok &= good;
  }
  return ok ? 0 : 1;
}
