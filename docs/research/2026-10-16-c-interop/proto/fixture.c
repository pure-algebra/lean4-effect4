/* fixture.c -- the scanner of fixture.h. */

#define _POSIX_C_SOURCE 200809L
#include "fixture.h"

#include "e4val.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

fixture_frame *fixture_frames = NULL;
size_t fixture_count = 0;
static size_t capacity = 0;

static bool is_hex_token(const char *s, size_t n) {
  if (n < 18 || n % 2) return false;
  for (size_t i = 0; i < n; i++) {
    char c = s[i];
    if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) return false;
  }
  return true;
}

static void add(const char *tok, size_t n, const char *file, size_t line) {
  e4_buf b = {0};
  if (!e4_unhex(tok, n, &b)) { e4_buf_free(&b); return; }
  if (fixture_count == capacity) {
    capacity = capacity ? capacity * 2 : 64;
    fixture_frames = realloc(fixture_frames, capacity * sizeof(fixture_frame));
  }
  fixture_frame *f = &fixture_frames[fixture_count++];
  const char *base = strrchr(file, '/');
  snprintf(f->origin, sizeof f->origin, "%s:%zu", base ? base + 1 : file, line);
  f->ptr = b.ptr;
  f->len = b.len;
}

long fixture_load(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return -1;
  size_t before = fixture_count, lineno = 0, cap = 0;
  char *line = NULL;
  ssize_t got;
  while ((got = getline(&line, &cap, f)) >= 0) {
    lineno++;
    if (got == 0 || line[0] == '#') continue;
    char *p = line;
    while (*p) {
      while (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t') p++;
      char *start = p;
      while (*p && *p != ' ' && *p != '\n' && *p != '\r' && *p != '\t') p++;
      if (p > start && is_hex_token(start, (size_t)(p - start)))
        add(start, (size_t)(p - start), path, lineno);
    }
  }
  free(line);
  fclose(f);
  return (long)(fixture_count - before);
}

void fixture_free(void) {
  for (size_t i = 0; i < fixture_count; i++) free(fixture_frames[i].ptr);
  free(fixture_frames);
  fixture_frames = NULL;
  fixture_count = capacity = 0;
}
