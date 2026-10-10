/* scene.h: a retained picture that takes patches and flattens to a stream, deciding nothing.
 *
 * Lean's live loop (docs/research/2026-10-10-live-view/probes/src/ProbeView/Live.lean) answers
 * each edit with a patch: rows that extend the stream replay.h paints (tools/view/replay.h).
 *
 *   P width height ratio light hue step   the target, when its size changed
 *   R role rrggbb / Y face ...            the look, on the first patch
 *   O id ax ay                            an object put at the anchor (ax, ay) in its group;
 *                                         its device rows follow, relative to the anchor, to `o`
 *   M id dx dy                            an object moved by (dx, dy) logical pixels
 *   X id                                  an object dropped
 *   G group dx dy                         a group's origin moved
 *   I id prev                             a new object's place in the order: after `prev`, or first
 *   Q id id ...                           the whole order, when the old objects did not keep it
 *   E frame                               the end of the patch
 *
 * An id is `group/key#rank`. Flattening writes the target, the look, and each object's rows in
 * order, each moved by its group's origin plus its anchor. A move of (dx, dy) logical pixels is
 * Lean's `Dev.move ratio dx dy` (tools/Tools/View/Picture.lean): fills, curves and pointer boxes
 * move by ratio times the move in device pixels; texts and cuts by the move in thousandths of a
 * logical pixel; shapes by ratio times the move in thousandths of a device pixel. By the lowering's
 * move law (`lowerCall_move`), the flattened stream is the stream of the whole picture.
 *
 * Contracts: scene_apply_row takes one row without its line break and answers 0 on a malformed
 * row; scene_flatten writes a stream that replay_stream reads. Memory is the scene's: scene_free
 * releases it. C11, no dependency beyond the C library.
 */
#ifndef EFFECT4_SCENE_H
#define EFFECT4_SCENE_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- small owned strings ---------- */

static inline char *scene_dup(const char *s) {
  size_t n = strlen(s) + 1;
  char *d = (char *)malloc(n);
  if (d) memcpy(d, s, n);
  return d;
}

/* ---------- objects, by id, in a chained hash table ---------- */

typedef struct SceneObj {
  char *id;
  char *group;          /* the id's text before its first '/' */
  long ax, ay;          /* the anchor in the group, logical pixels */
  char **rows;          /* device rows relative to the anchor */
  int nrows, caprows;
  struct SceneObj *next;
} SceneObj;

typedef struct SceneGroup { char *name; long ox, oy; } SceneGroup;

typedef struct Scene {
  SceneObj **table; size_t buckets, count;
  SceneObj **order; size_t norder, caporder;
  SceneGroup *groups; size_t ngroups, capgroups;
  char *target;         /* the last P row */
  char **look; int nlook, caplook;
  long ratio;           /* the target's ratio, a whole number */
  SceneObj *open;       /* the object an O row opened, until `o` */
} Scene;

static inline uint64_t scene_hash(const char *s) {
  uint64_t h = 1469598103934665603ULL;
  for (; *s; s++) { h ^= (unsigned char)*s; h *= 1099511628211ULL; }
  return h;
}

static inline int scene_init(Scene *sc) {
  memset(sc, 0, sizeof *sc);
  sc->buckets = 1024;
  sc->table = (SceneObj **)calloc(sc->buckets, sizeof *sc->table);
  sc->ratio = 1;
  return sc->table != NULL;
}

static inline SceneObj *scene_find(const Scene *sc, const char *id) {
  for (SceneObj *o = sc->table[scene_hash(id) % sc->buckets]; o; o = o->next)
    if (!strcmp(o->id, id)) return o;
  return NULL;
}

static inline void scene_obj_clear_rows(SceneObj *o) {
  for (int i = 0; i < o->nrows; i++) free(o->rows[i]);
  o->nrows = 0;
}

static inline void scene_obj_free(SceneObj *o) {
  scene_obj_clear_rows(o);
  free(o->rows); free(o->id); free(o->group); free(o);
}

static inline int scene_grow_table(Scene *sc) {
  size_t nb = sc->buckets * 2;
  SceneObj **t = (SceneObj **)calloc(nb, sizeof *t);
  if (!t) return 0;
  for (size_t b = 0; b < sc->buckets; b++)
    for (SceneObj *o = sc->table[b], *nx; o; o = nx) {
      nx = o->next;
      size_t i = scene_hash(o->id) % nb;
      o->next = t[i]; t[i] = o;
    }
  free(sc->table); sc->table = t; sc->buckets = nb;
  return 1;
}

/* The object with `id`, made empty at the anchor when it is new. */
static inline SceneObj *scene_put(Scene *sc, const char *id, long ax, long ay) {
  SceneObj *o = scene_find(sc, id);
  if (o) { scene_obj_clear_rows(o); o->ax = ax; o->ay = ay; return o; }
  if (sc->count + 1 > sc->buckets && !scene_grow_table(sc)) return NULL;
  o = (SceneObj *)calloc(1, sizeof *o);
  if (!o) return NULL;
  o->id = scene_dup(id);
  const char *slash = strchr(id, '/');
  size_t g = slash ? (size_t)(slash - id) : 0;
  o->group = (char *)malloc(g + 1);
  if (!o->id || !o->group) { free(o->id); free(o->group); free(o); return NULL; }
  memcpy(o->group, id, g); o->group[g] = 0;
  o->ax = ax; o->ay = ay;
  size_t i = scene_hash(id) % sc->buckets;
  o->next = sc->table[i]; sc->table[i] = o; sc->count++;
  return o;
}

static inline int scene_obj_push(SceneObj *o, const char *row) {
  if (o->nrows == o->caprows) {
    int cap = o->caprows ? 2 * o->caprows : 8;
    char **r = (char **)realloc(o->rows, (size_t)cap * sizeof *r);
    if (!r) return 0;
    o->rows = r; o->caprows = cap;
  }
  return (o->rows[o->nrows++] = scene_dup(row)) != NULL;
}

/* ---------- the order of painting ---------- */

static inline int scene_order_reserve(Scene *sc, size_t n) {
  if (n <= sc->caporder) return 1;
  size_t cap = sc->caporder ? sc->caporder : 64;
  while (cap < n) cap *= 2;
  SceneObj **o = (SceneObj **)realloc(sc->order, cap * sizeof *o);
  if (!o) return 0;
  sc->order = o; sc->caporder = cap;
  return 1;
}

static inline void scene_order_remove(Scene *sc, const SceneObj *o) {
  for (size_t i = 0; i < sc->norder; i++)
    if (sc->order[i] == o) {
      memmove(&sc->order[i], &sc->order[i + 1], (sc->norder - i - 1) * sizeof *sc->order);
      sc->norder--;
      return;
    }
}

/* Insert `o` after `prev`, or first when `prev` is NULL. */
static inline int scene_order_insert(Scene *sc, SceneObj *o, const SceneObj *prev) {
  if (!scene_order_reserve(sc, sc->norder + 1)) return 0;
  size_t at = 0;
  if (prev) {
    size_t i = 0;
    while (i < sc->norder && sc->order[i] != prev) i++;
    if (i == sc->norder) return 0;
    at = i + 1;
  }
  memmove(&sc->order[at + 1], &sc->order[at], (sc->norder - at) * sizeof *sc->order);
  sc->order[at] = o; sc->norder++;
  return 1;
}

/* ---------- groups ---------- */

static inline SceneGroup *scene_group(Scene *sc, const char *name, int make) {
  for (size_t i = 0; i < sc->ngroups; i++) if (!strcmp(sc->groups[i].name, name)) return &sc->groups[i];
  if (!make) return NULL;
  if (sc->ngroups == sc->capgroups) {
    size_t cap = sc->capgroups ? 2 * sc->capgroups : 8;
    SceneGroup *g = (SceneGroup *)realloc(sc->groups, cap * sizeof *g);
    if (!g) return NULL;
    sc->groups = g; sc->capgroups = cap;
  }
  SceneGroup *g = &sc->groups[sc->ngroups];
  g->name = scene_dup(name); g->ox = 0; g->oy = 0;
  if (!g->name) return NULL;
  sc->ngroups++;
  return g;
}

/* ---------- rows ---------- */

/* Split a row at its tabs, in place: at most `most` fields. */
static inline int scene_fields(char *line, char **f, int most) {
  int n = 0;
  f[n++] = line;
  for (char *c = line; *c && n < most; c++) if (*c == '\t') { *c = 0; f[n++] = c + 1; }
  return n;
}

static inline int scene_look_push(Scene *sc, const char *row) {
  if (sc->nlook == sc->caplook) {
    int cap = sc->caplook ? 2 * sc->caplook : 16;
    char **l = (char **)realloc(sc->look, (size_t)cap * sizeof *l);
    if (!l) return 0;
    sc->look = l; sc->caplook = cap;
  }
  return (sc->look[sc->nlook++] = scene_dup(row)) != NULL;
}

/* Take one patch row. Answers 0 when it is malformed or names an object it cannot find. */
static inline int scene_apply_row(Scene *sc, const char *row) {
  if (sc->open) {   /* inside an O … o block: a device row of the open object */
    if (!strcmp(row, "o")) { sc->open = NULL; return 1; }
    return scene_obj_push(sc->open, row);
  }
  char *copy = scene_dup(row);
  if (!copy) return 0;
  int most = 1;
  for (const char *c = row; *c; c++) if (*c == '\t') most++;
  char **f = (char **)malloc((size_t)most * sizeof *f);
  if (!f) { free(copy); return 0; }
  int n = scene_fields(copy, f, most);
  int ok = 1;
  switch (f[0][0]) {
  case 'P':
    free(sc->target); sc->target = scene_dup(row);
    if (n >= 4) { long r = atol(f[3]) / 1000; sc->ratio = r > 0 ? r : 1; } else ok = 0;
    break;
  case 'R': case 'Y': ok = scene_look_push(sc, row); break;
  case 'O': ok = n >= 4 && (sc->open = scene_put(sc, f[1], atol(f[2]), atol(f[3]))) != NULL; break;
  case 'M': {
    SceneObj *o = n >= 4 ? scene_find(sc, f[1]) : NULL;
    if (o) { o->ax += atol(f[2]); o->ay += atol(f[3]); } else ok = 0;
    break;
  }
  case 'X': {
    SceneObj *o = n >= 2 ? scene_find(sc, f[1]) : NULL;
    if (!o) { ok = 0; break; }
    scene_order_remove(sc, o);
    SceneObj **p = &sc->table[scene_hash(o->id) % sc->buckets];
    while (*p != o) p = &(*p)->next;
    *p = o->next; sc->count--;
    scene_obj_free(o);
    break;
  }
  case 'G': {
    SceneGroup *g = n >= 4 ? scene_group(sc, f[1], 1) : NULL;
    if (g) { g->ox += atol(f[2]); g->oy += atol(f[3]); } else ok = 0;
    break;
  }
  case 'I': {
    SceneObj *o = n >= 2 ? scene_find(sc, f[1]) : NULL;
    SceneObj *prev = (n >= 3 && f[2][0]) ? scene_find(sc, f[2]) : NULL;
    ok = o && (n < 3 || !f[2][0] || prev) && scene_order_insert(sc, o, prev);
    break;
  }
  case 'Q':
    sc->norder = 0;
    if (!scene_order_reserve(sc, (size_t)n)) { ok = 0; break; }
    for (int i = 1; i < n && ok; i++) {
      SceneObj *o = scene_find(sc, f[i]);
      if (o) sc->order[sc->norder++] = o; else ok = 0;
    }
    break;
  case 'E': break;
  default: ok = 0;
  }
  free(f); free(copy);
  return ok;
}

/* Write a number list `s` (space separated) with every pair moved by (dx, dy). */
static inline void scene_write_points(FILE *out, char *s, long dx, long dy) {
  int i = 0;
  for (char *tok = strtok(s, " "); tok; tok = strtok(NULL, " "), i++)
    fprintf(out, "%s%ld", i ? " " : "", atol(tok) + (i % 2 ? dy : dx));
}

/* Write one device row moved by (dx, dy) logical pixels at the scene's ratio: `Dev.move`. */
static inline void scene_write_row(FILE *out, const char *row, long dx, long dy, long r) {
  char *copy = scene_dup(row);
  if (!copy) return;
  char *f[64]; int n = scene_fields(copy, f, 64);
  char k = f[0][0];
  for (int i = 0; i < n; i++) {
    if (i) fputc('\t', out);
    long v = 0; int moved = 1;
    if ((k == 'F' && i >= 3 && i <= 6) || (k == 'B' && i >= 3 && i <= 10) || (k == 'H' && i >= 2 && i <= 5))
      v = atol(f[i]) + r * ((k == 'H' ? i % 2 == 0 : i % 2 == 1) ? dx : dy);
    else if ((k == 'C' && (i == 1 || i == 2)) || (k == 'K' && (i == 1 || i == 2)))
      v = atol(f[i]) + 1000 * (i == 1 ? dx : dy);
    else if (k == 'T' && (i == 2 || i == 3))
      v = atol(f[i]) + 1000 * (i == 2 ? dx : dy);
    else if (k == 'S' && i >= 3 && i < n - 1) { scene_write_points(out, f[i], 1000 * r * dx, 1000 * r * dy); continue; }
    else moved = 0;
    if (moved) fprintf(out, "%ld", v); else fputs(f[i], out);
  }
  fputc('\n', out);
  free(copy);
}

/* **The stream of the scene**: the target, the look, then each object's rows in order, each moved
 * by its group's origin and its anchor. */
static inline void scene_flatten(const Scene *sc, FILE *out) {
  if (sc->target) fprintf(out, "%s\n", sc->target);
  for (int i = 0; i < sc->nlook; i++) fprintf(out, "%s\n", sc->look[i]);
  for (size_t i = 0; i < sc->norder; i++) {
    const SceneObj *o = sc->order[i];
    long gx = 0, gy = 0;
    for (size_t g = 0; g < sc->ngroups; g++)
      if (!strcmp(sc->groups[g].name, o->group)) { gx = sc->groups[g].ox; gy = sc->groups[g].oy; break; }
    for (int j = 0; j < o->nrows; j++) scene_write_row(out, o->rows[j], gx + o->ax, gy + o->ay, sc->ratio);
  }
}

static inline void scene_free(Scene *sc) {
  for (size_t b = 0; b < sc->buckets; b++)
    for (SceneObj *o = sc->table[b], *nx; o; o = nx) { nx = o->next; scene_obj_free(o); }
  free(sc->table); free(sc->order);
  for (size_t g = 0; g < sc->ngroups; g++) free(sc->groups[g].name);
  free(sc->groups); free(sc->target);
  for (int i = 0; i < sc->nlook; i++) free(sc->look[i]);
  free(sc->look);
  memset(sc, 0, sizeof *sc);
}

#endif
