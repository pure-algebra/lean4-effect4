/* play.c: a window that shows a folder of frames and plays the motion between them (tools/view;
 * docs/research/2026-10-09-visual-pipeline.md, slices V1 and V3).
 *
 *   play DIR    the pictures of DIR in name order: `NNN.draw` is a frame, `NNN-TTT.draw` a
 *               picture of the motion that leads to frame NNN (tools/Drivers/View.lean writes both)
 *
 * Keys: Right or Space plays the motion to the next frame; Left steps back to the frame before,
 * with no motion; Home and End go to the first and the last frame; Q or Escape quits.
 *
 * It decides nothing: each picture is a stream that Lean wrote, replayed by replay.h. The motion
 * is Lean's too: each picture between two frames is a moment of the step (`Tools.View.sample`).
 */
#define _GNU_SOURCE
#include <SDL.h>
#include <dirent.h>

#include "replay.h"

#define MOST 4096
#define STEP_MS 16   /* the time each picture of a motion stays on the screen: 60 a second */

static char *names[MOST];
static int count;

static int by_name(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

/* A frame, as against a picture of motion: its name has no `-`. */
static int is_frame(int i) { return strchr(names[i], '-') == NULL; }

/* The `.draw` files of `dir`, in name order. Answers their count. */
static int load(const char *dir) {
  DIR *d = opendir(dir);
  if (!d) { perror(dir); return 0; }
  struct dirent *e;
  while ((e = readdir(d)) && count < MOST) {
    size_t n = strlen(e->d_name);
    if (n > 5 && !strcmp(e->d_name + n - 5, ".draw")) names[count++] = strdup(e->d_name);
  }
  closedir(d);
  qsort(names, (size_t)count, sizeof *names, by_name);
  return count;
}

typedef struct Screen {
  SDL_Window *window;
  SDL_Renderer *renderer;
  const PaintFaces *faces;
  const char *dir;
  int shown;   /* the index of the picture on the screen */
} Screen;

/* Replay picture `i` and put it on the screen, at one logical pixel for one point. */
static void show(Screen *s, int i) {
  char path[4096];
  snprintf(path, sizeof path, "%s/%s", s->dir, names[i]);
  double W = 0, H = 0, ratio = 1;
  if (!replay_target(path, &W, &H, &ratio)) return;
  int bad = 0;
  cairo_surface_t *surface = replay_stream(path, s->faces, &bad);
  if (!surface) return;
  cairo_surface_flush(surface);
  int w = cairo_image_surface_get_width(surface), h = cairo_image_surface_get_height(surface);
  SDL_Texture *texture = SDL_CreateTexture(s->renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, w, h);
  SDL_UpdateTexture(texture, NULL, cairo_image_surface_get_data(surface), cairo_image_surface_get_stride(surface));
  int winW = 1, winH = 1, outW = 1, outH = 1;
  SDL_GetWindowSize(s->window, &winW, &winH);
  SDL_GetRendererOutputSize(s->renderer, &outW, &outH);
  const double scale = (double)outW / (double)winW;   /* device pixels of the screen for one point */
  SDL_Rect dst = {0, 0, (int)((double)w * scale / ratio), (int)((double)h * scale / ratio)};
  SDL_SetRenderDrawColor(s->renderer, 0x14, 0x11, 0x0d, 0xff);   /* the ground of PAINT_DARK */
  SDL_RenderClear(s->renderer);
  SDL_RenderCopy(s->renderer, texture, NULL, &dst);
  SDL_RenderPresent(s->renderer);
  SDL_DestroyTexture(texture);
  cairo_surface_destroy(surface);
  char title[512];
  snprintf(title, sizeof title, "%s / %s%s", s->dir, names[i], bad ? "  (rows that are no call)" : "");
  SDL_SetWindowTitle(s->window, title);
  s->shown = i;
}

/* Play every picture from the one shown to picture `to`, one after another. */
static void play_to(Screen *s, int to) {
  for (int i = s->shown + 1; i <= to; i++) {
    show(s, i);
    if (i < to) SDL_Delay(STEP_MS);
  }
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: play DIR\n"); return 2; }
  if (!load(argv[1])) { fprintf(stderr, "play: no .draw file in %s\n", argv[1]); return 1; }
  double W = 0, H = 0, most = 0, ratio = 1;
  for (int i = 0; i < count; i++) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", argv[1], names[i]);
    if (replay_target(path, &W, &H, &ratio) && H > most) most = H;
  }
  PaintFaces faces;
  if (!paint_faces_open(&faces)) { fprintf(stderr, "play: a face does not open\n"); return 1; }
  if (SDL_Init(SDL_INIT_VIDEO) != 0) { fprintf(stderr, "play: %s\n", SDL_GetError()); return 1; }
  Screen s = {0};
  s.faces = &faces;
  s.dir = argv[1];
  s.window = SDL_CreateWindow("play", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, (int)W, (int)most,
                              SDL_WINDOW_ALLOW_HIGHDPI | SDL_WINDOW_RESIZABLE);
  s.renderer = s.window ? SDL_CreateRenderer(s.window, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC) : NULL;
  if (s.window && !s.renderer) s.renderer = SDL_CreateRenderer(s.window, -1, SDL_RENDERER_SOFTWARE);
  if (!s.renderer) { fprintf(stderr, "play: %s\n", SDL_GetError()); return 1; }
  int first = 0;
  while (first < count - 1 && !is_frame(first)) first++;
  show(&s, first);
  for (SDL_Event e; SDL_WaitEvent(&e);) {
    if (e.type == SDL_QUIT) break;
    if (e.type == SDL_WINDOWEVENT && e.window.event == SDL_WINDOWEVENT_EXPOSED) show(&s, s.shown);
    if (e.type != SDL_KEYDOWN) continue;
    const SDL_Keycode key = e.key.keysym.sym;
    if (key == SDLK_q || key == SDLK_ESCAPE) break;
    if (key == SDLK_RIGHT || key == SDLK_SPACE) {
      int next = s.shown + 1;
      while (next < count && !is_frame(next)) next++;
      if (next < count) play_to(&s, next);
    } else if (key == SDLK_LEFT) {
      int back = s.shown - 1;
      while (back > 0 && !is_frame(back)) back--;
      if (back >= 0) show(&s, back);
    } else if (key == SDLK_HOME) {
      show(&s, first);
    } else if (key == SDLK_END) {
      int last = count - 1;
      while (last > 0 && !is_frame(last)) last--;
      show(&s, last);
    }
  }
  SDL_DestroyRenderer(s.renderer);
  SDL_DestroyWindow(s.window);
  SDL_Quit();
  paint_faces_close(&faces);
  for (int i = 0; i < count; i++) free(names[i]);
  return 0;
}
