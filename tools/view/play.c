/* play.c: a window that shows a folder of frames and plays the motion between them (tools/view;
 * docs/research/2026-10-09-visual-pipeline.md, slices V1 and V3).
 *
 *   play DIR    the pictures of DIR in name order: `NNN.draw` is a frame, `NNN-TTT.draw` a
 *               picture of the motion that leads to frame NNN (tools/Drivers/View.lean writes both)
 *   play DIR --shot N FILE   draw the Nth picture through the window's renderer, read its pixels
 *               back and save them as BMP: the check of this path with no screen
 *
 * The window is SDL3's (vendor/SDL3-3.4.16, built static by its build.sh into tools/view/sdl3).
 *
 * Keys: Right or Space plays the motion to the next frame; Left steps back to the frame before,
 * with no motion; Home and End go to the first and the last frame; Q or Escape quits.
 *
 * It decides nothing: each picture is a stream that Lean wrote, replayed by replay.h. The motion
 * is Lean's too: each picture between two frames is a moment of the step (`Tools.View.sample`).
 */
#define _GNU_SOURCE
#include <SDL3/SDL.h>
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

/* Replay picture `i` and draw it, at one logical pixel for one point; present it unless only a
 * reading of the pixels follows. */
static void draw(Screen *s, int i, int present);
static void show(Screen *s, int i) { draw(s, i, 1); }

static void draw(Screen *s, int i, int present) {
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
  SDL_GetCurrentRenderOutputSize(s->renderer, &outW, &outH);
  const double scale = (double)outW / (double)winW;   /* device pixels of the screen for one point */
  SDL_SetRenderScale(s->renderer, 1.0f, 1.0f);
  SDL_FRect dst = {0.0f, 0.0f, (float)((double)w * scale / ratio), (float)((double)h * scale / ratio)};
  SDL_SetRenderDrawColor(s->renderer, 0x14, 0x11, 0x0d, 0xff);   /* the ground of PAINT_DARK */
  SDL_RenderClear(s->renderer);
  SDL_RenderTexture(s->renderer, texture, NULL, &dst);
  if (present) SDL_RenderPresent(s->renderer);
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
  const int shot = argc == 5 && !strcmp(argv[2], "--shot");
  if (argc != 2 && !shot) { fprintf(stderr, "usage: play DIR [--shot N FILE]\n"); return 2; }
  if (!load(argv[1])) { fprintf(stderr, "play: no .draw file in %s\n", argv[1]); return 1; }
  double W = 0, H = 0, most = 0, ratio = 1;
  for (int i = 0; i < count; i++) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", argv[1], names[i]);
    if (replay_target(path, &W, &H, &ratio) && H > most) most = H;
  }
  PaintFaces faces;
  if (!paint_faces_open(&faces)) { fprintf(stderr, "play: a face does not open\n"); return 1; }
  if (!SDL_Init(SDL_INIT_VIDEO)) { fprintf(stderr, "play: %s\n", SDL_GetError()); return 1; }
  Screen s = {0};
  s.faces = &faces;
  s.dir = argv[1];
  s.window = SDL_CreateWindow("play", (int)W, (int)most, SDL_WINDOW_HIGH_PIXEL_DENSITY | SDL_WINDOW_RESIZABLE);
  s.renderer = s.window ? SDL_CreateRenderer(s.window, NULL) : NULL;
  if (s.window && !s.renderer) s.renderer = SDL_CreateRenderer(s.window, SDL_SOFTWARE_RENDERER);
  if (s.renderer) SDL_SetRenderVSync(s.renderer, 1);
  if (!s.renderer) { fprintf(stderr, "play: %s\n", SDL_GetError()); return 1; }
  int first = 0;
  while (first < count - 1 && !is_frame(first)) first++;
  if (shot) {
    const int n = atoi(argv[3]);
    if (n < 0 || n >= count) { fprintf(stderr, "play: no picture %d of %d\n", n, count); return 1; }
    draw(&s, n, 0);
    SDL_Surface *pixels = SDL_RenderReadPixels(s.renderer, NULL);
    const int saved = pixels && SDL_SaveBMP(pixels, argv[4]);
    if (pixels) SDL_DestroySurface(pixels);
    SDL_DestroyRenderer(s.renderer);
    SDL_DestroyWindow(s.window);
    SDL_Quit();
    paint_faces_close(&faces);
    printf("%s: %s\n", names[n], saved ? argv[4] : SDL_GetError());
    for (int i = 0; i < count; i++) free(names[i]);
    return saved ? 0 : 1;
  }
  show(&s, first);
  for (SDL_Event e; SDL_WaitEvent(&e);) {
    if (e.type == SDL_EVENT_QUIT) break;
    if (e.type == SDL_EVENT_WINDOW_EXPOSED || e.type == SDL_EVENT_WINDOW_PIXEL_SIZE_CHANGED) show(&s, s.shown);
    if (e.type != SDL_EVENT_KEY_DOWN) continue;
    const SDL_Keycode key = e.key.key;
    if (key == SDLK_Q || key == SDLK_ESCAPE) break;
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
