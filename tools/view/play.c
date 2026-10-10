/* play.c: a window that shows a folder of frames and plays the motion between them (tools/view;
 * docs/research/2026-10-09-visual-pipeline.md, slices V1 and V3), or a live session's patches.
 *
 *   play DIR    the pictures of DIR in name order: `NNN.draw` is a frame, `NNN-TTT.draw` a
 *               picture of the motion that leads to frame NNN (tools/Drivers/View.lean writes both)
 *   play DIR --shot N FILE   draw the Nth picture through the window's renderer, read its pixels
 *               back and save them as BMP: the check of this path with no screen
 *   play --live the patch rows of a live session on standard input (tools/Drivers/Live.lean): each
 *               row is applied to a retained store (scene.h), and each patch's end paints the
 *               store's stream, read from memory (replay_memory). The window holds the last frame
 *               when the input ends. A move is shown at its end; the motion of a move is not drawn.
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
#include "scene.h"

#define MOST 4096
#define STEP_MS 16   /* a picture's time on the screen when a stream names no step: 60 a second */

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
  Replay *replay;   /* the look's colours and faces, kept from one picture to the next */
  const char *dir;
  int shown;   /* the index of the picture on the screen */
} Screen;

/* Replay picture `i` and draw it, at one logical pixel for one point; present it unless only a
 * reading of the pixels follows. */
static void draw(Screen *s, int i, int present);
static void show(Screen *s, int i) { draw(s, i, 1); }

/* Show a painted picture of `ratio` device pixels a logical pixel, at one logical pixel for one
 * point, or smaller to fit the window; present it unless only a reading of the pixels follows. */
static void show_surface(Screen *s, cairo_surface_t *surface, double ratio, int present) {
  cairo_surface_flush(surface);
  int w = cairo_image_surface_get_width(surface), h = cairo_image_surface_get_height(surface);
  SDL_Texture *texture = SDL_CreateTexture(s->renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, w, h);
  SDL_UpdateTexture(texture, NULL, cairo_image_surface_get_data(surface), cairo_image_surface_get_stride(surface));
  int winW = 1, winH = 1, outW = 1, outH = 1;
  SDL_GetWindowSize(s->window, &winW, &winH);
  SDL_GetCurrentRenderOutputSize(s->renderer, &outW, &outH);
  const double scale = (double)outW / (double)winW;   /* device pixels of the screen for one point */
  SDL_SetRenderScale(s->renderer, 1.0f, 1.0f);
  /* The picture at its size, or smaller to fit the window: one factor for both sides, never larger. */
  const double natW = (double)w * scale / ratio, natH = (double)h * scale / ratio;
  double fit = 1.0;
  if (natW > (double)outW) fit = (double)outW / natW;
  if (natH * fit > (double)outH) fit = (double)outH / natH;
  SDL_SetTextureScaleMode(texture, SDL_SCALEMODE_LINEAR);
  SDL_FRect dst = {0.0f, 0.0f, (float)(natW * fit), (float)(natH * fit)};
  const uint32_t ground = s->replay->tokens.ground;   /* the look's ground, from the stream */
  SDL_SetRenderDrawColor(s->renderer, (Uint8)(ground >> 16), (Uint8)(ground >> 8), (Uint8)ground, 0xff);
  SDL_RenderClear(s->renderer);
  SDL_RenderTexture(s->renderer, texture, NULL, &dst);
  if (present) SDL_RenderPresent(s->renderer);
  SDL_DestroyTexture(texture);
}

static void draw(Screen *s, int i, int present) {
  char path[4096];
  snprintf(path, sizeof path, "%s/%s", s->dir, names[i]);
  double W = 0, H = 0, ratio = 1;
  if (!replay_target(path, &W, &H, &ratio)) return;
  int bad = 0;
  cairo_surface_t *surface = replay_stream(path, s->replay, &bad);
  if (!surface) return;
  show_surface(s, surface, ratio, present);
  cairo_surface_destroy(surface);
  char title[512];
  snprintf(title, sizeof title, "%s / %s%s", s->dir, names[i], bad ? "  (rows that are no call)" : "");
  SDL_SetWindowTitle(s->window, title);
  s->shown = i;
}

/* Play every picture from the one shown to picture `to`, one after another, in the look's time:
 * picture k of n stands at k/n of the step's milliseconds from the start, or STEP_MS after the
 * one before when the stream names no step. A picture that takes longer to draw is not skipped. */
static void play_to(Screen *s, int to) {
  const int n = to - s->shown;
  const Uint64 start = SDL_GetTicks();
  for (int i = s->shown + 1, k = 1; i <= to; i++, k++) {
    show(s, i);
    if (i == to) break;
    const double step = s->replay->step;
    const Uint64 due = step > 0 ? start + (Uint64)(step * k / n) : SDL_GetTicks() + STEP_MS;
    const Uint64 now = SDL_GetTicks();
    if (due > now) SDL_Delay((Uint32)(due - now));
  }
}

/* Whether an event asks to quit: the window's close, Q or Escape. */
static int quits(const SDL_Event *e) {
  if (e->type == SDL_EVENT_QUIT) return 1;
  return e->type == SDL_EVENT_KEY_DOWN && (e->key.key == SDLK_Q || e->key.key == SDLK_ESCAPE);
}

/* The live mode: apply each patch row of standard input to a retained store, and paint the store's
 * stream at each patch's end. Answers 0 when every row applied. */
static int live(void) {
  Scene sc;
  if (!scene_init(&sc)) { fprintf(stderr, "play: no memory for the scene\n"); return 1; }
  Replay replay; memset(&replay, 0, sizeof replay);
  if (!SDL_Init(SDL_INIT_VIDEO)) { fprintf(stderr, "play: %s\n", SDL_GetError()); scene_free(&sc); return 1; }
  Screen s = {0};
  s.replay = &replay;
  s.dir = "live";
  int frames = 0, bad = 0, quit = 0;
  char *line = NULL; size_t cap = 0; ssize_t len;
  while (!quit && (len = getline(&line, &cap, stdin)) > 0) {
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
    if (!len) continue;
    if (!scene_apply_row(&sc, line)) { bad++; fprintf(stderr, "play: a row does not apply: %.80s\n", line); continue; }
    if (line[0] != 'E') continue;
    char *flat = NULL; size_t flen = 0;
    FILE *out = open_memstream(&flat, &flen);
    if (!out) break;
    scene_flatten(&sc, out);
    fclose(out);
    int rows = 0;
    cairo_surface_t *surface = replay_memory(flat, flen, &replay, &rows);
    free(flat);
    if (!surface) { bad++; continue; }
    const double ratio = (double)sc.ratio;
    if (!s.window) {
      const int w = cairo_image_surface_get_width(surface), h = cairo_image_surface_get_height(surface);
      s.window = SDL_CreateWindow("play --live", (int)(w / ratio), (int)(h / ratio),
                                  SDL_WINDOW_HIGH_PIXEL_DENSITY | SDL_WINDOW_RESIZABLE);
      s.renderer = s.window ? SDL_CreateRenderer(s.window, NULL) : NULL;
      if (s.window && !s.renderer) s.renderer = SDL_CreateRenderer(s.window, SDL_SOFTWARE_RENDERER);
      if (s.renderer) SDL_SetRenderVSync(s.renderer, 1);
      if (!s.renderer) { fprintf(stderr, "play: %s\n", SDL_GetError()); cairo_surface_destroy(surface); break; }
    }
    show_surface(&s, surface, ratio, 1);
    cairo_surface_destroy(surface);
    frames++;
    char title[128];
    snprintf(title, sizeof title, "play --live: frame %d%s", frames, rows ? "  (rows that are no call)" : "");
    SDL_SetWindowTitle(s.window, title);
    for (SDL_Event e; SDL_PollEvent(&e);) if (quits(&e)) quit = 1;
  }
  free(line);
  if (!quit && s.window)
    for (SDL_Event e; SDL_WaitEvent(&e);) if (quits(&e)) break;
  if (s.renderer) SDL_DestroyRenderer(s.renderer);
  if (s.window) SDL_DestroyWindow(s.window);
  SDL_Quit();
  replay_close(&replay);
  scene_free(&sc);
  fprintf(stderr, "play: %d frames live, %d rows that do not apply\n", frames, bad);
  return bad ? 1 : 0;
}

int main(int argc, char **argv) {
  if (argc == 2 && !strcmp(argv[1], "--live")) return live();
  const int shot = argc == 5 && !strcmp(argv[2], "--shot");
  if (argc != 2 && !shot) { fprintf(stderr, "usage: play DIR [--shot N FILE] | play --live\n"); return 2; }
  if (!load(argv[1])) { fprintf(stderr, "play: no .draw file in %s\n", argv[1]); return 1; }
  double W = 0, H = 0, most = 0, ratio = 1;
  for (int i = 0; i < count; i++) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", argv[1], names[i]);
    if (replay_target(path, &W, &H, &ratio) && H > most) most = H;
  }
  Replay replay; memset(&replay, 0, sizeof replay);
  if (!SDL_Init(SDL_INIT_VIDEO)) { fprintf(stderr, "play: %s\n", SDL_GetError()); return 1; }
  Screen s = {0};
  s.replay = &replay;
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
    replay_close(&replay);
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
  replay_close(&replay);
  for (int i = 0; i < count; i++) free(names[i]);
  return 0;
}
