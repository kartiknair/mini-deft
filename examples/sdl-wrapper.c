#include <SDL.h>
#include <inttypes.h>
#include <stdlib.h>

typedef struct {
  char* buffer;
  uint64_t length;
  uint64_t capacity;
} str;

static char* to_null_terminated(const str* string) {
  char* nulled = malloc(string->length + 1);
  for (uint64_t i = 0; i < string->length; i++) {
    nulled[i] = string->buffer[i];
  }
  nulled[string->length] = '\0';
  return nulled;
}

typedef struct {
  uint64_t width;
  uint64_t height;
  void* _sdl_window;
  void* _sdl_renderer;
} Window;

typedef struct {
  uint8_t r;
  uint8_t g;
  uint8_t b;
  uint8_t a;
} Color;

typedef struct {
  uint64_t type;
  void* _sdl_event;
} Event;

int32_t sdl_init_everything_c() { return SDL_Init(SDL_INIT_EVERYTHING); }

Window sdl_wrapped_window_c(str* title, uint64_t* width, uint64_t* height) {
  SDL_Window* sdl_window =
      SDL_CreateWindow(to_null_terminated(title), SDL_WINDOWPOS_CENTERED,
                       SDL_WINDOWPOS_CENTERED, *width, *height, 0);

  SDL_Renderer* sdl_renderer =
      SDL_CreateRenderer(sdl_window, -1, SDL_RENDERER_ACCELERATED);

  Window window = {
      .width = *width,
      .height = *height,
      ._sdl_window = sdl_window,
      ._sdl_renderer = sdl_renderer,
  };

  return window;
}

void sdl_destroy_window_c(Window* window) {
  SDL_DestroyWindow((SDL_Window*)window->_sdl_window);
  SDL_Quit();
}

void sdl_window_clear_c(Window* window) {
  SDL_RenderClear((SDL_Renderer*)window->_sdl_renderer);
}

void sdl_window_set_color_c(Window* window, Color* color) {
  SDL_SetRenderDrawColor((SDL_Renderer*)window->_sdl_renderer, color->r,
                         color->g, color->b, color->a);
}

void sdl_window_draw_point_c(Window* window, uint64_t* x, uint64_t* y) {
  SDL_RenderDrawPoint((SDL_Renderer*)window->_sdl_renderer, *x, *y);
}

void sdl_window_draw_rect_c(Window* window, uint64_t* x, uint64_t* y,
                            uint64_t* width, uint64_t* height) {
  SDL_Rect r;
  r.x = *x;
  r.y = *y;
  r.w = *width;
  r.h = *height;

  SDL_RenderFillRect((SDL_Renderer*)window->_sdl_renderer, &r);
}

void sdl_window_present_c(Window* window) {
  SDL_RenderPresent((SDL_Renderer*)window->_sdl_renderer);
}

void sdl_blank_event_c(Event* sret) {
  sret->type = 0;
  sret->_sdl_event = NULL;
}

int32_t sdl_poll_event_c(Event* event) {
  SDL_Event sdl_event;
  int32_t result = SDL_PollEvent(&sdl_event);
  if (result) {
    if (event->_sdl_event == NULL) {
      event->_sdl_event = malloc(sizeof(SDL_Event));
    }

    *((SDL_Event*)event->_sdl_event) = sdl_event;
    event->type = ((SDL_Event*)(event->_sdl_event))->type;
  }
  return result;
}

void sdl_destroy_event_c(Event* event) {
  if (event->_sdl_event != NULL) {
    free(event->_sdl_event);
  }
}
