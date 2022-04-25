#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

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

str read_file_c(const str* path) {
  char* null_termed_path = to_null_terminated(path);

  FILE* f = fopen(null_termed_path, "rb");
  fseek(f, 0, SEEK_END);
  long fsize = ftell(f);
  fseek(f, 0, SEEK_SET);

  char* buffer = malloc(fsize + 1);
  fread(buffer, fsize, 1, f);
  str result = {
      .buffer = buffer,
      .length = fsize,
      .capacity = fsize + 1,
  };

  free(null_termed_path);
  fclose(f);

  return result;
}

void write_file_c(const str* path, const str* contents) {
  char* null_termed_path = to_null_terminated(path);

  FILE* f = fopen(null_termed_path, "wb");
  fwrite(contents->buffer, 1, contents->length, f);

  free(null_termed_path);
  fclose(f);
}

uint64_t timestamp_c() { return (uint64_t)time(NULL); }

str timestamp_to_string_c(const uint64_t* timestamp) {
  struct tm* timeinfo = localtime((time_t[]){*timestamp});

  char* result_buffer = asctime(timeinfo);
  uint64_t result_len = strlen(result_buffer);

  str result = {
      .buffer = NULL,
      .length = result_len,
      .capacity = result_len,
  };

  result.buffer = malloc(sizeof(result_len));
  for (uint64_t i = 0; i < result_len - 1; i++) {
    result.buffer[i] = result_buffer[i];
  }

  return result;
}

str u64_to_string_c(const uint64_t* number) {
  uint64_t length = snprintf(NULL, 0, "%lu", *number);
  char* buffer = malloc(length + 1);
  snprintf(buffer, length + 1, "%lu", *number);
  return (str){.buffer = buffer, .length = length, .capacity = length};
}

str i64_to_string_c(const int64_t* number) {
  uint64_t length = snprintf(NULL, 0, "%ld", *number);
  char* buffer = malloc(length + 1);
  snprintf(buffer, length + 1, "%ld", *number);
  return (str){.buffer = buffer, .length = length, .capacity = length};
}

str f64_to_string_c(const double* number) {
  uint64_t length = snprintf(NULL, 0, "%.15g", *number);
  char* buffer = malloc(length + 1);
  snprintf(buffer, length + 1, "%.15g", *number);
  return (str){.buffer = buffer, .length = length, .capacity = length};
}

void print_c(const str* string) {
  for (uint64_t i = 0; i < string->length; i++) {
    putchar(string->buffer[i]);
  }
}

void println_c(const str* string) {
  for (uint64_t i = 0; i < string->length; i++) {
    putchar(string->buffer[i]);
  }
  putchar('\n');
}
