#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>

void print_u8(uint8_t* n) { printf("%u", *n); }
void print_u16(uint16_t* n) { printf("%u", *n); }
void print_u32(uint32_t* n) { printf("%u", *n); }
void print_u64(uint64_t* n) { printf("%lu", *n); }

void println_u8(uint8_t* n) { printf("%u\n", *n); }
void println_u16(uint16_t* n) { printf("%u\n", *n); }
void println_u32(uint32_t* n) { printf("%u\n", *n); }
void println_u64(uint64_t* n) { printf("%lu\n", *n); }

void print_i8(int8_t* n) { printf("%d", *n); }
void print_i16(int16_t* n) { printf("%d", *n); }
void print_i32(int32_t* n) { printf("%d", *n); }
void print_i64(int64_t* n) { printf("%ld", *n); }

void println_i8(int8_t* n) { printf("%d\n", *n); }
void println_i16(int16_t* n) { printf("%d\n", *n); }
void println_i32(int32_t* n) { printf("%d\n", *n); }
void println_i64(int64_t* n) { printf("%ld\n", *n); }

void print_f32(float* n) { printf("%g", *n); }
void print_f64(double* n) { printf("%g", *n); }

void println_f32(float* n) { printf("%g\n", *n); }
void println_f64(double* n) { printf("%g\n", *n); }

void print_char(uint8_t* byte) { printf("%c", *byte); }
void println_char(uint8_t* byte) { printf("%c\n", *byte); }

double pow_f64(double* base, double* power) { return pow(*base, *power); }
float pow_f32(float* base, float* power) { return powf(*base, *power); }

double sqrt_f64(double* n) { return sqrt(*n); }
float sqrt_f32(float* n) { return sqrtf(*n); }

uint64_t current_time() { return (uint64_t)time(NULL); }
