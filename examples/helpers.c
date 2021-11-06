#include <stdint.h>
#include <stdio.h>

void print_u8(uint8_t n) { printf("%u\n", n); }
void print_u16(uint16_t n) { printf("%u\n", n); }
void print_u32(uint32_t n) { printf("%u\n", n); }
void print_u64(uint64_t n) { printf("%lu\n", n); }

void print_i8(int8_t n) { printf("%d\n", n); }
void print_i16(int16_t n) { printf("%d\n", n); }
void print_i32(int32_t n) { printf("%d\n", n); }
void print_i64(int64_t n) { printf("%ld\n", n); }

void print_f32(float n) { printf("%g\n", n); }
void print_f64(double n) { printf("%g\n", n); }
