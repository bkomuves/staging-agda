
//
// parsing and pretty-printing big integers
// 
// Note: the inputs are assumed to be valid and the result fitting in the given bigint
//

#include <assert.h>
#include <stdint.h>

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

//------------------------------------------------------------------------------
// *** helper functions (some bigint arithmetic)

int bigint_is_zero(int nlimbs, const uint64_t *src) {
  int ok = 1;
  for(int i=0; i<nlimbs; i++) {
    if (src[i] != 0) { 
      ok = 0; 
      break; 
    }
  }
  return ok;
}

void shift_limbs_left(int nlimbs, uint64_t *limbs, int k) {
  assert( (k > 0) && (k < 64) );
  uint64_t carry = 0;
  for(int i=0; i<nlimbs; i++) {
    uint64_t x = limbs[i];
    limbs[i] = (x << k) | carry;
    carry = x >> (64-k);
  }
}

void bigint_add_small(int nlimbs, uint64_t *tgt, uint64_t small) {
  uint64_t carry = small;
  for(int i=0; i<nlimbs; i++) {
    uint64_t x = tgt[i];
    uint64_t y = x + carry;
    tgt[i] = y;
    carry  = (y < x) ? 1 : 0;
  }
}

void bigint_mul_small(int nlimbs, uint64_t *tgt, uint64_t small) {
  uint64_t carry = 0;
  for(int i=0; i<nlimbs; i++) {
    __uint128_t z = ((__uint128_t)tgt[i]) * small + carry;
    uint64_t lo = (uint64_t)(z      );
    uint64_t hi = (uint64_t)(z >> 64);
    tgt[i] = lo;
    carry  = hi;
  }
}

uint64_t bigint_divmod_small(int nlimbs, uint64_t *tgt, uint64_t small) {
  uint64_t carry = 0;
  for(int i=0; i<nlimbs; i++) {
    __uint128_t x = ((__uint128_t)carry) << 64;
    x += tgt[nlimbs-1-i];
    tgt[nlimbs-1-i] = (uint64_t)(x / small);
    carry = (uint64_t)(x % small);
  }
  return carry;
}

//------------------------------------------------------------------------------
// *** parsing from strings

uint64_t from_hex_digit(char c) {
  if ( (c >= '0') && (c <= '9') ) return (uint64_t)(c - '0'     );
  if ( (c >= 'A') && (c <= 'F') ) return (uint64_t)(c - 'A' + 10);
  if ( (c >= 'a') && (c <= 'f') ) return (uint64_t)(c - 'a' + 10);
  return 0;
}

// parse a hexadecimal number (without the 0x prefix)
void parse_hex_into(const char *str, int nlimbs, uint64_t *tgt) {
  for(int i=0; i<nlimbs; i++) tgt[i] = 0;
  const char *p = str;
  while( p[0] != 0 ) {
    shift_limbs_left( nlimbs , tgt , 4 );   // multiply by 16
    bigint_add_small( nlimbs , tgt , from_hex_digit( p[0] ) );
    p++;
  }
}

// parse a decimal number
void parse_dec_into(const char *str, int nlimbs, uint64_t *tgt) {
  for(int i=0; i<nlimbs; i++) tgt[i] = 0;
  const char *p = str;
  while( p[0] != 0 ) {
    bigint_mul_small( nlimbs , tgt , 10 );   // multiply by 10
    bigint_add_small( nlimbs , tgt , from_hex_digit( p[0] ) );
    p++;
  }
}

// "recognizes" hex and decimal strings
void parse_bigint_into(const char *str, int nlimbs, uint64_t *tgt) {
  if ( (str[0] == '0') && ((str[1] == 'x') || (str[1] == 'X')) ) {
    return parse_hex_into( str+2 , nlimbs , tgt );
  }
  else {
    return parse_dec_into( str , nlimbs , tgt );
  }
}

//------------------------------------------------------------------------------
// *** decimal printing

void fprint_dec(FILE *h, int nlimbs, const uint64_t *src) {
  char     *buf = (char*)     alloca(20*nlimbs+1);    // 64 bit always fits into 20 decimal digits 
  uint64_t *big = (uint64_t*) alloca(8*nlimbs);
  memcpy( big , src , 8*nlimbs );

  char *p = buf;
  do {
    uint64_t r = bigint_divmod_small( nlimbs , big , 10 );
    p[0] = (char)(r + '0');
    p++;
  }
  while( !bigint_is_zero(nlimbs,big) );

  while(p > buf) {
    p--;
    fprintf( h, "%c", p[0] );
  }
}

void fprintln_dec(FILE *h, int nlimbs, const uint64_t *src) {
  fprint_dec(h, nlimbs, src);
  printf("\n");
}

void fshow_dec(FILE *h, const char *name, int nlimbs, const uint64_t *src) {
  printf("%s = ",name);
  fprintln_dec(h, nlimbs, src);
}

//------------------------------------------------------------------------------
// *** hexadecimal printing

void fprint_hex_uint64(FILE *h, uint64_t x) {
  for(int i=0; i<16; i++) {
    uint64_t y = (x >> (4*(15-i))) & 0x0f;
    if (y < 10) {
      fprintf(h, "%c", (char)(y + '0') );
    }
    else {      
      fprintf(h, "%c", (char)(y - 10 + 'a') );
    }
  }
}

void fprint_hex(FILE *h, int nlimbs, const uint64_t *src) {
  printf("0x");
  for(int i=0; i<nlimbs; i++) fprint_hex_uint64(h, src[nlimbs-1-i]); 
}

void fprintln_hex(FILE *h, int nlimbs, const uint64_t *src) {
  fprint_hex(h, nlimbs, src);
  printf("\n");
}

void fshow_hex(FILE *h, const char *name, int nlimbs, const uint64_t *src) {
  printf("%s = ",name);
  fprintln_hex(h, nlimbs, src);
}

//------------------------------------------------------------------------------

int main() {
  char dec0[] = "0";
  char dec1[] = "1234567890123456789012345";
  char dec2[] = "99307946937885056825021746409023806484733317497466653116008043155211777145516";
  char dec3[] = "33164041917095738370361137924700515030372624327030028450727055558255225003533";
  char hex1[] = "0xb280a763307eb64821cdcda8280ec0bd502c95bdad0f128ea6320788ae7d3458";
  char hex2[] = "0x75bd332e239f36744e879d3a9e85c11d4c44f50e7382f7720fc4e0b8eca992f9";

  uint64_t big[4];

  parse_bigint_into(dec0,4,big); fshow_dec(stdout, "dec0", 4, big);
  parse_bigint_into(dec1,4,big); fshow_dec(stdout, "dec1", 4, big);
  parse_bigint_into(dec2,4,big); fshow_dec(stdout, "dec2", 4, big);
  parse_bigint_into(dec3,4,big); fshow_dec(stdout, "dec3", 4, big);
  parse_bigint_into(hex1,4,big); fshow_hex(stdout, "hex1", 4, big);
  parse_bigint_into(hex2,4,big); fshow_hex(stdout, "hex2", 4, big);
}

