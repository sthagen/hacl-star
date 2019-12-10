/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /opt/kremlin/krml -verbose -verbose -I /opt/hacl-star/code/old/lib/kremlin -I /opt/kremlin/kremlib/compat -I /opt/hacl-star/specs -I /opt/hacl-star/specs/old -I . -fparentheses -fcurly-braces -fno-shadow -ccopt -march=native -verbose -ldopt -flto -bundle Crypto.Symmetric.AES+Crypto.Symmetric.AES128=*[rename=Hacl_AES] -tmpdir aesgcm-c -minimal -add-include "kremlib.h" -skip-compilation aesgcm-c/out.krml
  F* version: 5ec54b2f
  KreMLin version: 44acff92
 */
#include "kremlib.h"

#ifndef __Hacl_AES_H
#define __Hacl_AES_H




typedef uint8_t *Crypto_Symmetric_AES_bytes;

typedef uint8_t *Crypto_Symmetric_AES_block;

typedef uint8_t *Crypto_Symmetric_AES_skey;

typedef uint8_t *Crypto_Symmetric_AES_xkey;

typedef uint32_t Crypto_Symmetric_AES_rnd;

typedef uint32_t Crypto_Symmetric_AES_idx_16;

typedef uint8_t *Crypto_Symmetric_AES_sbox;

void Crypto_Symmetric_AES_mk_sbox(uint8_t *sbox);

void Crypto_Symmetric_AES_mk_inv_sbox(uint8_t *sbox);

void Crypto_Symmetric_AES_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox);

void Crypto_Symmetric_AES_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox);

void Crypto_Symmetric_AES_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox);

typedef uint8_t *Crypto_Symmetric_AES128_bytes;

typedef uint8_t *Crypto_Symmetric_AES128_block;

typedef uint8_t *Crypto_Symmetric_AES128_skey;

typedef uint8_t *Crypto_Symmetric_AES128_xkey;

typedef uint32_t Crypto_Symmetric_AES128_rnd;

typedef uint32_t Crypto_Symmetric_AES128_idx_16;

typedef uint8_t *Crypto_Symmetric_AES128_sbox;

void Crypto_Symmetric_AES128_mk_sbox(uint8_t *sbox);

void Crypto_Symmetric_AES128_mk_inv_sbox(uint8_t *sbox);

void Crypto_Symmetric_AES128_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox);

void Crypto_Symmetric_AES128_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox);

void
Crypto_Symmetric_AES128_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox);

#define __Hacl_AES_H_DEFINED
#endif
